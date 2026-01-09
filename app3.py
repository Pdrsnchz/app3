from ib_insync import IB, Stock, util
import pandas as pd
import pytz
from datetime import datetime, time
import dash
from dash import html, dcc, dash_table
from dash.dependencies import Output, Input
import threading
import asyncio
import time as _time
import os
import pickle
import webbrowser
import math
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent

# ========== CONFIG ==========
TICKERS = UNIVERSE = [
    "AAPL","ABNB","ADBE","AMD","AMZN","APP","ARM","AVGO","BABA","BE","BIDU","BMNR","CAT",
    "CIEN","COST","CRM","CRS","CRSP","CSCO","CVS","DUOL","EBAY","ELF","ETSY","EXPE","FNMA",
    "FSLR","GLD","GOOGL","HD","HOOD","IBM","INTU","IONQ","JPM","LENZ","LULU","META","PDD",
    "MOS","MRNA","MRVL","MSFT","MSTR","MU","NKE","NFLX","NOW","NVDA","OKLO","OPEN","ORCL",
    "OSCR","OTIS","PANW","PCAR","PINS","PLTR","PTON","RBLX","RDDT","RGTI","RIOT","RMBS",
    "RKLB","RKT","RUN","SBAC","SBUX","SGBX","SNOW","SHOP","SOFI","SRPT","STX","STZ","TSLA",
    "TSM","TWLO","TXN","UPST","V","VRTX","WFC","WMT","Z","ZTS"
]

COMPARE_WITH = "SPY"
IB_HOST = "127.0.0.1"
IB_PORT = 7497
IB_CLIENT_ID = 42

N_DAYS = 5
MIN_PRIOR_DAYS_FOR_RVOL = 2   # allow computation with fewer prior days
RRS_LENGTH = 12
RVOL_THRESHOLD = 1.2
POLL_SECONDS = 60

TZ_NY = pytz.timezone("America/New_York")

# → FAVORITOS: lista/sets de tickers que quieres marcar manualmente
FAVORITES = {"AAPL","ABNB","AMD","AMZN","BE","GOOGL","META","MSFT","NFLX","NOW","NVDA","MU","ORCL","PLTR","RGTI","SOFI","TSLA"}


# timeframes: (barSizeSetting, durationStr)
TIMEFRAMES = {
    "1M": ("1 min", "1 D"),
    "5M": ("5 mins", "2 D"),
    "15M": ("15 mins", "3 D"),
}

TF_BASE_SECONDS = {
    "1M": 60,
    "5M": 300,
    "15M": 900
}

CACHE_DIR = BASE_DIR / "cache"
os.makedirs(CACHE_DIR, exist_ok=True)

# ========== LOGGING (auditoría) ==========
import csv

LOG_DIR = BASE_DIR / "logs"
LOG_DIR.mkdir(parents=True, exist_ok=True)
# =========================================
SPY_CACHE_TTL = 300

SPY_RVOL_DELAY_SEC = 6
SPY_RVOL_START_HOUR = 10  # primer cálculo válido (hora NY)

# path caché 1H SPY
SPY_1H_CACHE_PATH = CACHE_DIR / "SPY__1H.pkl"

# ========== SHARED STATE ==========
latest_results = {
    t: {tf: {"RRS": None, "corr": None, "bgcolor": "white"} for tf in TIMEFRAMES} | {"RVol": None}
    for t in TICKERS
}
state_lock = threading.Lock()

disk_cache = {}
spy_cache = {tf: {"df": None, "ts": None} for tf in TIMEFRAMES}

stage2 = set()

initial_update_done = False
updating = True
progress = {"processed": 0, "total": 0}
# progreso del recálculo de RVol (cada 15 min)
rvol_progress = {"processed": 0, "total": 0, "running": False, "last_update": None}
last_full_update = None

spy_rvol_state = {
    "Q": None,          # 60 días
    "M": None,          # 20 días
    "2W": None,         # 10 días
    "1W": None,         # 5 días
    "last_update": None,
    "last_hour": None,  # hora NY del último cálculo aplicado
    "last_date": None,  # fecha NY del último cálculo aplicado
    "last_ts": None     # timestamp NY de la última barra 1H usada para el cálculo
}

# ================= COUNTDOWN HELPERS =================
def seconds_until_tf_close(tf_key: str) -> int:
    now_utc = datetime.now(pytz.utc)
    now_ny = now_utc.astimezone(TZ_NY)
    minute = now_ny.minute
    second = now_ny.second

    base = TF_BASE_SECONDS.get(tf_key, 60)
    period_min = base // 60
    seconds_into = (minute % period_min) * 60 + second
    remaining = (base - 1) - seconds_into
    return max(0, int(remaining))

def seconds_until_rvol_refresh() -> int:
    now_utc = datetime.now(pytz.utc)
    now_ny = now_utc.astimezone(TZ_NY)
    minute = now_ny.minute
    second = now_ny.second

    # next multiple of 15
    next_q = ((minute // 15) + 1) * 15
    if next_q == 60:
        target_min = 0
    else:
        target_min = next_q

    curr_seconds = minute * 60 + second
    target_seconds = target_min * 60 + 6
    if next_q == 60:
        target_seconds = 60 * 60 + 6

    remaining = target_seconds - curr_seconds
    if remaining < 0:
        remaining += 3600
    return max(0, int(remaining))

def fmt_mmss(secs: int) -> str:
    return f"{secs // 60:02d}:{secs % 60:02d}"
    
# ========== HELPERS ==========
def floor_to_tf(dt: datetime, tf_seconds: int) -> datetime:
    """
    Devuelve dt floored al múltiplo de tf_seconds anterior (mantiene tz-aware).
    Ej: dt=10:00:06, tf_seconds=60 -> 10:00:00
    """
    if dt.tzinfo is None:
        raise ValueError("floor_to_tf expects timezone-aware datetime")
    ts = int(dt.timestamp())
    floored = ts - (ts % tf_seconds)
    return datetime.fromtimestamp(floored, tz=dt.tzinfo)
    
def drop_partial_bar_if_needed(df: pd.DataFrame, tf_seconds: int, end_dt: datetime | None = None) -> pd.DataFrame:
    """
    Elimina la última barra si está en formación (petición hecha a 'now').
    Si end_dt no es None, se asume que la petición ya iba anclada a una vela cerrada.
    """
    try:
        if df is None or df.empty:
            return df

        if end_dt is not None:
            return df

        if not isinstance(df.index, pd.DatetimeIndex):
            return df

        idx = pd.to_datetime(df.index)
        if idx.tz is None:
            idx = idx.tz_localize(TZ_NY)
        else:
            idx = idx.tz_convert(TZ_NY)
        df.index = idx

        now_ny = datetime.now(pytz.utc).astimezone(TZ_NY)
        floor_ts = floor_to_tf(now_ny, tf_seconds)

        return df[df.index < floor_ts]

    except Exception:
        return df

def cache_path(symbol: str, tf_key: str):
    return os.path.join(CACHE_DIR, f"{symbol}__{tf_key}.pkl")

def load_disk_cache(symbol: str, tf_key: str):
    path = cache_path(symbol, tf_key)
    if os.path.exists(path):
        try:
            with open(path, "rb") as f:
                df = pickle.load(f)
                # ensure index timezone normalized
                if isinstance(df, pd.DataFrame) and not df.empty:
                    if df.index.tz is None:
                        df.index = df.index.tz_localize(TZ_NY)
                    else:
                        df.index = df.index.tz_convert(TZ_NY)
                return df
        except Exception:
            return None
    return None

def save_disk_cache(symbol: str, tf_key: str, df: pd.DataFrame):
    path = cache_path(symbol, tf_key)
    try:
        df_to_save = df.copy()
        if isinstance(df_to_save, pd.DataFrame) and not df_to_save.empty:
            if df_to_save.index.tz is None:
                df_to_save.index = df_to_save.index.tz_localize(TZ_NY)
            else:
                df_to_save.index = df_to_save.index.tz_convert(TZ_NY)
        with open(path, "wb") as f:
            pickle.dump(df_to_save, f)
    except Exception:
        pass

def ensure_ny_index(series_or_index):
    s = pd.to_datetime(series_or_index)
    if s.dt.tz is None:
        return s.dt.tz_localize(TZ_NY)
    return s.dt.tz_convert(TZ_NY)

def map_corr_to_color(corr):
    if corr is None or pd.isna(corr):
        return "white"
    c = float(corr)
    if c > 0.75: return "#006400"
    if c > 0.50: return "#2e8b57"
    if c > 0.25: return "#66c266"
    if c > 0.00: return "#cfeccf"
    if c > -0.25: return "#f4cfcf"
    if c > -0.50: return "#f29b9b"
    if c > -0.75: return "#ff7b7b"
    return "#b20000"

# ==== SPY 1H cache helpers ====
def load_spy_1h_cache() -> pd.DataFrame:
    if not os.path.exists(SPY_1H_CACHE_PATH):
        return pd.DataFrame()
    try:
        with open(SPY_1H_CACHE_PATH, "rb") as f:
            df = pickle.load(f)
        if isinstance(df, pd.DataFrame) and not df.empty:
            if isinstance(df.index, pd.DatetimeIndex):
                if df.index.tz is None:
                    df.index = df.index.tz_localize(TZ_NY)
                else:
                    df.index = df.index.tz_convert(TZ_NY)
                df.index.name = "datetime"
        return df
    except Exception:
        return pd.DataFrame()

def save_spy_1h_cache(df: pd.DataFrame):
    """
    Guarda en disco el DataFrame pasado y actualiza spy_rvol_state['last_ts'] con
    la última timestamp conocida (tz-aware, NY).
    """
    try:
        if df is None:
            df2 = pd.DataFrame()
        else:
            df2 = df.copy()

        if isinstance(df2, pd.DataFrame) and not df2.empty:
            # normalizar índice a TZ_NY y fijar nombre
            if isinstance(df2.index, pd.DatetimeIndex):
                if df2.index.tz is None:
                    df2.index = df2.index.tz_localize(TZ_NY)
                else:
                    df2.index = df2.index.tz_convert(TZ_NY)
                df2.index.name = "datetime"
            # actualizar estado con la última barra conocida
            try:
                spy_rvol_state["last_ts"] = df2.index.max()
            except Exception:
                spy_rvol_state["last_ts"] = None
        else:
            # si df2 está vacío, limpiar last_ts
            spy_rvol_state["last_ts"] = None

        with open(SPY_1H_CACHE_PATH, "wb") as f:
            pickle.dump(df2, f)
    except Exception:
        # no elevar excepción en la escritura de caché para no romper el worker
        pass

def update_spy_1h_cache(loop, ib, spy_contract, end_dt: datetime | None = None):
    """
    Pide hasta 2H de barras 1H ending en end_dt (si se pasa) y guarda sólo la(s)
    barra(s) nuevas en el cache on-disk SPY__1H.pkl. Devuelve el dataframe completo cacheado.

    - end_dt: datetime aware en TZ_NY indicando el 'endDateTime' deseado (última vela cerrada).
              Si es None, se usa el comportamiento por defecto (now) — pero NUNCA deberías
              llamar sin pasar end_dt cuando quieras la última vela cerrada.
    """
    # preparar string endDateTime para la API de IB (formato YYYYMMDD HH:MM:SS, zona NY)
    if end_dt is not None:
        end_ny = end_dt.astimezone(TZ_NY)
        end_str = end_ny.strftime("%Y%m%d %H:%M:%S")
    else:
        end_str = ""  # fallback (preferible pasar end_dt siempre)

    try:
        bars = loop.run_until_complete(ib.reqHistoricalDataAsync(
            spy_contract, end_str, "2 H", "1 hour", "TRADES", useRTH=True, formatDate=1
        ))
    except Exception:
        bars = None

    if not bars:
        return load_spy_1h_cache()

    df_new = util.df(bars)
    if df_new.empty:
        return load_spy_1h_cache()

    # normalizar timestamp -> índice (NY TZ)
    if "date" in df_new.columns:
        df_new["date"] = pd.to_datetime(df_new["date"])
        if df_new["date"].dt.tz is None:
            df_new["date"] = df_new["date"].dt.tz_localize(TZ_NY)
        else:
            df_new["date"] = df_new["date"].dt.tz_convert(TZ_NY)
        df_new.set_index("date", inplace=True)
    elif isinstance(df_new.index, pd.DatetimeIndex):
        idx = pd.to_datetime(df_new.index)
        if idx.tz is None:
            idx = idx.tz_localize(TZ_NY)
        else:
            idx = idx.tz_convert(TZ_NY)
        df_new.index = idx
    else:
        return load_spy_1h_cache()

    df_new.index.name = "datetime"
    df_new = df_new[~df_new.index.duplicated(keep="last")].sort_index()

    # tomamos únicamente la última barra del bloque solicitado (la barra cerrada que pedimos)
    last_bar = df_new.iloc[[-1]]

    # cargar caché on-disk actual
    df_cache = load_spy_1h_cache()
    if df_cache is None or df_cache.empty:
        df_cache = last_bar
    else:
        # si la última barra del fetch ya está presente o es anterior o igual, evitamos añadirla
        try:
            last_cache_ts = df_cache.index.max()
            last_bar_ts = last_bar.index.max()
            if last_bar_ts <= last_cache_ts:
                # nada nuevo que añadir
                return df_cache
        except Exception:
            # en caso de cualquier error temporal, seguimos con concat/dedupe
            pass

        # concat y dedupe por índice: así construimos un histórico incremental persistente
        df_cache = pd.concat([df_cache, last_bar])
        df_cache = df_cache[~df_cache.index.duplicated(keep="last")].sort_index()

    save_spy_1h_cache(df_cache)
    return df_cache

# ========== HELPERS PARA AUDITORÍA RVol ==========
def log_rvol_to_csv(
    ticker: str,
    tag: str,
    bar_ts,
    current_value,
    historical_values,
    avg_value,
    rvol_value
):
    """
    Escritura robusta a CSV de los componentes usados para RVol.
    Convierte timestamps y valores a strings seguros para CSV.
    """
    try:
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        path = LOG_DIR / f"{ticker}_RVol.csv"
        write_header = not path.exists()

        # serializar bar_ts de forma segura
        if bar_ts is None:
            bar_ts_str = ""
        else:
            try:
                bar_ts_str = bar_ts.isoformat()
            except Exception:
                bar_ts_str = str(bar_ts)

        # normalizar numéricos (vacío si None)
        def n(x):
            try:
                return float(x) if x is not None else ""
            except Exception:
                return ""

        cur = n(current_value)
        avg = n(avg_value)
        rvolv = n(rvol_value)

        hist_str = ""
        if historical_values:
            try:
                hist_str = "|".join(map(lambda v: str(float(v)) if v is not None else "", historical_values))
            except Exception:
                try:
                    hist_str = "|".join(map(str, historical_values))
                except Exception:
                    hist_str = ""

        with open(path, "a", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            if write_header:
                writer.writerow([
                    "timestamp",
                    "tag",
                    "bar_ts",
                    "current_value",
                    "avg_value",
                    "rvol",
                    "historical_values"
                ])
            writer.writerow([
                datetime.now(TZ_NY).strftime("%Y-%m-%d %H:%M:%S"),
                tag,
                bar_ts_str,
                cur,
                avg,
                rvolv,
                hist_str
            ])
    except Exception:
        # nunca elevar para no romper el worker; mantenemos el comportamiento robusto
        pass

# ==============================================

def compute_rvol_from_last_complete_day(df_agg: pd.DataFrame):
    """
    Variante de compute_rvol_from_df que elige como 'session_day' la última
    sesión que tenga la barra de cierre RTH completa (última vela >= 16:00)
    y calcula RVol usando esa sesión.
    """
    comps = get_rvol_components_last_complete(df_agg)
    if comps is None:
        return None
    current_cum, prior_cums, avg_prior, bar_ts = comps
    if avg_prior is None or avg_prior <= 0:
        return None
    return current_cum / avg_prior

def get_rvol_components_last_complete(df_agg: pd.DataFrame):
    """
    Igual que get_rvol_components pero busca la última sesión "completa" (última vela >= 16:00).
    Devuelve (current_cum, prior_cums, avg_prior, bar_ts) o None.
    """
    try:
        if df_agg is None or df_agg.empty:
            return None
        df = df_agg.copy()
        if df.index.tz is None:
            df.index = df.index.tz_localize(TZ_NY)
        else:
            df.index = df.index.tz_convert(TZ_NY)

        session_days = sorted({d for d in df.index.date})
        if not session_days:
            return None

        # buscar la última sesión que tenga al menos una vela a/b >= 16:00
        candidate_day = None
        for d in reversed(session_days):
            day_df = df[df.index.date == d]
            if day_df.empty:
                continue
            last_time = day_df.index.max().time()
            if last_time >= time(16, 0):
                candidate_day = d
                break

        # si no se encontró sesión con cierre completo, tomar la última disponible (fallback)
        if candidate_day is None:
            candidate_day = session_days[-1]

        # ahora replicamos la lógica para esa session_day
        session_day = candidate_day
        today_bars = df[df.index.date == session_day]
        if today_bars.empty:
            return None
        last_time_today = today_bars.index.max().time()
        start_today = time(9, 30)
        end_today = min(last_time_today, time(16, 0))
        if start_today > end_today:
            return None

        current_df = df[(df.index.date == session_day) & (df.index.time >= start_today) & (df.index.time <= end_today)]
        if current_df.empty:
            return None

        current_cum = float(current_df["volume"].sum())
        bar_ts = current_df.index.max()

        prior_days = [d for d in session_days if d < session_day]
        prior_days = prior_days[-N_DAYS:]
        prior_cums = []
        for d in prior_days:
            day_df = df[df.index.date == d]
            if day_df.empty:
                continue
            d_df = day_df[(day_df.index.time >= time(9,30)) & (day_df.index.time <= min(end_today, time(16,0)))]
            if not d_df.empty:
                prior_cums.append(float(d_df["volume"].sum()))

        if len(prior_cums) < MIN_PRIOR_DAYS_FOR_RVOL:
            return None

        avg_prior = sum(prior_cums) / len(prior_cums)
        if avg_prior <= 0:
            return None

        return (current_cum, prior_cums, float(avg_prior), bar_ts)
    except Exception:
        return None

def get_rvol_components(df_agg: pd.DataFrame):
    """
    Extrae (current_cum, prior_cums, avg_prior, bar_ts) del DataFrame 15m (misma lógica que compute_rvol_from_df).
    Devuelve None si no es posible calcular.
    """
    try:
        if df_agg is None or df_agg.empty:
            return None
        df = df_agg.copy()
        if df.index.tz is None:
            df.index = df.index.tz_localize(TZ_NY)
        else:
            df.index = df.index.tz_convert(TZ_NY)

        session_days = sorted({d for d in df.index.date})
        if not session_days:
            return None
        session_day = session_days[-1]

        today_bars = df[df.index.date == session_day]
        if today_bars.empty:
            return None
        last_time_today = today_bars.index.max().time()
        start_today = time(9, 30)
        end_today = min(last_time_today, time(16, 0))
        if start_today > end_today:
            return None

        current_df = df[(df.index.date == session_day) & (df.index.time >= start_today) & (df.index.time <= end_today)]
        if current_df.empty:
            return None

        current_cum = float(current_df["volume"].sum())
        bar_ts = current_df.index.max()

        prior_days = [d for d in session_days if d < session_day]
        prior_days = prior_days[-N_DAYS:]
        prior_cums = []
        for d in prior_days:
            day_df = df[df.index.date == d]
            if day_df.empty:
                continue
            d_df = day_df[(day_df.index.time >= time(9,30)) & (day_df.index.time <= min(end_today, time(16,0)))]
            if not d_df.empty:
                prior_cums.append(float(d_df["volume"].sum()))

        if len(prior_cums) < MIN_PRIOR_DAYS_FOR_RVOL:
            return None

        avg_prior = sum(prior_cums) / len(prior_cums)
        if avg_prior <= 0:
            return None

        return (current_cum, prior_cums, float(avg_prior), bar_ts)
    except Exception:
        return None


def get_spy_hourly_components(df_1h: pd.DataFrame, lookback_days: int):
    """
    Extrae (rvol, current_cum, prior_cums, avg_prior, bar_ts) para SPY 1H.
    Si para un día previo no existe la vela exactamente a `current_hour`, busca
    retrocediendo hasta encontrar un día con esa misma hora. Evita reutilizar
    la misma fecha sustituta más de una vez.
    Devuelve None si no es posible.
    """
    try:
        if df_1h is None or df_1h.empty:
            return None
        df = df_1h.copy()
        if isinstance(df.index, pd.DatetimeIndex):
            idx = pd.to_datetime(df.index)
            if idx.tz is None:
                idx = idx.tz_localize(TZ_NY)
            else:
                idx = idx.tz_convert(TZ_NY)
            df.index = idx
        else:
            return None

        df = df.sort_index()
        current_ts = df.index.max()
        current_day = current_ts.date()
        current_hour = current_ts.time()

        # acumulado HOY hasta current_hour
        today_df = df[df.index.date == current_day]
        today_df = today_df[today_df.index.time <= current_hour]
        if today_df.empty:
            return None

        current_cum = float(today_df["volume"].sum())
        bar_ts = today_df.index.max()

        # todos los días anteriores disponibles (orden cronológico asc)
        prior_days_all = sorted({d for d in df.index.date if d < current_day})
        if not prior_days_all:
            return None

        # tomamos la ventana nominal de días más recientes a considerar
        candidate_window = prior_days_all[-lookback_days:] if len(prior_days_all) >= lookback_days else prior_days_all[:]

        prior_cums = []
        used_dates = set()

        # helper: devuelve cumulative hasta current_hour en 'day' si existe vela en esa hora
        def cum_for_day(day):
            day_df = df[df.index.date == day]
            if day_df.empty:
                return None
            # debe existir una vela en la hora exacta para considerarlo válido
            if any(t == current_hour for t in day_df.index.time):
                return float(day_df[day_df.index.time <= current_hour]["volume"].sum())
            return None

        # procesamos desde el día más cercano hacia atrás
        for d in reversed(candidate_window):
            # intentar usar d o, si no tiene la hora, buscar hacia atrás en prior_days_all
            found = False
            # índice en prior_days_all
            try:
                pos = prior_days_all.index(d)
            except ValueError:
                pos = None

            # primero probar el propio día d
            cum = cum_for_day(d)
            if cum is not None and d not in used_dates:
                prior_cums.append(cum)
                used_dates.add(d)
                found = True
            else:
                # buscar día anterior no usada que sí tenga la vela en current_hour
                if pos is not None:
                    for j in range(pos - 1, -1, -1):
                        cand = prior_days_all[j]
                        if cand in used_dates:
                            continue
                        cum_cand = cum_for_day(cand)
                        if cum_cand is not None:
                            prior_cums.append(cum_cand)
                            used_dates.add(cand)
                            found = True
                            break
            # si no se encuentra ninguno, simplemente saltar (no duplicar)
            if len(prior_cums) >= lookback_days:
                break

        # requisitos mínimos
        if len(prior_cums) < MIN_PRIOR_DAYS_FOR_RVOL:
            return None

        avg_prior = sum(prior_cums) / len(prior_cums)
        if avg_prior <= 0:
            return None

        rvol = float(current_cum / avg_prior)
        return (rvol, current_cum, prior_cums, float(avg_prior), bar_ts)
    except Exception:
        return None

# ========== INDICATOR CALCS ==========
def compute_rvol_from_df(df_agg: pd.DataFrame):
    """
    RVol computed using RTH windows only (9:30 - 16:00). This function
    assumes we only care about regular trading hours data.
    """
    if df_agg is None or df_agg.empty:
        return None
    df = df_agg.copy()
    # ensure tz
    if df.index.tz is None:
        df.index = df.index.tz_localize(TZ_NY)
    else:
        df.index = df.index.tz_convert(TZ_NY)

    session_days = sorted({d for d in df.index.date})
    if not session_days:
        return None

    session_day = session_days[-1]

    # RTH window for current day: 09:30 -> min(last_bar, 16:00)
    today_bars = df[df.index.date == session_day]
    if today_bars.empty:
        return None
    last_time_today = today_bars.index.max().time()
    start_today = time(9, 30)
    end_today = min(last_time_today, time(16, 0))
    if start_today > end_today:
        return None

    current_df = df[(df.index.date == session_day) &
                    (df.index.time >= start_today) &
                    (df.index.time <= end_today)]
    if current_df.empty:
        return None

    current_cum = current_df["volume"].sum()

    prior_days = [d for d in session_days if d < session_day]
    prior_days = prior_days[-N_DAYS:]  # up to N_DAYS previous sessions
    prior_cums = []
    for d in prior_days:
        day_df = df[df.index.date == d]
        if day_df.empty:
            continue
        d_df = day_df[(day_df.index.time >= time(9,30)) & (day_df.index.time <= min(end_today, time(16,0)))]
        if not d_df.empty:
            prior_cums.append(d_df["volume"].sum())

    if len(prior_cums) < MIN_PRIOR_DAYS_FOR_RVOL:
        return None

    avg_prior = sum(prior_cums) / len(prior_cums)
    if avg_prior <= 0:
        return None
    return current_cum / avg_prior
    
def compute_spy_rvol_hourly(df_1h: pd.DataFrame, lookback_days: int) -> float | None:
    """
    Replica EXACTA de la lógica PineScript 'Relative Volume at Time'
    usando barras de 1H.
    """

    if df_1h is None or df_1h.empty:
        return None

    df = df_1h.copy()

    # asegurar datetime index NY
    if isinstance(df.index, pd.DatetimeIndex):
        idx = pd.to_datetime(df.index)
        if idx.tz is None:
            idx = idx.tz_localize(TZ_NY)
        else:
            idx = idx.tz_convert(TZ_NY)
        df.index = idx
    else:
        return None

    df = df.sort_index()

    # día y hora actual (última barra cerrada)
    current_ts = df.index.max()
    current_day = current_ts.date()
    current_hour = current_ts.time()

    # volumen acumulado HOY hasta current_hour
    today_df = df[df.index.date == current_day]
    today_df = today_df[today_df.index.time <= current_hour]

    if today_df.empty:
        return None

    current_cum = today_df["volume"].sum()

    # días anteriores
    prior_days = sorted({d for d in df.index.date if d < current_day})
    prior_days = prior_days[-lookback_days:]

    prior_cums = []

    for d in prior_days:
        d_df = df[df.index.date == d]
        d_df = d_df[d_df.index.time <= current_hour]
        if not d_df.empty:
            prior_cums.append(d_df["volume"].sum())

    if len(prior_cums) < MIN_PRIOR_DAYS_FOR_RVOL:
        return None

    avg_prior = sum(prior_cums) / len(prior_cums)
    if avg_prior <= 0:
        return None

    return round(float(current_cum / avg_prior), 2)

def compute_rrs_and_corr(df_sym: pd.DataFrame, df_spy: pd.DataFrame, length: int = RRS_LENGTH):
    if df_sym is None or df_spy is None:
        return None, None
    idx = df_sym.index.intersection(df_spy.index)
    if len(idx) < length + 1:
        return None, None
    idx = idx.sort_values()[-(length+1):]
    sym = df_sym.reindex(idx)
    spy = df_spy.reindex(idx)

    try:
        move_sym = sym["close"].iloc[-1] - sym["close"].iloc[-1 - length]
        move_spy = spy["close"].iloc[-1] - spy["close"].iloc[-1 - length]
    except Exception:
        return None, None

    prev_s = sym["close"].shift(1)
    tr_s = pd.concat([
        sym["high"] - sym["low"],
        (sym["high"] - prev_s).abs(),
        (sym["low"] - prev_s).abs()
    ], axis=1).max(axis=1)
    atr_sym = tr_s.rolling(length).mean().iloc[-2]

    prev_p = spy["close"].shift(1)
    tr_p = pd.concat([
        spy["high"] - spy["low"],
        (spy["high"] - prev_p).abs(),
        (spy["low"] - prev_p).abs()
    ], axis=1).max(axis=1)
    atr_spy = tr_p.rolling(length).mean().iloc[-2]

    if pd.isna(atr_sym) or pd.isna(atr_spy) or atr_sym == 0:
        return None, None

    power = move_spy / atr_spy
    rrs = (move_sym - power * atr_sym) / atr_sym
    corr = sym["close"].iloc[-length:].corr(spy["close"].iloc[-length:])
    return round(float(rrs), 2), round(float(corr), 2) if corr is not None else None

# ========== BOOTSTRAP FROM DISK ==========
def populate_from_disk_cache():
    """
    Carga cachés desde disco en `disk_cache` y rellena `latest_results` con valores iniciales.
    Además escribe un log de auditoría para cada RVol inicial si es posible.
    """
    global disk_cache
    disk_cache = {}

    # --- Load RVOL_15M for RVol first ---
    for t in TICKERS:
        df_rvol = load_disk_cache(t, "RVOL_15M")
        if df_rvol is not None:
            disk_cache[(t, "RVOL_15M")] = df_rvol

            # intento primario de cálculo
            rvol = compute_rvol_from_df(df_rvol)
            # si falla intentamos con la última sesión completa como fallback
            if rvol is None:
                rvol = compute_rvol_from_last_complete_day(df_rvol)

            with state_lock:
                latest_results[t]["RVol"] = round(rvol, 2) if rvol is not None else None

            # audit log: intentamos obtener componentes legibles para el log inicial
            comps = get_rvol_components(df_rvol)
            used_tag = "15M_init"
            if comps is None:
                # fallback a la última sesión completa para poder loggear componentes
                comps = get_rvol_components_last_complete(df_rvol)
                used_tag = "15M_init_last_complete"

            if comps is not None:
                current_cum, prior_cums, avg_prior, bar_ts = comps
            else:
                current_cum = prior_cums = avg_prior = bar_ts = None

            # fuerza escritura del log inicial (incluso si rvol es None, escribimos la fila para auditoría)
            try:
                log_rvol_to_csv(t, used_tag, bar_ts, current_cum, prior_cums, avg_prior, rvol)
            except Exception:
                pass

        else:
            with state_lock:
                latest_results[t]["RVol"] = None

    # --- Load SPY caches for each tf ---
    for tf in TIMEFRAMES:
        df_spy = load_disk_cache("SPY", tf)
        if df_spy is not None:
            disk_cache[(COMPARE_WITH, tf)] = df_spy
            spy_cache[tf] = {"df": df_spy, "ts": _time.time()}

    # --- Load RRS caches and compute RRS/corr if possible (using SPY cache) ---
    for t in TICKERS:
        for tf in TIMEFRAMES:
            df = load_disk_cache(t, tf)
            if df is not None:
                disk_cache[(t, tf)] = df
                if spy_cache[tf]["df"] is not None:
                    rrs, corr = compute_rrs_and_corr(df, spy_cache[tf]["df"])
                    with state_lock:
                        latest_results[t][tf]["RRS"] = rrs
                        latest_results[t][tf]["corr"] = corr
                        latest_results[t][tf]["bgcolor"] = map_corr_to_color(corr)
                else:
                    with state_lock:
                        latest_results[t][tf]["RRS"] = None
                        latest_results[t][tf]["corr"] = None
                        latest_results[t][tf]["bgcolor"] = "white"
            else:
                # ensure placeholders exist so later logic doesn't KeyError
                if (t, tf) not in disk_cache:
                    disk_cache[(t, tf)] = pd.DataFrame()
                    with state_lock:
                        latest_results[t][tf]["RRS"] = None
                        latest_results[t][tf]["corr"] = None
                        latest_results[t][tf]["bgcolor"] = "white"

    # --- Load SPY 1H cache (if exists) so hourly RVol can use it immediately ---
    df_spy_1h = load_spy_1h_cache()
    if df_spy_1h is not None and not df_spy_1h.empty:
        try:
            cutoff = datetime.now(pytz.utc).astimezone(TZ_NY).replace(minute=0, second=0, microsecond=0)
            df_trim = df_spy_1h[df_spy_1h.index <= cutoff]
            if not df_trim.empty:
                spy_rvol_state["Q"]  = compute_spy_rvol_hourly(df_trim, 60)
                spy_rvol_state["M"]  = compute_spy_rvol_hourly(df_trim, 20)
                spy_rvol_state["2W"] = compute_spy_rvol_hourly(df_trim, 10)
                spy_rvol_state["1W"] = compute_spy_rvol_hourly(df_trim, 5)
                spy_rvol_state["last_date"] = cutoff.date()
                spy_rvol_state["last_hour"] = int(cutoff.hour)
                spy_rvol_state["last_update"] = datetime.now(TZ_NY).strftime("%Y-%m-%d %H:%M:%S")
                # guardamos el timestamp de la última barra usada (tz-aware)
                spy_rvol_state["last_ts"] = df_trim.index.max()

                # audit log for SPY initial (if possible)
                try:
                    sp_comps = get_spy_hourly_components(df_trim, 60)
                    if sp_comps is not None:
                        r_q, curr_q, hist_q, avg_q, ts_q = sp_comps
                        log_rvol_to_csv("SPY", "1H_init_Q", ts_q, curr_q, hist_q, avg_q, r_q)
                except Exception:
                    pass
        except Exception:
            pass

# ========== IB WORKER (incremental update, scheduled to TF boundaries) ==========
def ib_worker():
    global initial_update_done, updating, last_full_update, disk_cache, spy_cache, progress, stage2
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    ib = IB()
    loop.run_until_complete(ib.connectAsync(IB_HOST, IB_PORT, clientId=IB_CLIENT_ID, timeout=10))

    contracts = [Stock(t, "SMART", "USD") for t in TICKERS]
    loop.run_until_complete(ib.qualifyContractsAsync(*contracts))
    cmap = {c.symbol: c for c in contracts}

    spy_contract = Stock(COMPARE_WITH, "SMART", "USD")
    loop.run_until_complete(ib.qualifyContractsAsync(spy_contract))

    # helper to request historical data with retries and small pacing
    # Default useRTH=True now to request regular trading hours only
    def safe_req_hist(contract, durationStr, barSize, useRTH=True, retries=3, pause=0.25, end_dt: datetime | None = None):
        """
        Wrapper para reqHistoricalDataAsync que permite pasar end_dt (datetime aware en TZ_NY)
        para forzar pedir barras hasta la frontera anterior (última vela cerrada).
        end_dt: datetime aware en TZ_NY (si None, se deja cadena vacía -> IB usará 'now')
        """
        if end_dt is not None:
            # asegurarnos timezone NY
            if end_dt.tzinfo is None:
                end_dt = end_dt.tz_localize(TZ_NY)
            else:
                end_dt = end_dt.astimezone(TZ_NY)
            end_str = end_dt.strftime("%Y%m%d %H:%M:%S")
        else:
            end_str = ""

        for attempt in range(retries):
            try:
                bars = loop.run_until_complete(ib.reqHistoricalDataAsync(
                    contract, end_str, durationStr, barSize, "TRADES", useRTH=useRTH, formatDate=1
                ))
            except Exception:
                bars = None
            _time.sleep(pause)
            if bars:
                return bars
            pause += 0.1
        return None

    # initial values for progress
    total_tasks = len(TICKERS) * (1 + len(TIMEFRAMES))
    progress["total"] = total_tasks
    progress["processed"] = 0
    updating = True

    # First full pass: for each ticker download missing data (incremental) for RVOL_15M and all timeframes
    for t in TICKERS:
        # ---- RVol (15M) ----
        cached_rvol = disk_cache.get((t, "RVOL_15M"))
        last_ts = cached_rvol.index.max() if (cached_rvol is not None and not cached_rvol.empty) else None

        # freshness threshold
        CACHE_FRESH_SECONDS = 15 * 60
        now_ny = datetime.now(pytz.utc).astimezone(TZ_NY)
        skip_fetch = False
        if last_ts is not None:
            if last_ts.tzinfo is None:
                last_ts = last_ts.tz_localize(TZ_NY)
            else:
                last_ts = last_ts.tz_convert(TZ_NY)
            age_seconds = (now_ny - last_ts).total_seconds()
            if age_seconds <= CACHE_FRESH_SECONDS:
                skip_fetch = True

        if skip_fetch:
            df_comb = cached_rvol
            rvol = compute_rvol_from_df(df_comb)
            with state_lock:
                latest_results[t]["RVol"] = round(rvol, 2) if rvol is not None else None

            # audit log: extraer componentes y guardar
            comps = get_rvol_components(df_comb)
            if comps is not None:
                current_cum, prior_cums, avg_prior, bar_ts = comps
            else:
                current_cum = prior_cums = avg_prior = bar_ts = None
            try:
                log_rvol_to_csv(t, "15M_fullpass", bar_ts, current_cum, prior_cums, avg_prior, rvol)
            except Exception:
                pass
            progress["processed"] += 1
            continue

        # primary attempt: 8 days (RTH) -> más margen para sesiones parciales/feriados
        bars = safe_req_hist(cmap[t], "8 D", "15 mins", useRTH=True, retries=3, pause=0.15)
        # fallback: try 9 days if 8D returned nothing
        if not bars:
            bars = safe_req_hist(cmap[t], "9 D", "15 mins", useRTH=True, retries=2, pause=0.15)

        if bars:
            df_new = util.df(bars)
            df_new["date"] = pd.to_datetime(df_new["date"])
            if df_new["date"].dt.tz is None:
                df_new["date"] = df_new["date"].dt.tz_localize(TZ_NY)
            else:
                df_new["date"] = df_new["date"].dt.tz_convert(TZ_NY) 
            df_new.set_index("date", inplace=True)

            # 🔥 eliminar vela en curso (15M)
            df_new = drop_partial_bar_if_needed(df_new, TF_BASE_SECONDS["15M"], end_dt=None)

            df_new = df_new[~df_new.index.duplicated(keep="last")].sort_index()

            if last_ts is not None and cached_rvol is not None and not cached_rvol.empty:
                df_comb = pd.concat([cached_rvol, df_new[df_new.index > last_ts]])
            else:
                df_comb = df_new
            disk_cache[(t, "RVOL_15M")] = df_comb
            save_disk_cache(t, "RVOL_15M", df_comb)

            rvol = compute_rvol_from_df(df_comb)
            with state_lock:
                latest_results[t]["RVol"] = round(rvol, 2) if rvol is not None else None
        else:
            # ensure placeholder to avoid repeated expensive retries and keep cache consistent
            if (t, "RVOL_15M") not in disk_cache:
                disk_cache[(t, "RVOL_15M")] = pd.DataFrame()
                save_disk_cache(t, "RVOL_15M", pd.DataFrame())
            with state_lock:
                latest_results[t]["RVol"] = None

        progress["processed"] += 1

    # SPY initial cache updates for all TFs
    for tf, (barSize, duration) in TIMEFRAMES.items():
        cached_spy = disk_cache.get((COMPARE_WITH, tf))
        last_ts = cached_spy.index.max() if (cached_spy is not None and not cached_spy.empty) else None

        bars = safe_req_hist(spy_contract, duration, barSize, useRTH=True, retries=3, pause=0.15)
        if bars:
            df_new = util.df(bars)
            df_new["date"] = pd.to_datetime(df_new["date"])
            if df_new["date"].dt.tz is None:
                df_new["date"] = df_new["date"].dt.tz_localize(TZ_NY)
            else:
                df_new["date"] = df_new["date"].dt.tz_convert(TZ_NY)
            df_new.set_index("date", inplace=True)

            # 🔥 eliminar vela en curso (según TF)
            df_new = drop_partial_bar_if_needed(df_new, TF_BASE_SECONDS[tf], end_dt=None)

            df_new = df_new[~df_new.index.duplicated(keep="last")].sort_index()

            if last_ts is not None:
                df_comb = pd.concat([cached_spy, df_new[df_new.index > last_ts]])
            else:
                df_comb = df_new
            disk_cache[(COMPARE_WITH, tf)] = df_comb
            spy_cache[tf] = {"df": df_comb, "ts": _time.time()}
            save_disk_cache(COMPARE_WITH, tf, df_comb)

    # SPY 1H initial: if no cache, fetch full 65D 1H (only once at startup)
    df_spy_1h_cache = load_spy_1h_cache()
    if df_spy_1h_cache is None or df_spy_1h_cache.empty:
        bars_1h_full = safe_req_hist(spy_contract, "65 D", "1 hour", useRTH=True, retries=3, pause=0.2)
        if bars_1h_full:
            df1h = util.df(bars_1h_full)
            if "date" in df1h.columns:
                df1h["date"] = pd.to_datetime(df1h["date"])
                if df1h["date"].dt.tz is None:
                    df1h["date"] = df1h["date"].dt.tz_localize(TZ_NY)
                else:
                    df1h["date"] = df1h["date"].dt.tz_convert(TZ_NY)
                df1h.set_index("date", inplace=True)
            elif isinstance(df1h.index, pd.DatetimeIndex):
                idx = pd.to_datetime(df1h.index)
                if idx.tz is None:
                    idx = idx.tz_localize(TZ_NY)
                else:
                    idx = idx.tz_convert(TZ_NY)
                df1h.index = idx
            df1h.index.name = "datetime"
            df1h = df1h[~df1h.index.duplicated(keep="last")].sort_index()
            save_spy_1h_cache(df1h)
            df_spy_1h_cache = df1h
    else:
        df_spy_1h_cache = df_spy_1h_cache

    # Now RRS for tickers that passed RVol filter (initial)
    for t in TICKERS:
        rvol_val = latest_results[t]["RVol"]
        if rvol_val is None or rvol_val < RVOL_THRESHOLD:
            progress["processed"] += len(TIMEFRAMES)
            continue

        # mark as stage2 initially
        stage2.add(t)

        for tf, (barSize, duration) in TIMEFRAMES.items():
            cached = disk_cache.get((t, tf))
            last_ts = cached.index.max() if (cached is not None and not cached.empty) else None

            bars = safe_req_hist(cmap[t], duration, barSize, useRTH=True, retries=3, pause=0.12)
            if bars:
                df_new = util.df(bars)
                df_new["date"] = pd.to_datetime(df_new["date"])
                if df_new["date"].dt.tz is None:
                    df_new["date"] = df_new["date"].dt.tz_localize(TZ_NY)
                else:
                    df_new["date"] = df_new["date"].dt.tz_convert(TZ_NY)
                df_new.set_index("date", inplace=True)

                # 🔥 eliminar vela en curso (según TF)
                df_new = drop_partial_bar_if_needed(df_new, TF_BASE_SECONDS[tf], end_dt=None)

                df_new = df_new[~df_new.index.duplicated(keep="last")].sort_index()

                if last_ts is not None:
                    df_comb = pd.concat([cached, df_new[df_new.index > last_ts]])
                else:
                    df_comb = df_new
                df_comb = df_comb[~df_comb.index.duplicated(keep="last")].sort_index()
                disk_cache[(t, tf)] = df_comb
                save_disk_cache(t, tf, df_comb)

                spy_df = spy_cache[tf]["df"] if spy_cache[tf]["df"] is not None else disk_cache.get((COMPARE_WITH, tf))
                if spy_df is not None:
                    rrs, corr = compute_rrs_and_corr(df_comb, spy_df)
                    with state_lock:
                        # --- audit log: RRS / corr (initial) ---
                        try:
                            path_rrs = LOG_DIR / f"{t}_rrs.csv"
                            write_header = not path_rrs.exists()
                            with open(path_rrs, "a", newline="", encoding="utf-8") as frrs:
                                w = csv.writer(frrs)
                                if write_header:
                                    w.writerow(["timestamp", "phase", "tf", "rrs", "corr", "last_close_sym", "last_close_spy"])
                                last_close_sym = df_comb["close"].iloc[-1] if "close" in df_comb.columns and not df_comb.empty else ""
                                last_close_spy = spy_df.reindex(df_comb.index)["close"].iloc[-1] if (isinstance(spy_df, pd.DataFrame) and "close" in spy_df.columns and not spy_df.empty) else ""
                                w.writerow([datetime.now(TZ_NY).strftime("%Y-%m-%d %H:%M:%S"), "initial", tf, rrs, corr, last_close_sym, last_close_spy])
                        except Exception:
                            pass
                    
                        latest_results[t][tf]["RRS"] = rrs
                        latest_results[t][tf]["corr"] = corr
                        latest_results[t][tf]["bgcolor"] = map_corr_to_color(corr)
            else:
                # placeholder to avoid repeated attempts
                if (t, tf) not in disk_cache:
                    disk_cache[(t, tf)] = pd.DataFrame()
                    save_disk_cache(t, tf, pd.DataFrame())
            progress["processed"] += 1

    # first full pass done
    initial_update_done = True
    updating = False
    last_full_update = datetime.now()

    # helper to compute durationStr in seconds to request enough recent bars to allow RRS calc
    def compute_duration_seconds(tf_key):
        base = TF_BASE_SECONDS.get(tf_key, 60)
        bars_needed = RRS_LENGTH + 5
        return int(base * bars_needed)

    # After initial pass, continue incremental updates periodically
    while True:
        now_utc = datetime.now(pytz.utc)
        now_ny = now_utc.astimezone(TZ_NY)
        sec = now_ny.second
        minute = now_ny.minute
        hour = now_ny.hour

        # ensure we run after a small delay past the minute boundary so last bar is available
        if sec < 6:
            _time.sleep(0.3)
            continue

        # ---- Update SPY and stage2 RRS for each TF that closes now ----
        for tf_key, (barSize, _) in TIMEFRAMES.items():
            do_tf = False
            if tf_key == "1M":
                do_tf = True
            elif tf_key == "5M" and (minute % 5 == 0):
                do_tf = True
            elif tf_key == "15M" and (minute % 15 == 0):
                do_tf = True

            if not do_tf:
                continue

            # calcular duration y end_dt para pedir la última vela CERRADA del timeframe
            duration_seconds = compute_duration_seconds(tf_key)
            durationStr = f"{duration_seconds} S"

            # tf_seconds: segundos del timeframe (1M/5M/15M)
            tf_seconds = TF_BASE_SECONDS.get(tf_key, 60)
            now_ny_local = datetime.now(pytz.utc).astimezone(TZ_NY)
            # floor y tomar la frontera ANTERIOR para garantizar vela cerrada
            end_dt = floor_to_tf(now_ny_local, tf_seconds) - pd.Timedelta(seconds=tf_seconds)

            # pedir SPY hasta end_dt (última vela cerrada)
            bars_spy = safe_req_hist(spy_contract, durationStr, barSize, useRTH=True, retries=2, pause=0.12, end_dt=end_dt)

            if bars_spy:
                df_spy_new = util.df(bars_spy)
                df_spy_new["date"] = pd.to_datetime(df_spy_new["date"])
                if df_spy_new["date"].dt.tz is None:
                    df_spy_new["date"] = df_spy_new["date"].dt.tz_localize(TZ_NY)
                else:
                    df_spy_new["date"] = df_spy_new["date"].dt.tz_convert(TZ_NY)
                df_spy_new.set_index("date", inplace=True)

                cached_spy = disk_cache.get((COMPARE_WITH, tf_key))
                if cached_spy is not None and not cached_spy.empty:
                    last_ts = cached_spy.index.max()
                    df_spy_comb = pd.concat([cached_spy, df_spy_new[df_spy_new.index > last_ts]])
                else:
                    df_spy_comb = df_spy_new
                disk_cache[(COMPARE_WITH, tf_key)] = df_spy_comb
                spy_cache[tf_key] = {"df": df_spy_comb, "ts": _time.time()}
                save_disk_cache(COMPARE_WITH, tf_key, df_spy_comb)
            else:
                df_spy_comb = disk_cache.get((COMPARE_WITH, tf_key))

            spy_df = None
            sc = spy_cache.get(tf_key, {})
            sc_df = sc.get("df") if isinstance(sc, dict) else None
            if sc_df is not None and hasattr(sc_df, "empty") and not sc_df.empty:
                spy_df = sc_df
            else:
                tmp = disk_cache.get((COMPARE_WITH, tf_key))
                if tmp is not None and not tmp.empty:
                    spy_df = tmp

            # now update each ticker in stage2 for this TF
            for t in list(stage2):
                contract = cmap.get(t)
                if contract is None:
                    continue
                bars_sym = safe_req_hist(contract, durationStr, barSize, useRTH=True, retries=2, pause=0.12, end_dt=end_dt)

                if not bars_sym:
                    continue

                df_sym_new = util.df(bars_sym)
                df_sym_new["date"] = pd.to_datetime(df_sym_new["date"])
                if df_sym_new["date"].dt.tz is None:
                    df_sym_new["date"] = df_sym_new["date"].dt.tz_localize(TZ_NY)
                else:
                    df_sym_new["date"] = df_sym_new["date"].dt.tz_convert(TZ_NY)
                df_sym_new.set_index("date", inplace=True)

                cached_tf = disk_cache.get((t, tf_key))
                if cached_tf is not None and not cached_tf.empty:
                    last_ts = cached_tf.index.max()
                    df_comb = pd.concat([cached_tf, df_sym_new[df_sym_new.index > last_ts]])
                else:
                    df_comb = df_sym_new

                df_comb = df_comb[~df_comb.index.duplicated(keep="last")].sort_index()
                disk_cache[(t, tf_key)] = df_comb
                save_disk_cache(t, tf_key, df_comb)

                if spy_df is None:
                    continue
                rrs, corr = compute_rrs_and_corr(df_comb, spy_df)
                with state_lock:
                    # --- audit log: RRS / corr (incremental) ---
                    try:
                        path_rrs = LOG_DIR / f"{t}_rrs.csv"
                        write_header = not path_rrs.exists()
                        with open(path_rrs, "a", newline="", encoding="utf-8") as frrs:
                            w = csv.writer(frrs)
                            if write_header:
                                w.writerow(["timestamp", "phase", "tf", "rrs", "corr", "last_close_sym", "last_close_spy"])
                            last_close_sym = df_comb["close"].iloc[-1] if "close" in df_comb.columns and not df_comb.empty else ""
                            last_close_spy = spy_df.reindex(df_comb.index)["close"].iloc[-1] if (isinstance(spy_df, pd.DataFrame) and "close" in spy_df.columns and not spy_df.empty) else ""
                            w.writerow([datetime.now(TZ_NY).strftime("%Y-%m-%d %H:%M:%S"), "incremental", tf_key, rrs, corr, last_close_sym, last_close_spy])
                    except Exception:
                        pass

                    latest_results[t][tf_key]["RRS"] = rrs
                    latest_results[t][tf_key]["corr"] = corr
                    latest_results[t][tf_key]["bgcolor"] = map_corr_to_color(corr)

        # ---- Every 15 minutes: recompute RVol for all tickers and update stage2 set ----
        now_utc2 = datetime.now(pytz.utc)
        now_ny2 = now_utc2.astimezone(TZ_NY)
        if now_ny2.minute % 15 == 0:
            _time.sleep(6)  # small delay to ensure last 15m bar available

            # inicializar progreso de recálculo RVol
            with state_lock:
                rvol_progress["running"] = True
                rvol_progress["processed"] = 0
                rvol_progress["total"] = len(TICKERS)
                rvol_progress["last_update"] = None

            for t in TICKERS:
                # forzar petición hasta la última barra 15m CERRADA
                tf_seconds_15m = 15 * 60
                now_ny_local2 = datetime.now(pytz.utc).astimezone(TZ_NY)
                end_dt_15m = floor_to_tf(now_ny_local2, tf_seconds_15m) - pd.Timedelta(seconds=tf_seconds_15m)

                # pedir 8 días por defecto para tener +2 sesiones de margen (feriados/media jornada)
                bars_15m = safe_req_hist(cmap[t], "8 D", "15 mins", useRTH=True, retries=2, pause=0.12, end_dt=end_dt_15m)

                if not bars_15m:
                    # fallback a 9 días si 8D falla
                    bars_15m = safe_req_hist(cmap[t], "9 D", "15 mins", useRTH=True, retries=1, pause=0.12, end_dt=end_dt_15m)

                if not bars_15m:
                    # si no hay datos, contamos como procesado y seguimos
                    with state_lock:
                        rvol_progress["processed"] += 1
                    continue

                df_new = util.df(bars_15m)
                df_new["date"] = pd.to_datetime(df_new["date"])
                if df_new["date"].dt.tz is None:
                    df_new["date"] = df_new["date"].dt.tz_localize(TZ_NY)
                else:
                    df_new["date"] = df_new["date"].dt.tz_convert(TZ_NY)
                df_new.set_index("date", inplace=True)
                df_new = df_new[~df_new.index.duplicated(keep="last")].sort_index()

                cached_rvol = disk_cache.get((t, "RVOL_15M"))
                if cached_rvol is not None and not cached_rvol.empty:
                    last_ts = cached_rvol.index.max()
                    df_comb = pd.concat([cached_rvol, df_new[df_new.index > last_ts]])
                else:
                    df_comb = df_new

                disk_cache[(t, "RVOL_15M")] = df_comb
                save_disk_cache(t, "RVOL_15M", df_comb)

                rvol = compute_rvol_from_df(df_comb)
                with state_lock:
                    latest_results[t]["RVol"] = round(rvol, 2) if rvol is not None else None

                # audit log: extraer componentes y guardar
                comps = get_rvol_components(df_comb)
                if comps is not None:
                    current_cum, prior_cums, avg_prior, bar_ts = comps
                else:
                    current_cum = prior_cums = avg_prior = bar_ts = None
                try:
                    log_rvol_to_csv(t, "15M_recalc15m", bar_ts, current_cum, prior_cums, avg_prior, rvol)
                except Exception:
                    pass

                # actualizar stage2 según rvol
                if rvol is not None and rvol >= RVOL_THRESHOLD:
                    if t not in stage2:
                        stage2.add(t)
                else:
                    if t in stage2:
                        stage2.remove(t)
                        with state_lock:
                            for tf in TIMEFRAMES:
                                latest_results[t][tf] = {"RRS": None, "corr": None, "bgcolor": "white"}

                # incrementar contador de progreso (siempre)
                with state_lock:
                    rvol_progress["processed"] += 1

            # marcar terminado y timestamp
            with state_lock:
                rvol_progress["running"] = False
                rvol_progress["last_update"] = now_ny2.strftime("%Y-%m-%d %H:%M:%S")

        _time.sleep(0.8)
        
        # ===== SPY RVOL HOURLY (cache incremental 1H) =====
        now_ny = datetime.now(pytz.utc).astimezone(TZ_NY)

        if now_ny.hour >= SPY_RVOL_START_HOUR:
            cutoff = now_ny.replace(minute=0, second=0, microsecond=0)

            # comprobar caché on-disk: si está por debajo de cutoff, forzamos fetch inmediatamente
            df_on_disk = load_spy_1h_cache()
            last_cache_ts = None
            if isinstance(df_on_disk, pd.DataFrame) and not df_on_disk.empty:
                last_cache_ts = df_on_disk.index.max()

            last_calc_hour = spy_rvol_state.get("last_hour")
            last_calc_date = spy_rvol_state.get("last_date")

            need_compute = False

            # nunca se calculó
            if last_calc_hour is None or last_calc_date is None:
                need_compute = True
            # cálculo existente pero fecha/hora distinta
            elif (last_calc_date != cutoff.date()) or (last_calc_hour != cutoff.hour):
                need_compute = True

            # si la caché on-disk no contiene la barra hasta 'cutoff', forzamos fetch/compute
            if last_cache_ts is None or last_cache_ts < cutoff:
                need_compute = True

            if need_compute:
                # si estamos exactamente en hh:00 esperar SPY_RVOL_DELAY_SEC segundos para que IB publique la barra 1H cerrada
                if now_ny.minute == 0 and now_ny.second < SPY_RVOL_DELAY_SEC:
                    pass
                else:
                    # update cache (1 petición corta) - esta función añade solo las barras nuevas al pkl
                    # calcular end_dt = frontera anterior a la hora actual (última 1H cerrada)
                    now_ny_for_spy = datetime.now(pytz.utc).astimezone(TZ_NY)
                    cutoff = now_ny_for_spy.replace(minute=0, second=0, microsecond=0)
                    end_dt_1h = cutoff - pd.Timedelta(hours=1)   # la hora iniciada anterior -> vela cerrada

                    # Si la caché on-disk no existe o está vacía, hacer un fetch completo de 65D (Q) para asegurar suficiente lookback
                    df_on_disk = load_spy_1h_cache()
                    if df_on_disk is None or df_on_disk.empty:
                        bars_1h_full = safe_req_hist(spy_contract, "65 D", "1 hour", useRTH=True, retries=3, pause=0.3)
                        if bars_1h_full:
                            df1h = util.df(bars_1h_full)
                            if "date" in df1h.columns:
                                df1h["date"] = pd.to_datetime(df1h["date"])
                                if df1h["date"].dt.tz is None:
                                    df1h["date"] = df1h["date"].dt.tz_localize(TZ_NY)
                                else:
                                    df1h["date"] = df1h["date"].dt.tz_convert(TZ_NY)
                                df1h.set_index("date", inplace=True)
                            elif isinstance(df1h.index, pd.DatetimeIndex):
                                idx = pd.to_datetime(df1h.index)
                                if idx.tz is None:
                                    idx = idx.tz_localize(TZ_NY)
                                else:
                                    idx = idx.tz_convert(TZ_NY)
                                df1h.index = idx
                            df1h.index.name = "datetime"
                            df1h = df1h[~df1h.index.duplicated(keep="last")].sort_index()
                            save_spy_1h_cache(df1h)
                            df_1h_cache = df1h
                        else:
                            # si tampoco conseguimos el fetch completo, intentar la actualización incremental (más pequeña)
                            df_1h_cache = update_spy_1h_cache(loop, ib, spy_contract, end_dt=end_dt_1h)
                    else:
                        # caché ya existe: intentar sólo añadir la(s) barra(s) nuevas (actual incremental)
                        df_1h_cache = update_spy_1h_cache(loop, ib, spy_contract, end_dt=end_dt_1h)

                    # cargar de nuevo caché on-disk por seguridad
                    df_1h_cache = load_spy_1h_cache()

                    if df_1h_cache is None or df_1h_cache.empty:
                        # no datos, dejamos estado previo
                        pass
                    else:
                        # quedarnos con barras hasta cutoff (última hora cerrada)
                        df_trim = df_1h_cache[df_1h_cache.index <= cutoff]
                        if df_trim.empty:
                            # intentar con la hora anterior si corte no disponible
                            df_trim = df_1h_cache[df_1h_cache.index <= (cutoff - pd.Timedelta(hours=1))]

                        if not df_trim.empty:
                            with state_lock:
                                # obtener componentes y rvol para cada lookback y loguear
                                res_q = get_spy_hourly_components(df_trim, 60)
                                res_m = get_spy_hourly_components(df_trim, 20)
                                res_2w = get_spy_hourly_components(df_trim, 10)
                                res_1w = get_spy_hourly_components(df_trim, 5)

                                if res_q is not None:
                                    q, q_curr, q_hist, q_avg, q_ts = res_q
                                    spy_rvol_state["Q"] = round(q, 2)
                                    try:
                                        log_rvol_to_csv("SPY", "1H_Q", q_ts, q_curr, q_hist, q_avg, q)
                                    except Exception:
                                        pass
                                else:
                                    spy_rvol_state["Q"] = None

                                if res_m is not None:
                                    m, m_curr, m_hist, m_avg, m_ts = res_m
                                    spy_rvol_state["M"] = round(m, 2)
                                    try:
                                        log_rvol_to_csv("SPY", "1H_M", m_ts, m_curr, m_hist, m_avg, m)
                                    except Exception:
                                        pass
                                else:
                                    spy_rvol_state["M"] = None

                                if res_2w is not None:
                                    w2, w2_curr, w2_hist, w2_avg, w2_ts = res_2w
                                    spy_rvol_state["2W"] = round(w2, 2)
                                    try:
                                        log_rvol_to_csv("SPY", "1H_2W", w2_ts, w2_curr, w2_hist, w2_avg, w2)
                                    except Exception:
                                        pass
                                else:
                                    spy_rvol_state["2W"] = None

                                if res_1w is not None:
                                    w1, w1_curr, w1_hist, w1_avg, w1_ts = res_1w
                                    spy_rvol_state["1W"] = round(w1, 2)
                                    try:
                                        log_rvol_to_csv("SPY", "1H_1W", w1_ts, w1_curr, w1_hist, w1_avg, w1)
                                    except Exception:
                                        pass
                                else:
                                    spy_rvol_state["1W"] = None

                                # registrar la hora/fecha de la barra usada para el cálculo
                                spy_rvol_state["last_hour"] = int(df_trim.index.max().hour)
                                spy_rvol_state["last_date"] = df_trim.index.max().date()
                                # timestamp legible (puedes cambiar zona si quieres mostrar CET)
                                spy_rvol_state["last_update"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        # ====================================================

# ========== start: load disk cache into memory results before launching UI ==========
populate_from_disk_cache()

threading.Thread(target=ib_worker, daemon=True).start()

# ========== DASH UI ==========
app = dash.Dash(__name__)
server = app.server   # IMPORTANTE para añadir ruta Flask

columns = (
    [{"name": "Ticker", "id": "Ticker"}]
    + [{"name": f"RRS {tf}", "id": f"RRS_{tf}"} for tf in TIMEFRAMES]
    + [{"name": "RVol", "id": "RVol"}]
)

app.layout = html.Div([

    # ================== INTERVALS ==================
    dcc.Interval(id="refresh", interval=5000),
    dcc.Interval(id="countdown_interval", interval=1000),

    # ================== SPY RVOL PANEL ==================
    html.Div(
        id="spy-rvol-panel",
        children=[
            html.Div("SPY RVol Q: --"),
            html.Div("SPY RVol M: --"),
            html.Div("SPY RVol 2W: --"),
            html.Div("SPY RVol 1W: --"),
        ],
        style={
            "display": "flex",
            "justifyContent": "center",
            "gap": "24px",
            "marginBottom": "10px",
            "fontWeight": "bold",
            "color": "white",
        }
    ),

    # ================== ESTADO CACHE INICIAL ==================
    html.Div(
        "Estado cache inicial: --",
        id="status",
        style={"marginBottom": "6px", "fontWeight": "bold", "color": "white"}
    ),

    # ================== ESTADO RECALCULO RVOL ==================
    html.Div(
        "Estado recálculo RVol: --",
        id="rvol-status",
        style={"marginBottom": "8px", "fontWeight": "bold", "color": "white"}
    ),

    # ================== CONTADOR ==================
    html.Div(
        f"Tickers en tabla: 0/{len(TICKERS)}",
        id="count-panel",
        style={"marginBottom": "6px", "color": "white"}
    ),

    # ================== TABLA PRINCIPAL ==================
    dash_table.DataTable(
        id="table",
        columns=columns,
        data=[],
        page_size=100,
        sort_action="native",

        style_cell={
            "textAlign": "center",
            "backgroundColor": "transparent",
            "color": "white",
            "border-color": "#99999954",
        },

        style_header={
            "backgroundColor": "transparent",
            "fontWeight": "bold",
            "border": "none"
        },
    ),

    # ================== BOTÓN ==================
    html.Div(
        style={"marginTop": "12px", "textAlign": "center"},
        children=[
            html.A(
                html.Button(
                    "Lasts RVol calculated",
                    style={"padding": "8px 16px", "fontWeight": "bold"}
                ),
                href="/rvol-all",
                target="_blank"
            )
        ]
    )
])

@server.route("/rvol-all")
def rvol_all():
    with state_lock:
        rows = []
        for t in TICKERS:
            rvol = latest_results.get(t, {}).get("RVol")
            rows.append(
                f"<tr><td>{t}</td><td>{rvol:.2f}</td></tr>"
                if rvol is not None else
                f"<tr><td>{t}</td><td>--</td></tr>"
            )

    table_html = """
    <html>
    <head><title>RVol All</title></head>
    <body>
        <h3>RVol – Último cálculo</h3>
        <table border="1" cellpadding="4" cellspacing="0">
            <tr><th>Ticker</th><th>RVol</th></tr>
            {}
        </table>
    </body>
    </html>
    """.format("".join(rows))

    return table_html

# ========== CALLBACK COUNTDOWN HEADERS ==========
@app.callback(
    Output("table", "columns"),
    Input("countdown_interval", "n_intervals")
)
def update_columns_with_countdown(n):
    cols = [{"name": "Ticker", "id": "Ticker"}]
    for tf in TIMEFRAMES:
        secs = seconds_until_tf_close(tf)
        cols.append({"name": f"RRS {tf} ({fmt_mmss(secs)})", "id": f"RRS_{tf}"})
    rvol_secs = seconds_until_rvol_refresh()
    cols.append({"name": f"RVol ({fmt_mmss(rvol_secs)})", "id": "RVol"})
    return cols
# ========== TABLE UPDATE CALLBACK ==========
@app.callback(
    Output("table", "data"),
    Output("table", "style_data_conditional"),
    Output("status", "children"),
    Input("refresh", "n_intervals")
)
def update(n):
    rows = []
    styles = []
    with state_lock:
        total = progress.get("total", 0)
        processed = progress.get("processed", 0)
        ready = initial_update_done

        for t in TICKERS:
            rvol = latest_results[t]["RVol"]
            if rvol is None or rvol < RVOL_THRESHOLD:
                continue

            # ----- estrella para favoritos -----
            fav_prefix = "★ " if t in FAVORITES else ""
            ticker_display = f"{fav_prefix}{t}"

            row = {
                "Ticker": ticker_display,
                "RVol": f"{rvol:.2f}"
            }

            for tf in TIMEFRAMES:
                rrs = latest_results[t][tf]["RRS"]
                row[f"RRS_{tf}"] = (
                    f"{rrs:.2f}" if (rrs is not None and not pd.isna(rrs)) else None
                )

                color = latest_results[t][tf].get("bgcolor", "white")
                styles.append({
                    "if": {
                        "filter_query": f'{{Ticker}} = "{ticker_display}"',
                        "column_id": f"RRS_{tf}"
                    },
                    "backgroundColor": color,
                    "color": "black"
                })

            # ----- estilo especial para favoritos -----
            if t in FAVORITES:
                styles.append({
                    "if": {
                        "filter_query": '{Ticker} contains "★"',
                        "column_id": "Ticker"
                    },
                    "fontWeight": "bold",
                    "color": "#FFD700"  # dorado
                })

            rows.append(row)

        if not ready:
            status_text = f"Updating initial cache: {processed}/{total} tasks completed..."
            status_color = "orange"
        else:
            status_text = f"Data ready (last full update: {last_full_update})"
            status_color = "green"

    return rows, styles, html.Span(status_text, style={"color": status_color})

# ========== SPY_RVol UPDATE CALLBACK ==========
@app.callback(
    Output("spy-rvol-panel", "children"),
    Input("refresh", "n_intervals")
)
def update_spy_rvol_panel(n):
    with state_lock:
        q  = spy_rvol_state["Q"]
        m  = spy_rvol_state["M"]
        w2 = spy_rvol_state["2W"]
        w1 = spy_rvol_state["1W"]

    def fmt(label, val):
        return html.Div(f"{label}: {val:.2f}" if val is not None else f"{label}: --")

    return [
        fmt("SPY RVol Q",  q),
        fmt("SPY RVol M",  m),
        fmt("SPY RVol 2W", w2),
        fmt("SPY RVol 1W", w1),
    ]

# ========== RVOL RECALC PROGRESS CALLBACK ==========
@app.callback(
    Output("rvol-status", "children"),
    Input("refresh", "n_intervals")
)
def update_rvol_status(n):
    with state_lock:
        rp = dict(rvol_progress)  # copia ligera
    if rp.get("running"):
        return html.Span(f"RVol recalculation: {rp.get('processed',0)}/{rp.get('total',0)} tasks completed...", style={"color": "orange"})
    else:
        last = rp.get("last_update")
        if last:
            return html.Span(f"RVol (last update: {last})", style={"color": "green"})
        else:
            return html.Span("RVol not yet recalculated", style={"color": "green"})

# ========== COUNT TICKER PANEL CALLBACK ==========
@app.callback(
    Output("count-panel", "children"),
    Input("refresh", "n_intervals")
)
def update_count_panel(n):
    with state_lock:
        total = len(TICKERS)
        count = 0
        for t in TICKERS:
            rv = latest_results.get(t, {}).get("RVol")
            if rv is not None:
                try:
                    if float(rv) >= float(RVOL_THRESHOLD):
                        count += 1
                except Exception:
                    # ignora valores no convertibles
                    continue

    return html.Span(f"{count}/{total} tickers")

# ========== RUN ==========
if __name__ == "__main__":
    webbrowser.open("http://127.0.0.1:8060")
    app.run(host="127.0.0.1", port=8060)
