
"""
App: Radar de Noticias de Impacto (Binarias/Scalping)
-----------------------------------------------------
Un panel en Streamlit que agrega noticias de múltiples fuentes (RSS),
detecta palabras clave de alto impacto macro/corporativo/cripto,
estima un "Buzz Score" (recencia + impacto + fuente + tendencia),
y las mapea a activos típicos para binarias (FX/Índices/Oro/Cripto).

Cómo usar
---------
1) Instala dependencias:
     pip install -r requirements.txt
2) (Opcional) Edita feeds.json para añadir/quitar fuentes RSS.
3) (Opcional) Crea config.json con tu token de Telegram y chat_id
   siguiendo el ejemplo en config_example.json, si quieres alertas push.
4) Ejecuta la app:
     streamlit run app.py

Notas
-----
- No da señales ni garantías. Sirve para monitorear noticias que
  pueden generar volatilidad, no como recomendación de inversión.
- Evita el scraping agresivo: usamos RSS públicos y respetamos límites.
- Si una fuente falla, el agregador la ignora sin romper la app.
- Timezone por defecto: America/Panama.

© 2025 — Uso educativo. No es asesoría financiera.
"""


import streamlit as st
import feedparser
import pandas as pd
import numpy as np
import re, hashlib, json, time
from datetime import datetime, timezone, timedelta
import pytz
import requests
from urllib.parse import urlparse
import plotly.express as px
from math import exp, log


# === Configuración base ===
APP_TZ = "America/Panama"
HALF_LIFE_HOURS = 6.0  # vida media del factor "recencia"
MAX_ITEMS_PER_FEED = 50
CACHE_TTL_MIN = 10     # minutos para refrescar feeds si hay autorefresh

# Pesos por tipo de fuente (puedes ajustar)
SOURCE_WEIGHTS = {
    "cnbc.com": 1.0,
    "marketwatch.com": 0.9,
    "wsj.com": 0.9,
    "ft.com": 0.9,
    "cnn.com": 0.7,
    "yahoo.com": 0.8,
    "coindesk.com": 0.8,
    "cointelegraph.com": 0.7,
    "bloomberglinea.com": 0.9,
    "eleconomista.es": 0.8,
    "expansion.com": 0.8,
    "elpais.com": 0.7,
    "prensa.com": 0.8,              # Panamá
    "anpanama.com": 0.7,            # Panamá (negocios)
    "laestrella.com.pa": 0.7,       # Panamá
    "google.com": 0.6,              # Google News (agregador)
}
DEFAULT_SOURCE_WEIGHT = 0.6

# Palabras clave de alto impacto (no exhaustivo). Clave -> peso
IMPACT_KEYWORDS = {
    # Macro EE.UU.
    "cpi": 1.0, "inflation": 1.0, "ppi": 0.9, "gdp": 0.9,
    "payrolls": 1.0, "jobs report": 1.0, "unemployment": 0.9,
    "fomc": 1.0, "fed": 1.0, "rate hike": 1.0, "rate cut": 1.0,
    "pce": 0.9, "retail sales": 0.8, "ism": 0.8, "pmi": 0.8,

    # Europa / LatAm (genérico)
    "ecb": 1.0, "bank of england": 0.9, "banxico": 0.8,
    "banrep": 0.8, "bcb": 0.8, "bcrp": 0.7,

    # Energía / Materias Primas
    "opec": 1.0, "production cut": 0.9, "supply": 0.7,
    "brent": 0.7, "wti": 0.7,

    # Acciones / Empresas
    "earnings": 1.0, "guidance": 1.0, "downgrade": 0.9, "upgrade": 0.9,
    "merger": 1.0, "acquisition": 1.0, "antitrust": 0.8, "lawsuit": 0.7,
    "dividend": 0.7, "buyback": 0.7,

    # Cripto
    "etf": 0.9, "sec": 0.8, "hack": 0.9, "halving": 0.7,
    "binance": 0.8, "coinbase": 0.8, "bitcoin": 0.8, "ethereum": 0.7,
}

# Mapeo básico de keywords -> activos (para binarias/volatilidad)
KEYWORD_TO_ASSETS = {
    # USD y macro USA
    "fed": ["USD", "US500", "XAUUSD", "US10Y"],
    "cpi": ["USD", "US500", "XAUUSD"],
    "inflation": ["USD", "US500", "XAUUSD"],
    "ppi": ["USD", "US500"],
    "gdp": ["USD", "US500"],
    "payrolls": ["USD", "US500", "XAUUSD"],
    "unemployment": ["USD", "US500"],
    "fomc": ["USD", "US500", "XAUUSD"],
    "rate hike": ["USD", "US500", "XAUUSD"],
    "rate cut": ["USD", "US500", "XAUUSD"],
    "pce": ["USD", "US500", "XAUUSD"],
    "retail sales": ["USD", "US500"],

    # Europa
    "ecb": ["EURUSD", "DE40", "EU50"],
    "bank of england": ["GBPUSD", "UK100"],

    # LatAm bancos centrales (aprox.)
    "banxico": ["USDMXN"],
    "banrep": ["USDCOP"],
    "bcb": ["USDBRL"],
    "bcrp": ["USD/PEN"],

    # Energía
    "opec": ["OIL", "USDCAD", "USDNOK"],
    "production cut": ["OIL"],
    "brent": ["OIL"],
    "wti": ["OIL"],

    # Acciones USA -> índices
    "earnings": ["US500", "US100"],
    "guidance": ["US500", "US100"],
    "downgrade": ["US500", "US100"],
    "upgrade": ["US500", "US100"],
    "merger": ["US500", "US100"],
    "acquisition": ["US500", "US100"],

    # Cripto
    "bitcoin": ["BTCUSD"],
    "ethereum": ["ETHUSD"],
    "etf": ["BTCUSD", "US500"],
    "sec": ["BTCUSD", "US500"],
    "hack": ["BTCUSD", "ETHUSD"],
    "binance": ["BTCUSD", "ETHUSD"],
    "coinbase": ["BTCUSD", "ETHUSD"],
}

# Pares y activos típicos en binarias (filtro rápido)
DEFAULT_WATCHLIST = ["EURUSD","GBPUSD","USDJPY","USDCHF","USDCAD","AUDUSD",
                     "XAUUSD","BTCUSD","ETHUSD","US500","DE40","OIL"]


def load_feeds():
    """Lee feeds.json o usa una lista por defecto."""
    try:
        with open("feeds.json","r",encoding="utf-8") as f:
            feeds = json.load(f)
            assert isinstance(feeds, list) and len(feeds)>0
            return feeds
    except Exception:
        return [
            # Inglés
            "https://www.cnbc.com/id/100003114/device/rss/rss.html",  # CNBC Markets
            "https://www.marketwatch.com/feeds/topstories",
            "https://feeds.a.dj.com/rss/RSSMarketsMain.xml",          # WSJ Markets
            "https://www.ft.com/markets?format=rss",
            "https://rss.cnn.com/rss/money_latest.rss",
            "https://www.coindesk.com/arc/outboundfeeds/rss/?outputType=xml",
            "https://cointelegraph.com/rss",

            # Español (general/finanzas)
            "https://www.eleconomista.es/rss/rss_economia.php",
            "https://e00-expansion.uecdn.es/rss/economia.xml",
            "https://feeds.elpais.com/mrp/rss/elpais/cincodias/portada",
            # Panamá (si fallan, edítalos en feeds.json)
            "https://www.prensa.com/arcio/rss/economia/",
            "https://www.anpanama.com/rss",   # si no funciona, edítalo
            "https://news.google.com/rss/search?q=mercados+OR+bolsa+OR+econom%C3%ADa&hl=es-419&gl=PA&ceid=PA:es-419",
        ]

def tz_now():
    return datetime.now(pytz.timezone(APP_TZ))

def to_dt(entry):
    # Intenta published_parsed, luego updated_parsed, sino ahora
    if hasattr(entry, "published_parsed") and entry.published_parsed:
        return datetime(*entry.published_parsed[:6], tzinfo=timezone.utc).astimezone(pytz.timezone(APP_TZ))
    if hasattr(entry, "updated_parsed") and entry.updated_parsed:
        return datetime(*entry.updated_parsed[:6], tzinfo=timezone.utc).astimezone(pytz.timezone(APP_TZ))
    return tz_now()

def domain_weight(link:str) -> float:
    try:
        netloc = urlparse(link).netloc.lower()
        # quitar subdominios
        parts = netloc.split(".")
        dom = ".".join(parts[-2:]) if len(parts)>=2 else netloc
        return SOURCE_WEIGHTS.get(dom, DEFAULT_SOURCE_WEIGHT)
    except Exception:
        return DEFAULT_SOURCE_WEIGHT

def recency_score(dt: datetime) -> float:
    hours = max((tz_now() - dt).total_seconds() / 3600.0, 0.0)
    lam = log(2) / HALF_LIFE_HOURS
    return exp(-lam * hours)

def detect_assets_and_impact(text: str):
    text_l = text.lower()
    impact = 0.0
    assets = set()
    for k, w in IMPACT_KEYWORDS.items():
        if k in text_l:
            impact += w
            assets.update(KEYWORD_TO_ASSETS.get(k, []))

    # Regex de tickers estilo $TSLA / $AAPL (aportan a índices)
    for m in re.findall(r"\$[A-Z]{1,5}", text):
        assets.add("US100")
        assets.add("US500")

    return sorted(list(assets)), impact

def hash_id(title:str, link:str) -> str:
    h = hashlib.sha256()
    h.update((title or "").encode("utf-8"))
    h.update((link or "").encode("utf-8"))
    return h.hexdigest()[:16]

def fetch_all(feeds, max_items=MAX_ITEMS_PER_FEED):
    rows = []
    for url in feeds:
        try:
            parsed = feedparser.parse(url)
            for e in parsed.entries[:max_items]:
                title = getattr(e, "title", "") or ""
                summary = getattr(e, "summary", "") or ""
                link = getattr(e, "link", "") or ""
                dt = to_dt(e)
                assets, impact = detect_assets_and_impact(f"{title} {summary}")
                source_w = domain_weight(link)
                rec = recency_score(dt)
                buzz = rec * (0.6 + 0.3*impact + 0.1*source_w)
                rows.append({
                    "id": hash_id(title, link),
                    "time": dt,
                    "time_ago_min": int(max((tz_now() - dt).total_seconds() / 60.0, 0)),
                    "title": title,
                    "summary": summary,
                    "link": link,
                    "assets": ", ".join(assets) if assets else "",
                    "impact": round(impact, 3),
                    "source_weight": round(source_w, 3),
                    "recency": round(rec, 3),
                    "buzz_score": round(buzz, 5),
                    "source": urlparse(link).netloc or urlparse(url).netloc,
                })
        except Exception as ex:
            # Continúa con el siguiente feed
            continue
    if not rows:
        return pd.DataFrame(columns=["id","time","time_ago_min","title","summary","link","assets","impact","source_weight","recency","buzz_score","source"])
    df = pd.DataFrame(rows).drop_duplicates(subset=["id"])
    return df.sort_values("buzz_score", ascending=False).reset_index(drop=True)

def aggregate_trends(df: pd.DataFrame, within_minutes: int = 360):
    """Cuenta frecuencia de activos/keywords en la ventana elegida"""
    if df.empty:
        return pd.DataFrame(columns=["asset","count","avg_buzz"])
    cutoff = tz_now() - timedelta(minutes=within_minutes)
    dff = df[df["time"] >= cutoff]
    if dff.empty:
        return pd.DataFrame(columns=["asset","count","avg_buzz"])

    assets_expanded = []
    for _, r in dff.iterrows():
        assets = [a.strip() for a in (r["assets"] or "").split(",") if a.strip()]
        if not assets:
            # intenta inferir sesgo general por keywords (opcional)
            continue
        for a in assets:
            assets_expanded.append((a, r["buzz_score"]))

    if not assets_expanded:
        return pd.DataFrame(columns=["asset","count","avg_buzz"])

    tmp = pd.DataFrame(assets_expanded, columns=["asset","buzz"])
    grp = tmp.groupby("asset").agg(count=("asset","count"), avg_buzz=("buzz","mean")).reset_index()
    return grp.sort_values(["count","avg_buzz"], ascending=[False, False]).reset_index(drop=True)

def send_telegram(token: str, chat_id: str, text: str) -> bool:
    try:
        url = f"https://api.telegram.org/bot{token}/sendMessage"
        r = requests.post(url, json={"chat_id": chat_id, "text": text, "disable_web_page_preview": True, "parse_mode":"HTML"}, timeout=10)
        return r.status_code == 200
    except Exception:
        return False


# ============== UI ==============
st.set_page_config(page_title="Radar de Noticias de Impacto", layout="wide")
st.title("📈 Radar de Noticias de Impacto")
st.caption("Agregador de noticias (RSS) + heurísticas de impacto para detectar temas que pueden generar volatilidad.")

with st.sidebar:
    st.header("⚙️ Configuración")

    refresh_min = st.slider("Autorefresh (min)", 0, 30, 5, help="0 desactiva el autorefresco.")
    window_min = st.select_slider("Ventana de análisis", options=[30,60,90,120,180,240,360,720,1440], value=240, help="Minutos hacia atrás para tendencias.")
    watchlist_txt = st.text_input("Watchlist (coma separada)", value=",".join(DEFAULT_WATCHLIST))
    min_buzz = st.slider("Umbral mínimo de Buzz", 0.0, 2.0, 0.3, 0.05)

    st.subheader("🔔 Alertas Telegram (opcional)")
    enable_alerts = st.checkbox("Habilitar alertas")
    tg_token = st.text_input("Bot Token", value="", type="password")
    tg_chat_id = st.text_input("Chat ID", value="")

    if st.button("Guardar config Telegram"):
        try:
            cfg = {"enable_alerts": enable_alerts, "tg_token": tg_token.strip(), "tg_chat_id": tg_chat_id.strip(), "min_buzz": float(min_buzz)}
            with open("config.json","w",encoding="utf-8") as f:
                json.dump(cfg, f, ensure_ascii=False, indent=2)
            st.success("Config guardada en config.json")
        except Exception as ex:
            st.error(f"No se pudo guardar: {ex}")

feeds = load_feeds()
st.write(f"Fuentes activas: {len(feeds)}")
if st.button("Actualizar ahora"):
    st.session_state["last_fetch"] = 0  # fuerza refresco abajo

# Control de autorefresco básico
now_ts = time.time()
last_fetch = st.session_state.get("last_fetch", 0)
need_refresh = (now_ts - last_fetch) > (CACHE_TTL_MIN * 60)
if refresh_min > 0:
    st.autorefresh(interval=refresh_min*60*1000, key="autoref")

if (last_fetch == 0) or need_refresh:
    df = fetch_all(feeds)
    st.session_state["df"] = df
    st.session_state["last_fetch"] = now_ts
else:
    df = st.session_state.get("df", fetch_all(feeds))

if df.empty:
    st.warning("Sin datos por ahora. Revisa feeds.json o tu conexión.")
    st.stop()

# Filtro por watchlist
wl = [w.strip().upper() for w in watchlist_txt.split(",") if w.strip()]
if wl:
    mask = df["assets"].apply(lambda s: any(w in s for w in wl))
    df_w = df[mask].copy()
else:
    df_w = df.copy()

# Filtro por umbral mínimo
df_w = df_w[df_w["buzz_score"] >= min_buzz]

# Mostrar tendencias
trends = aggregate_trends(df_w, within_minutes=int(window_min))
colA, colB = st.columns([1.2, 2.0], gap="large")

with colA:
    st.subheader("📊 Tendencias por Activo")
    if not trends.empty:
        fig = px.bar(trends.head(15), x="asset", y="count", hover_data=["avg_buzz"], title="Menciones (última ventana)")
        st.plotly_chart(fig, use_container_width=True)
    else:
        st.info("Sin tendencias en la ventana seleccionada.")

    st.subheader("🧪 Top Historias (tabla)")
    st.dataframe(df_w[["time","time_ago_min","source","buzz_score","assets","impact","title"]].head(50), use_container_width=True, hide_index=True)

    csv = df_w.to_csv(index=False).encode("utf-8")
    st.download_button("⬇️ Exportar CSV", csv, file_name="noticias_impacto.csv", mime="text/csv")

with colB:
    st.subheader("📰 Historias Destacadas")
    topN = st.slider("Cuántas historias mostrar", 5, 50, 15, 5)
    for _, r in df_w.head(topN).iterrows():
        with st.container(border=True):
            st.markdown(f"**[{r['title']}]({r['link']})**")
            st.caption(f"{r['source']} • hace {r['time_ago_min']} min • Buzz={r['buzz_score']} • Impacto={r['impact']} • Activos: {r['assets'] or '—'}")
            if r["summary"]:
                st.write(r["summary"][:400] + ("..." if len(r["summary"])>400 else ""))

# Alertas Telegram si procede
try:
    with open("config.json","r",encoding="utf-8") as f:
        cfg = json.load(f)
except Exception:
    cfg = {"enable_alerts": False}

if cfg.get("enable_alerts") and cfg.get("tg_token") and cfg.get("tg_chat_id"):
    # envía alertas de los top 5 con mayor buzz por encima del umbral
    to_alert = df_w.head(5)
    sent = 0
    for _, r in to_alert.iterrows():
        msg = f"🚨 <b>Noticia Impacto</b>\n<b>{r['title']}</b>\nFuente: {r['source']}\nHace: {r['time_ago_min']} min\nBuzz: {r['buzz_score']}\nActivos: {r['assets'] or '—'}\n{r['link']}"
        ok = send_telegram(cfg["tg_token"], cfg["tg_chat_id"], msg)
        if ok: sent += 1
    if sent:
        st.success(f"Alertas enviadas: {sent}")


st.divider()
st.caption("Este panel prioriza recencia + impacto por palabras clave + reputación de fuente. Ajusta 'feeds.json' y los pesos para tu operativa.")
