"""
Piki Weekly Business Intelligence Dashboard
============================================
Architecture:
  1. Global Filters (sidebar: city, business, date range, time period)
  2. Shared data prep — one pass, all sections reuse filtered df
  3. Four tab sections selectable via pills/tabs:
       📈 Weekly Trends    — orders, sales, KPI, failed & rejected orders
       ⏰ Delivery Times   — stage breakdown, hourly, city charts, heatmap
       🚴 Rider Attendance — attendance pivot, deficiency alerts
       📦 Products         — product mix, business rankings, geo area tool
  4. Every section has AI Insight + Q&A chat
"""

import streamlit as st
import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
from matplotlib.backends.backend_pdf import PdfPages
from matplotlib.ticker import FuncFormatter
from io import BytesIO
from math import radians, sin, cos, sqrt, atan2
import numpy as np
from datetime import datetime, timedelta
import io
import re
from collections import defaultdict
from rapidfuzz import fuzz, process
import folium
from folium.plugins import HeatMap, Draw
from streamlit_folium import st_folium
from shapely.geometry import Point, Polygon
import anthropic
import os

# ─────────────────────────────────────────────────
# CONFIG
# ─────────────────────────────────────────────────
st.set_page_config(
    page_title="Piki BI Dashboard",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Custom CSS for clean look
st.markdown("""
<style>
    .metric-card {
        background: #f8f9fa; border-radius: 10px;
        padding: 16px; text-align: center; border-left: 4px solid #1f77b4;
    }
    .metric-value { font-size: 28px; font-weight: 700; color: #1f77b4; }
    .metric-label { font-size: 13px; color: #666; margin-top: 4px; }
    .section-header {
        background: linear-gradient(90deg, #1f77b4 0%, #0d5fa3 100%);
        color: white; padding: 10px 18px; border-radius: 8px;
        font-size: 16px; font-weight: 600; margin-bottom: 16px;
    }
    .kpi-ok  { color: #28a745; font-weight: 700; }
    .kpi-bad { color: #dc3545; font-weight: 700; }
    div[data-testid="stTabs"] button { font-size: 15px; font-weight: 600; }
</style>
""", unsafe_allow_html=True)

# ─────────────────────────────────────────────────
# CONSTANTS
# ─────────────────────────────────────────────────
FAILED_KPI       = 10          # max failed orders / week
GROWTH_RATE      = 0.012       # 1.2% weekly KPI
KPI_START_YEAR   = 2026
TARGET_RIDERS    = pd.DataFrame({
    'Business City':        ['Masaki','City Centre','Mlimani','Mikocheni','Mbezi',
                             'Kigamboni','Kinondoni','Arusha','Dodoma','Zanzibar','Mwanza'],
    'Weekday Active Riders':[40, 35, 9, 10, 8, 1, 3, 8, 3, 2, 2],
    'Weekend Active Riders':[50, 40, 10, 13, 10, 1, 4, 10, 4, 3, 3]
})
REGIONAL_CITIES  = ['Arusha','Dodoma','Mwanza','Zanzibar']
DAR_CITIES       = ['Mlimani','Mbezi','Masaki','Mikocheni','City Centre','Kinondoni']
OPERATING_HOURS  = list(range(7, 24)) + [0, 1, 2]
DAY_NAMES        = ['Monday','Tuesday','Wednesday','Thursday','Friday','Saturday','Sunday']

PRODUCT_MAPPING  = {
    'chapatti':'chapati','chapati - per piece':'chapati',
    'chickenshawarma':'chicken shawarma','tradional wings':'traditional wings',
    'burger':'beef burger','1 pc chicken':'chicken piece (1)','1pc chicken':'chicken piece (1)',
    'plain chips':'regular chips','chips':'regular chips','fries':'regular chips',
    'french fries':'regular chips','french fries - regular':'regular chips',
    'chips (salted crisps)':'regular chips','chips kavu':'regular chips',
    'reg coleslaw':'coleslaw','regular coleslaw':'coleslaw',
    'soda':'soft drinks','soda - 600ml':'soft drinks (600ml)','coke':'coca cola',
    '600ml coke':'coke - 600ml','1.25ltr coke':'coke - 1.25l',
    'dasani water still - 500ml':'water - 500ml','dew drop - 600ml (12 pack)':'water - 600ml',
}

# ─────────────────────────────────────────────────
# HELPERS — pure functions, no Streamlit calls
# ─────────────────────────────────────────────────
def millions(x, pos):
    return f'{x/1_000_000:.1f}M'

fmt_millions = FuncFormatter(millions)

def haversine(lat1, lon1, lat2, lon2):
    R = 6371.0
    lat1, lon1, lat2, lon2 = map(radians, [lat1, lon1, lat2, lon2])
    a = sin((lat2-lat1)/2)**2 + cos(lat1)*cos(lat2)*sin((lon2-lon1)/2)**2
    return R * 2 * atan2(sqrt(a), sqrt(1-a))

def extract_products(text):
    results = []
    for qty, name in re.findall(r"(\d+)\s*x\s*([^:\n\r]+)", str(text)):
        results.append((name.lower().strip(), int(qty)))
    return results

def standardize_product(name):
    if name in PRODUCT_MAPPING:
        return PRODUCT_MAPPING[name]
    m = process.extractOne(name, PRODUCT_MAPPING.keys(), scorer=fuzz.token_sort_ratio)
    return PRODUCT_MAPPING[m[0]] if m and m[1] >= 80 else name

def compute_delivery_stages(df):
    """Add all delivery stage columns to df (in-place-safe via copy)."""
    df = df.copy()
    for col in ['DELIVERY TIME','ACCEPTED BUSINESS HOUR','ASSIGNED HOUR',
                'ACCEPTED DRIVER HOUR','IN BUSINESS HOUR','PICKUP HOUR','DELIVERY HOUR']:
        if col in df.columns:
            df[col] = pd.to_datetime(df[col], errors='coerce')

    def stage(a, b, default):
        s = (df[b] - df[a]).dt.total_seconds() / 60
        return s.mask(s < 0, default)

    df['Accepted by Business'] = stage('DELIVERY TIME',        'ACCEPTED BUSINESS HOUR', 0).clip(lower=0)
    df['Assigned Time']        = stage('ACCEPTED BUSINESS HOUR','ASSIGNED HOUR',          3)
    df['Accepted by Driver']   = stage('ASSIGNED HOUR',         'ACCEPTED DRIVER HOUR',   3)
    df['Driver to Business']   = stage('ACCEPTED DRIVER HOUR',  'IN BUSINESS HOUR',       7)
    df['Driver in Business']   = stage('IN BUSINESS HOUR',      'PICKUP HOUR',           15)
    df['Pickup to Customer']   = stage('PICKUP HOUR',           'DELIVERY HOUR',         15)

    adt = (df['DELIVERY HOUR'] - df['DELIVERY TIME']).dt.total_seconds() / 60
    adt2 = (df['DELIVERY HOUR'] - df['ACCEPTED BUSINESS HOUR']).dt.total_seconds() / 60
    df['Average Delivery Time'] = adt.mask(adt < 0, adt2).mask(adt2 < 0, 40)
    return df

def categorize_delay(row):
    if row.get('Average Delivery Time', 0) <= 100:
        return ""
    issues = []
    checks = [
        ('Accepted by Business', 30), ('Assigned Time', 30),
        ('Accepted by Driver', 30),   ('Driver to Business', 30),
        ('Driver in Business', 60),   ('Pickup to Customer', 45),
    ]
    for col, limit in checks:
        v = row.get(col, 0)
        if v < 0 or v > limit:
            issues.append(f"{col} Delay")
    return ", ".join(issues) if issues else "Unclassified Delay"

def week_label(period_or_date):
    """Return readable week label from a Period or datetime."""
    try:
        p = pd.Period(period_or_date, freq='W')
        return f"W{p.week} ({p.start_time.strftime('%d %b')})"
    except Exception:
        return str(period_or_date)

def apply_growth_kpi(weekly):
    weekly = weekly.copy()
    weekly['Year'] = weekly['Week'].dt.year
    base = weekly[weekly['Year'] == KPI_START_YEAR].head(1)
    if base.empty:
        weekly['Growth KPI Orders'] = None
        return weekly
    idx = base.index[0]
    weekly['Growth KPI Orders'] = None
    weekly.loc[idx, 'Growth KPI Orders'] = base['Total_Orders'].values[0]
    for i in range(idx+1, len(weekly)):
        weekly.loc[i, 'Growth KPI Orders'] = weekly.loc[i-1, 'Growth KPI Orders'] * (1 + GROWTH_RATE)
    return weekly

def add_distance(df):
    if not all(c in df.columns for c in ['CUSTOMER LATITUDE','CUSTOMER LONGITUDE',
                                          'BUSINESS LATITUDE','BUSINESS LONGITUDE']):
        return df
    df = df.copy()
    df['DISTANCE (km)'] = df.apply(
        lambda r: haversine(r['CUSTOMER LATITUDE'],r['CUSTOMER LONGITUDE'],
                            r['BUSINESS LATITUDE'],r['BUSINESS LONGITUDE']), axis=1)
    bins   = [0, 2, 3, 4, 5, 7, float('inf')]
    labels = ['0-2 km','2-3 km','3-4 km','4-5 km','5-7 km','7+ km']
    df['Distance Category'] = pd.cut(df['DISTANCE (km)'], bins=bins, labels=labels)
    return df

def excel_bytes(df, sheet='Sheet1'):
    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine='xlsxwriter') as w:
        df.to_excel(w, index=False, sheet_name=sheet)
    buf.seek(0)
    return buf.read()

def format_products_clean(products_text):
    extracted = extract_products(str(products_text))
    if not extracted:
        return ""
    return ", ".join(f"{qty} x {name.title()}" for name, qty in extracted)

# ─────────────────────────────────────────────────
# CLAUDE AI HELPERS
# ─────────────────────────────────────────────────
def claude_insight(prompt: str, max_tokens: int = 700) -> str:
    try:
        key = os.getenv("CLAUDE_API_KEY")
        if not key:
            return "⚠️ Set CLAUDE_API_KEY environment variable to enable AI insights."
        client = anthropic.Anthropic(api_key=key)
        r = client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=max_tokens,
            messages=[{"role": "user", "content": prompt}]
        )
        return r.content[0].text
    except Exception as e:
        return f"⚠️ AI insight unavailable: {e}"

def claude_chat_answer(context: str, history: list, question: str) -> str:
    try:
        key = os.getenv("CLAUDE_API_KEY")
        if not key:
            return "⚠️ Set CLAUDE_API_KEY environment variable."
        client = anthropic.Anthropic(api_key=key)
        system = f"""You are a senior BI analyst for a food delivery company in Tanzania.
Answer questions about the dashboard section using this data context:
{context}
Be concise, specific, and use real numbers. If data doesn't support an answer, say so."""
        r = client.messages.create(
            model="claude-sonnet-4-6", max_tokens=600,
            system=system,
            messages=history + [{"role": "user", "content": question}]
        )
        return r.content[0].text
    except Exception as e:
        return f"⚠️ Could not get answer: {e}"

def ai_block(section_key: str, context: str, insight_text: str):
    """Renders insight expander + Q&A chat for any section."""
    with st.expander("🤖 AI Insight", expanded=True):
        st.markdown(insight_text)

    with st.expander("💬 Follow-up Questions", expanded=False):
        hkey = f"chat_{section_key}"
        if hkey not in st.session_state:
            st.session_state[hkey] = []
        for m in st.session_state[hkey]:
            st.chat_message(m["role"]).markdown(m["content"])
        q = st.chat_input("Ask anything about this section…", key=f"inp_{section_key}")
        if q:
            st.chat_message("user").markdown(q)
            with st.spinner("Thinking…"):
                ans = claude_chat_answer(context, st.session_state[hkey], q)
            st.chat_message("assistant").markdown(ans)
            st.session_state[hkey] += [{"role":"user","content":q},
                                        {"role":"assistant","content":ans}]
        if st.session_state[hkey]:
            if st.button("🗑️ Clear chat", key=f"clr_{section_key}"):
                st.session_state[hkey] = []
                st.rerun()

# ─────────────────────────────────────────────────
# INSIGHT BUILDERS — return (text, context)
# ─────────────────────────────────────────────────
def build_trend_insight(weekly, full_df):
    ws = weekly[['Week_Label','Total_Orders','Growth KPI Orders','Total_Sales']].to_string(index=False)
    wow = ""
    prev_lbl = None
    if len(weekly) >= 2:
        l, p = weekly.iloc[-1], weekly.iloc[-2]
        do = l['Total_Orders'] - p['Total_Orders']
        ds = l['Total_Sales']  - p['Total_Sales']
        prev_lbl  = p['Week_Label']
        wow = (f"WoW Orders: {do:+.0f} ({do/p['Total_Orders']*100:+.1f}%)\n"
               f"WoW Sales: {ds:+,.0f} TZS ({ds/p['Total_Sales']*100:+.1f}%)")

    contrib = ""
    if prev_lbl and 'BUSINESS NAME' in full_df.columns:
        _df = full_df.copy()
        _df['wl'] = (_df['DELIVERY DATE'].dt.isocalendar().year.astype(str)
                     + "-W" + _df['DELIVERY DATE'].dt.isocalendar().week.astype(str).str.zfill(2))
        lbl = weekly.iloc[-1]['Week_Label']
        lb = _df[_df['wl']==lbl].groupby('BUSINESS NAME').size().reset_index(name='Latest')
        pb = _df[_df['wl']==prev_lbl].groupby('BUSINESS NAME').size().reset_index(name='Prev')
        bz = pd.merge(lb, pb, on='BUSINESS NAME', how='outer').fillna(0)
        bz['Δ'] = bz['Latest'] - bz['Prev']
        bz = bz.sort_values('Δ', ascending=False)
        contrib = (f"\nTop Growers:\n{bz.head(5).to_string(index=False)}"
                   f"\nTop Decliners:\n{bz.tail(5).to_string(index=False)}")

    context = f"WEEKLY TREND:\n{ws}\n\nWEEK-OVER-WEEK:\n{wow}{contrib}"
    prompt = f"""Senior BI analyst for a Tanzanian food delivery company.
{context}
Provide:
1. **Trend Direction** – Growing, flat or declining? Key turning points.
2. **KPI Performance** – Which weeks beat/miss the 1.2% growth KPI?
3. **WoW Deep Dive** – Top business drivers of change this week.
4. **Sales vs Orders** – Is average order value shifting?
5. **Actions** – 2 specific, prioritized actions for this week.
Use real numbers. Be concise."""
    return claude_insight(prompt, 900), context


def build_failed_insight(failed_weekly, pivot_df=None, week_label_str=None):
    ws = failed_weekly[['Week_Label','Failed Orders']].to_string(index=False)
    context = f"FAILED ORDERS TREND (KPI≤{FAILED_KPI}/week):\n{ws}"
    if pivot_df is not None:
        context += f"\n\nWEEKLY BREAKDOWN — {week_label_str}:\n{pivot_df.to_string()}"
    prompt = f"""Senior operations analyst for a Tanzanian food delivery company.
{context}
Provide:
1. **Trend** – Improving, worsening or stable?
2. **KPI Breaches** – Which weeks & by how much?
3. **City / Day Patterns** – Where do failures concentrate?
4. **Root Cause Hypotheses** – What operational factors likely cause these?
5. **Actions** – 3 specific fixes for the highest-risk areas.
Use real numbers."""
    return claude_insight(prompt, 750), context


def build_delivery_insight(stage_df, city):
    summary = stage_df[['BUSINESS CITY','Average Delivery Time','Driver in Business',
                         'Pickup to Customer','Accepted by Business']].head(30).to_string(index=False)
    context = f"DELIVERY STAGE DATA — {city}:\n{summary}"
    prompt = f"""Senior BI analyst for a Tanzanian food delivery company.
{context}
Provide:
1. **Overall Speed** – Is avg delivery time acceptable (<45 min target)?
2. **Bottleneck Stage** – Which stage contributes most to delays?
3. **City Comparison** – Best vs worst performing areas.
4. **Vendor Prep Risk** – Is Driver-in-Business time too high?
5. **Actions** – 2 specific fixes for the biggest delay source.
Use real numbers."""
    return claude_insight(prompt, 700), context


def build_attendance_insight(pivot_df, week_sel, df_week):
    deficiency_cities = pivot_df[pivot_df['Avg Deficiency'] > 0][
        ['WORKING ZONE','Avg Deficiency','Status']].to_string(index=False)
    ok_cities = pivot_df[pivot_df['Avg Deficiency'] == 0]['WORKING ZONE'].tolist()
    total_drivers = df_week['DRIVER NAME'].nunique() if not df_week.empty else 0
    context = (f"DRIVER ATTENDANCE — Week {week_sel}\n"
               f"Total unique drivers active: {total_drivers}\n"
               f"Cities with deficiency:\n{deficiency_cities}\n"
               f"Cities at target: {', '.join(ok_cities)}")
    prompt = f"""Senior operations analyst for a Tanzanian food delivery company.
{context}
Provide:
1. **Attendance Summary** – How many cities are understaffed vs sufficient?
2. **Highest Risk Zones** – Which areas need urgent rider recruitment?
3. **Day Patterns** – Are deficiencies on weekdays, weekends or both?
4. **Impact on Delivery** – Link understaffing to potential delivery delays.
5. **Actions** – Specific staffing recommendations per city.
Use real numbers."""
    return claude_insight(prompt, 700), context


def build_product_insight(total_df, biz_df, weekly_prod_df):
    top10 = total_df.head(10).to_string(index=False)
    top_biz = biz_df.head(10).to_string(index=False)
    total_qty = int(total_df['Total Quantity'].sum())
    top3_share = round(total_df.head(3)['Total Quantity'].sum() / total_qty * 100, 1) if total_qty else 0
    context = (f"PRODUCT MIX — Total items sold: {total_qty:,}\n"
               f"Top-3 share: {top3_share}% of volume\n\n"
               f"Top 10 Products:\n{top10}\n\n"
               f"Top 10 Businesses:\n{top_biz}")
    prompt = f"""Senior BI analyst for a Tanzanian food delivery company.
{context}
Provide:
1. **Best Sellers** – What dominates and what does it reveal about customer preferences?
2. **Concentration Risk** – Over-reliance on few products or businesses?
3. **Business Performance** – Revenue vs volume outliers in top businesses.
4. **Menu Opportunity** – Underperforming categories worth promoting.
5. **Actions** – One for the product team, one for the commercial team.
Use real numbers. Be concise."""
    return claude_insight(prompt, 750), context


# ─────────────────────────────────────────────────
# SIDEBAR — Upload & Global Filters
# ─────────────────────────────────────────────────
with st.sidebar:
    st.image("https://via.placeholder.com/250x80.png?text=Piki+BI", use_column_width=True)
    st.title("📊 Piki Dashboard")
    st.divider()

    # ── Auto-load CSV from repo ──
    DATA_FILE = "February Week 3.csv"
    DATA_RELOAD_KEY = "raw_df_loaded_file"

    # Allow optional manual override upload (for testing)
    with st.expander("📤 Override with a different file (optional)", expanded=False):
        uploaded = st.file_uploader("Upload CSV or Excel", type=["csv","xlsx"])
        if uploaded:
            raw = (pd.read_csv(uploaded) if uploaded.name.endswith(".csv")
                   else pd.read_excel(uploaded))
            raw['DELIVERY DATE'] = pd.to_datetime(raw['DELIVERY DATE'], errors='coerce')
            raw['DELIVERY TIME'] = pd.to_datetime(raw['DELIVERY TIME'], errors='coerce')
            st.session_state.raw_df = raw
            st.session_state[DATA_RELOAD_KEY] = "manual_upload"
            st.success(f"✅ Manual upload: {len(raw):,} rows")

    if "raw_df" not in st.session_state or st.session_state.get(DATA_RELOAD_KEY) != DATA_FILE:
        try:
            raw = pd.read_csv(DATA_FILE)
            raw['DELIVERY DATE'] = pd.to_datetime(raw['DELIVERY DATE'], errors='coerce')
            raw['DELIVERY TIME'] = pd.to_datetime(raw['DELIVERY TIME'], errors='coerce')
            st.session_state.raw_df = raw
            st.session_state[DATA_RELOAD_KEY] = DATA_FILE
            st.success(f"✅ Auto-loaded: {DATA_FILE} ({len(raw):,} rows)")
        except FileNotFoundError:
            st.error(f"❌ Data file '{DATA_FILE}' not found. Make sure it exists in the app folder.")
            st.info("Or use the file uploader above to load data manually.")
            st.stop()
        except Exception as e:
            st.error(f"❌ Error loading data: {e}")
            st.stop()

    raw = st.session_state.raw_df

    st.divider()
    st.subheader("🔍 Global Filters")

    # ── Date range — default latest week ──
    max_date = raw['DELIVERY DATE'].max()
    min_date = raw['DELIVERY DATE'].min()
    latest_mon = (max_date - pd.Timedelta(days=max_date.weekday())).date()
    latest_sun = (latest_mon + pd.Timedelta(days=6))

    date_range = st.date_input(
        "Date Range",
        value=[latest_mon, latest_sun],
        min_value=min_date.date(),
        max_value=max_date.date(),
        help="Defaults to latest week. Expand to view historical data."
    )

    cities = sorted(raw['BUSINESS CITY'].dropna().unique())
    city_sel = st.multiselect("Business City", cities, placeholder="All cities")

    businesses = sorted(raw['BUSINESS NAME'].dropna().unique())
    biz_sel = st.multiselect("Business Name", businesses, placeholder="All businesses")

    hour_opt = st.selectbox("Time Period",
        ["All Day","Morning (7–11)","Afternoon (12–16)","Evening (17–22)",
         "Late Night (23–2)","Custom"])
    custom_hours = []
    if hour_opt == "Custom":
        custom_hours = st.multiselect("Hours", OPERATING_HOURS)

    st.divider()
    st.caption(f"Data spans {min_date.date()} → {max_date.date()}")

# ─────────────────────────────────────────────────
# APPLY GLOBAL FILTERS → produce `df`
# ─────────────────────────────────────────────────
df = raw.copy()

if len(date_range) == 2:
    df = df[(df['DELIVERY DATE'] >= pd.to_datetime(date_range[0])) &
            (df['DELIVERY DATE'] <= pd.to_datetime(date_range[1]))]
if city_sel:
    df = df[df['BUSINESS CITY'].isin(city_sel)]
if biz_sel:
    df = df[df['BUSINESS NAME'].isin(biz_sel)]

df['HOUR'] = df['DELIVERY TIME'].dt.hour
df = df[df['HOUR'].isin(OPERATING_HOURS)]

if hour_opt == "Morning (7–11)":
    df = df[df['HOUR'].between(7, 11)]
elif hour_opt == "Afternoon (12–16)":
    df = df[df['HOUR'].between(12, 16)]
elif hour_opt == "Evening (17–22)":
    df = df[df['HOUR'].between(17, 22)]
elif hour_opt == "Late Night (23–2)":
    df = df[(df['HOUR'] >= 23) | (df['HOUR'] <= 2)]
elif hour_opt == "Custom" and custom_hours:
    df = df[df['HOUR'].isin(custom_hours)]

# ─────────────────────────────────────────────────
# HEADER
# ─────────────────────────────────────────────────
st.title("📊 Piki Weekly Business Intelligence")

city_label = ", ".join(city_sel) if city_sel else "All Cities"
biz_label  = f"{len(biz_sel)} businesses" if biz_sel else "All Businesses"
st.markdown(
    f"**Active filters:** 📅 `{date_range[0]} → {date_range[1]}` &nbsp;|&nbsp; "
    f"🏙️ `{city_label}` &nbsp;|&nbsp; 🏪 `{biz_label}` &nbsp;|&nbsp; ⏰ `{hour_opt}`"
)

if df.empty:
    st.error("No data matches the current filters. Adjust the filters in the sidebar.")
    st.stop()

# ── Quick KPI bar ──
col1, col2, col3, col4, col5 = st.columns(5)
total_orders  = len(df)
total_sales   = df['SUBTOTAL'].sum() if 'SUBTOTAL' in df.columns else 0
total_failed  = len(df[df['STATE'] == 'Delivery Failed By Driver']) if 'STATE' in df.columns else 0
unique_biz    = df['BUSINESS NAME'].nunique()
unique_drivers = df['DRIVER NAME'].nunique() if 'DRIVER NAME' in df.columns else 0

col1.metric("📦 Total Orders",  f"{total_orders:,}")
col2.metric("💰 Total Sales",   f"{total_sales/1_000_000:.1f}M TZS")
col3.metric("❌ Failed Orders", f"{total_failed}")
col4.metric("🏪 Active Businesses", f"{unique_biz}")
col5.metric("🚴 Active Riders", f"{unique_drivers}")

st.divider()

# ─────────────────────────────────────────────────
# MAIN TABS
# ─────────────────────────────────────────────────
tab1, tab2, tab3, tab4, tab5 = st.tabs([
    "📈 Weekly Trends",
    "⏰ Delivery Times",
    "🚴 Rider Attendance",
    "📦 Products & Geo",
    "🎉 Piki Party Store",
])

# ═══════════════════════════════════════════════════════════════
# TAB 1 — WEEKLY TRENDS
# ═══════════════════════════════════════════════════════════════
with tab1:
    st.markdown('<div class="section-header">📈 Orders & Sales KPI Trend</div>', unsafe_allow_html=True)

    # ── Weekly aggregation ──
    weekly = (
        df.groupby(df['DELIVERY DATE'].dt.to_period('W-SUN'))
        .agg(Total_Orders=('ID','count'), Total_Sales=('SUBTOTAL','sum'))
        .reset_index()
    )
    weekly['Week']       = weekly['DELIVERY DATE'].dt.start_time
    weekly['Week_Label'] = weekly['DELIVERY DATE'].apply(
        lambda p: f"W{p.week} ({p.start_time.strftime('%d %b')})"
    )
    weekly = apply_growth_kpi(weekly)

    # ── Chart ──
    fig, ax1 = plt.subplots(figsize=(13, 5))
    ax1.plot(weekly['Week_Label'], weekly['Total_Orders'],
             color='#1f77b4', marker='o', lw=2, label='Total Orders')
    if 'Growth KPI Orders' in weekly.columns:
        ax1.plot(weekly['Week_Label'], weekly['Growth KPI Orders'],
                 color='green', lw=2, linestyle='--', label='1.2% Growth KPI')
    ax1.set_ylabel("Orders"); ax1.grid(True, alpha=0.3)
    ax2 = ax1.twinx()
    ax2.bar(weekly['Week_Label'], weekly['Total_Sales'],
            alpha=0.25, color='#ff7f0e', label='Sales (TZS)')
    ax2.set_ylabel("Sales (TZS)"); ax2.yaxis.set_major_formatter(fmt_millions)
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax1.legend(lines1+lines2, labels1+labels2, loc='upper left', fontsize=9)
    plt.title("Weekly Orders vs Sales vs KPI"); plt.xticks(rotation=30, ha='right')
    plt.tight_layout(); st.pyplot(fig); plt.close()

    st.dataframe(
        weekly[['Week_Label','Total_Orders','Growth KPI Orders','Total_Sales']].rename(
            columns={'Week_Label':'Week','Total_Orders':'Orders',
                     'Growth KPI Orders':'KPI Target','Total_Sales':'Sales (TZS)'}
        ), use_container_width=True
    )

    # AI
    with st.spinner("Generating trend insight…"):
        ins1, ctx1 = build_trend_insight(weekly, df)
    ai_block("trend_orders", ctx1, ins1)

    st.divider()

    # ── Predictive Forecast — Claude AI ──
    st.markdown('<div class="section-header">🔮 AI Predictive Forecast (Next 4 Weeks)</div>', unsafe_allow_html=True)

    if len(weekly) >= 4:
        _wr = weekly.copy().reset_index(drop=True)
        _wr['g'] = _wr['Total_Orders'].pct_change()
        avg_g  = _wr['g'].tail(3).mean()
        last_o = int(_wr.iloc[-1]['Total_Orders'])
        last_k = _wr.iloc[-1]['Growth KPI Orders']
        last_w = _wr.iloc[-1]['Week']

        # Build numeric forecast for chart
        preds, po, pk = [], last_o, last_k
        for i in range(1, 5):
            po = po * (1 + avg_g); pk = pk * (1 + GROWTH_RATE)
            preds.append({"Week_Label": f"Forecast W+{i}",
                          "Predicted Orders": int(po), "KPI Target": int(pk),
                          "Week": last_w + pd.Timedelta(days=7*i)})
        fcast = pd.DataFrame(preds)

        risk = ("🔴 HIGH RISK – Declining" if avg_g < 0
                else "🟡 MODERATE – Below KPI" if avg_g < GROWTH_RATE
                else "🟢 STABLE GROWTH")

        # Chart: actual + forecast
        fig2, ax2 = plt.subplots(figsize=(13, 5))
        ax2.plot(weekly['Week_Label'], weekly['Total_Orders'],
                 marker='o', color='#1f77b4', lw=2, label='Actual Orders')
        if 'Growth KPI Orders' in weekly.columns:
            ax2.plot(weekly['Week_Label'], weekly['Growth KPI Orders'],
                     linestyle='--', color='green', lw=1.5, label='KPI Trajectory')
        ax2.plot(fcast['Week_Label'], fcast['Predicted Orders'],
                 marker='o', linestyle='--', color='purple', lw=2, label='AI Predicted')
        ax2.plot(fcast['Week_Label'], fcast['KPI Target'],
                 linestyle=':', color='orange', lw=1.5, label='Future KPI Target')
        ax2.axvline(x=len(weekly)-0.5, color='gray', linestyle=':', alpha=0.4)
        ax2.set_xlabel("Week"); ax2.set_ylabel("Orders")
        ax2.legend(); ax2.grid(True, alpha=0.3)
        plt.title("AI Forecast: Actual vs KPI vs Predicted")
        plt.xticks(rotation=30, ha='right'); plt.tight_layout()
        st.pyplot(fig2); plt.close()

        st.dataframe(fcast[['Week_Label','Predicted Orders','KPI Target']],
                     use_container_width=True)

        # Claude AI forecast analysis
        hist_str  = weekly[['Week_Label','Total_Orders']].to_string(index=False)
        fcast_str = fcast[['Week_Label','Predicted Orders','KPI Target']].to_string(index=False)
        _avg_g_pct = round(avg_g * 100, 2)
        _forecast_prompt = (
            "You are a senior BI analyst for a Tanzanian food delivery company.\n\n"
            "HISTORICAL WEEKLY ORDERS:\n" + hist_str + "\n\n"
            "STATISTICAL FORECAST (next 4 weeks, avg 3-week growth = " + str(_avg_g_pct) + "%):\n"
            + fcast_str + "\n\nRisk level: " + risk + "\nKPI target: 1.2% weekly growth\n\n"
            "Provide a forward-looking AI forecast analysis:\n"
            "1. **Growth Trajectory** - Is the forecast realistic given the trend?\n"
            "2. **Risk Assessment** - What could cause actual orders to fall below forecast?\n"
            "3. **Upside Scenarios** - What operational changes could beat the forecast?\n"
            "4. **KPI Gap Analysis** - Will the business likely meet 1.2% growth KPI?\n"
            "5. **Strategic Actions** - 2-3 specific steps to take NOW for the next 4 weeks.\n\n"
            "Be specific, use real numbers, write as a strategic advisor."
        )

        with st.expander("🤖 AI Forecast Analysis", expanded=True):
            with st.spinner("Claude is analyzing the forecast…"):
                _fc_insight = claude_insight(_forecast_prompt, max_tokens=900)
            st.markdown(_fc_insight)

        _fc_ctx = "FORECAST:\n" + fcast_str + "\n\nHISTORY:\n" + hist_str + "\nRisk: " + risk
        with st.expander("💬 Ask about the Forecast", expanded=False):
            _fh = "chat_forecast"
            if _fh not in st.session_state:
                st.session_state[_fh] = []
            for _m in st.session_state[_fh]:
                st.chat_message(_m["role"]).markdown(_m["content"])
            _q = st.chat_input("e.g. What would need to happen to hit KPI?", key="inp_forecast")
            if _q:
                st.chat_message("user").markdown(_q)
                with st.spinner("Thinking…"):
                    _ans = claude_chat_answer(_fc_ctx, st.session_state[_fh], _q)
                st.chat_message("assistant").markdown(_ans)
                st.session_state[_fh] += [{"role":"user","content":_q},
                                           {"role":"assistant","content":_ans}]
            if st.session_state[_fh]:
                if st.button("🗑️ Clear chat", key="clr_forecast"):
                    st.session_state[_fh] = []; st.rerun()
    else:
        st.info("Need 4+ weeks of data to generate a forecast.")

    st.divider()

    # ── Failed & Rejected Orders ──
    st.markdown('<div class="section-header">❌ Failed & Rejected Orders Analysis</div>', unsafe_allow_html=True)

    if 'STATE' not in df.columns:
        st.info("STATE column not found.")
    else:
        failed_df   = df[df['STATE'] == 'Delivery Failed By Driver'].copy()
        rejected_df = df[df['STATE'].str.contains('Rejected|rejected', na=False)].copy()

        c1, c2 = st.columns(2)
        c1.metric("Total Failed (period)", len(failed_df),
                  delta=f"KPI ≤ {FAILED_KPI}/week",
                  delta_color="off")
        c2.metric("Total Rejected (period)", len(rejected_df))

        # Weekly trend chart
        def _weekly_state_trend(state_df, label, color, kpi_line=None):
            if state_df.empty:
                return None
            state_df = state_df.copy()
            state_df['ISO_Y'] = state_df['DELIVERY DATE'].dt.isocalendar().year
            state_df['ISO_W'] = state_df['DELIVERY DATE'].dt.isocalendar().week
            wk = (state_df.groupby(['ISO_Y','ISO_W']).size()
                  .reset_index(name=label))
            wk['Week_Label'] = (wk['ISO_Y'].astype(str)+"-W"+
                                wk['ISO_W'].astype(str).str.zfill(2))
            fig, ax = plt.subplots(figsize=(12, 4))
            ax.plot(wk['Week_Label'], wk[label], marker='o', color=color, lw=2, label=label)
            if kpi_line:
                ax.axhline(kpi_line, linestyle='--', color='orange', lw=2,
                           label=f'KPI ({kpi_line})')
            ax.set_xlabel("Week"); ax.set_ylabel("Count"); ax.grid(True, alpha=0.3)
            ax.legend(); plt.xticks(rotation=45, ha='right'); plt.tight_layout()
            return fig, wk

        if not failed_df.empty:
            result = _weekly_state_trend(failed_df, "Failed Orders", "#d62728", FAILED_KPI)
            if result:
                fig_f, failed_weekly = result
                st.pyplot(fig_f); plt.close()

                # Day × City pivot for selected week
                failed_weekly_wl = failed_weekly.copy()
                week_opts = failed_weekly_wl['Week_Label'].tolist()
                sel_week = st.selectbox("Select Week for Breakdown", week_opts,
                                        index=len(week_opts)-1, key="failed_week_sel")
                yr, wn = int(sel_week.split("-W")[0]), int(sel_week.split("-W")[1])
                w_start = pd.to_datetime(f"{yr}-W{wn}-1", format='%G-W%V-%u')
                w_end   = w_start + pd.Timedelta(days=6)
                wf      = failed_df[(failed_df['DELIVERY DATE'] >= w_start) &
                                    (failed_df['DELIVERY DATE'] <= w_end)].copy()
                wf['Day'] = wf['DELIVERY DATE'].dt.day_name()

                pivot = pd.pivot_table(wf, index='BUSINESS CITY', columns='Day',
                                       values='ID', aggfunc='count', fill_value=0)
                pivot = pivot.reindex(columns=DAY_NAMES, fill_value=0)
                pivot['Total'] = pivot.sum(axis=1)
                total_row = pivot.sum().to_frame().T; total_row.index = ['TOTAL']
                pivot = pd.concat([pivot, total_row])
                tot = int(pivot.loc['TOTAL','Total'])
                pivot['Status'] = ""
                pivot.loc['TOTAL','Status'] = (
                    "✅ Within KPI" if tot <= FAILED_KPI
                    else f"❌ Over by {tot - FAILED_KPI}"
                )
                st.dataframe(pivot.style.set_properties(**{'text-align':'center'}),
                             use_container_width=True)
                st.download_button("⬇️ Download Failed Orders",
                                   data=excel_bytes(wf),
                                   file_name=f"failed_{sel_week}.xlsx",
                                   mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

                with st.spinner("Generating failed orders insight…"):
                    ins_f, ctx_f = build_failed_insight(failed_weekly_wl, pivot, sel_week)
                ai_block("failed_orders", ctx_f, ins_f)

        if not rejected_df.empty:
            st.markdown("#### 🚫 Rejected Orders Trend")
            result_r = _weekly_state_trend(rejected_df, "Rejected Orders", "#9467bd")
            if result_r:
                fig_r, rej_weekly = result_r
                st.pyplot(fig_r); plt.close()

        # PDF download
        st.divider()
        pdf_data = BytesIO()
        with PdfPages(pdf_data) as pdf:
            for city in sorted(df['BUSINESS CITY'].dropna().unique()):
                cdf = df[df['BUSINESS CITY'] == city]
                cw = (cdf.groupby(cdf['DELIVERY DATE'].dt.to_period('W-SUN'))
                      .agg(Total_Orders=('ID','count'), Total_Sales=('SUBTOTAL','sum'))
                      .reset_index())
                cw['Week'] = cw['DELIVERY DATE'].dt.start_time
                cw['Week_Label'] = cw['DELIVERY DATE'].apply(
                    lambda p: f"W{p.week}")
                cw = apply_growth_kpi(cw)
                fig_p, ax_p1 = plt.subplots(figsize=(10, 5))
                ax_p1.plot(cw['Week_Label'], cw['Total_Orders'], marker='o', label='Orders')
                if 'Growth KPI Orders' in cw.columns:
                    ax_p1.plot(cw['Week_Label'], cw['Growth KPI Orders'],
                               linestyle='--', color='green', label='KPI')
                ax_p1.set_ylabel("Orders"); ax_p1.grid(True)
                ax_p2 = ax_p1.twinx()
                ax_p2.plot(cw['Week_Label'], cw['Total_Sales'],
                           color='orange', marker='o', label='Sales')
                ax_p2.yaxis.set_major_formatter(fmt_millions)
                ax_p2.set_ylabel("Sales (TZS)")
                plt.title(f"KPI Trend — {city}"); fig_p.legend(loc='upper left')
                plt.tight_layout(); pdf.savefig(fig_p); plt.close()

        st.download_button("📥 Download All Cities KPI PDF",
                           data=pdf_data.getvalue(),
                           file_name="Weekly_KPI_All_Cities.pdf",
                           mime="application/pdf")


# ═══════════════════════════════════════════════════════════════
# TAB 2 — DELIVERY TIMES
# ═══════════════════════════════════════════════════════════════
with tab2:
    st.markdown('<div class="section-header">⏰ Delivery Time Analysis</div>', unsafe_allow_html=True)

    df2 = compute_delivery_stages(df)
    df2 = add_distance(df2)
    df2['ISO_Week'] = df2['DELIVERY DATE'].dt.isocalendar().week
    df2['ISO_Year'] = df2['DELIVERY DATE'].dt.isocalendar().year

    # ── Week selector — default latest week ──
    _wk_grp = (df2.groupby(['ISO_Year','ISO_Week']).size().reset_index()[['ISO_Year','ISO_Week']]
               .sort_values(['ISO_Year','ISO_Week']))
    _wk_grp['Label'] = (_wk_grp['ISO_Year'].astype(str) + "-W"
                         + _wk_grp['ISO_Week'].astype(str).str.zfill(2))
    del_week_labels = _wk_grp['Label'].tolist()
    sel_del_week = st.selectbox("📅 Select Week (KPI metrics & table, default = latest)",
                                del_week_labels, index=len(del_week_labels)-1, key="del_week_sel")
    _yr = int(sel_del_week.split("-W")[0]); _wn = int(sel_del_week.split("-W")[1])
    df2_week = df2[(df2['ISO_Year']==_yr) & (df2['ISO_Week']==_wn)]

    # ── KPI metrics — selected week only ──
    _comp = (df2_week[df2_week['STATE'].isin(['Delivery Completed By Driver','Completed'])]
             if 'STATE' in df2_week.columns else df2_week)
    avg_adt = _comp['Average Delivery Time'].mean() if not _comp.empty else 0
    avg_dib = _comp['Driver in Business'].mean()    if not _comp.empty else 0
    avg_p2c = _comp['Pickup to Customer'].mean()    if not _comp.empty else 0
    avg_abb = _comp['Accepted by Business'].mean()  if not _comp.empty else 0

    mc1, mc2, mc3, mc4 = st.columns(4)
    mc1.metric("⏱ Avg Delivery Time",    f"{avg_adt:.1f} min",
               delta="Target < 45 min",  delta_color=("normal" if avg_adt < 45 else "inverse"))
    mc2.metric("🍳 Vendor Prep Time",    f"{avg_dib:.1f} min",
               delta="Target < 20 min",  delta_color=("normal" if avg_dib < 20 else "inverse"))
    mc3.metric("🛵 Pickup→Customer",     f"{avg_p2c:.1f} min")
    mc4.metric("✅ Business Acceptance", f"{avg_abb:.1f} min")

    # ── Stage table — selected week only ──
    st.subheader(f"📊 Delivery Stage Avg by City — {sel_del_week}")
    stage_cols = ['Accepted by Business','Assigned Time','Accepted by Driver',
                  'Driver to Business','Driver in Business','Pickup to Customer',
                  'Average Delivery Time']
    city_stage = (df2_week.groupby('BUSINESS CITY')[stage_cols]
                  .mean().round(1).reset_index()
                  .sort_values('Average Delivery Time', ascending=True))
    st.dataframe(city_stage, use_container_width=True)
    st.download_button("⬇️ Download Delivery Table",
                       data=city_stage.to_csv(index=False).encode(),
                       file_name=f"delivery_{sel_del_week}.csv", mime="text/csv")

    # ── Hourly chart ──
    st.subheader("📈 Hourly Delivery Time vs Volume")
    df2['HOUR'] = df2['DELIVERY TIME'].dt.hour
    hourly = (df2[df2['HOUR'].isin(OPERATING_HOURS)]
              .groupby('HOUR')
              .agg(avg_dt=('Average Delivery Time','mean'), orders=('ID','count'))
              .reset_index())
    hourly['order_idx'] = hourly['HOUR'].apply(lambda h: OPERATING_HOURS.index(h))
    hourly = hourly.sort_values('order_idx')
    hourly['Label'] = hourly['HOUR'].apply(lambda h: f"{h:02d}:00")

    fig_h, ax_h1 = plt.subplots(figsize=(13, 5))
    ax_h2 = ax_h1.twinx()
    ax_h2.bar(hourly['Label'], hourly['orders'], alpha=0.25, color='steelblue', label='Orders')
    ax_h1.plot(hourly['Label'], hourly['avg_dt'], marker='o', color='red', lw=2, label='Avg Delivery Time')
    ax_h1.set_ylabel("Avg Delivery Time (min)"); ax_h2.set_ylabel("Order Volume")
    ax_h1.set_xlabel("Hour"); ax_h1.grid(True, alpha=0.3)
    h1l, h1lb = ax_h1.get_legend_handles_labels(); h2l, h2lb = ax_h2.get_legend_handles_labels()
    ax_h1.legend(h1l+h2l, h1lb+h2lb, loc='upper right')
    plt.title("Hourly Delivery Time vs Volume"); plt.xticks(rotation=90); plt.tight_layout()
    st.pyplot(fig_h); plt.close()

    # ── Area charts (Dar vs Regional) ──
    st.subheader("📍 Area Performance Charts")
    for area_name, cities in [("🏙️ Dar es Salaam", DAR_CITIES), ("🌍 Regional", REGIONAL_CITIES)]:
        with st.expander(area_name):
            df_area = df2[df2['BUSINESS CITY'].isin(cities)]
            if df_area.empty:
                st.info("No data for this area in current filter.")
                continue
            for metric, title in [
                ('Average Delivery Time', 'Avg Delivery Time'),
                ('Driver in Business',    'Vendor Prep Time'),
                ('Pickup to Customer',    'Pickup → Customer'),
            ]:
                fig_a, ax_a = plt.subplots(figsize=(10, 4))
                for city in cities:
                    cdf = df_area[df_area['BUSINESS CITY']==city]
                    if cdf.empty: continue
                    wk = (cdf.groupby(cdf['DELIVERY DATE'].dt.to_period('W-SUN'))[metric]
                          .mean().reset_index())
                    wk.columns = ['Period', metric]
                    wk = wk.sort_values('Period')
                    wk['Label'] = [f"W{i+1}" for i in range(len(wk))]
                    ax_a.plot(wk['Label'], wk[metric], marker='o', label=city)
                ax_a.set_title(f"{title} — {area_name}")
                ax_a.set_ylabel("Minutes"); ax_a.grid(True, alpha=0.3); ax_a.legend()
                plt.tight_layout(); st.pyplot(fig_a); plt.close()

    # AI insight
    with st.spinner("Generating delivery insight…"):
        ins2, ctx2 = build_delivery_insight(city_stage, city_label)
    ai_block("delivery_time", ctx2, ins2)

    st.divider()

    # ── Heatmap ──
    st.subheader("🗺️ Customer & Business Location Heatmap")
    req_geo = ['CUSTOMER LATITUDE','CUSTOMER LONGITUDE','BUSINESS LATITUDE','BUSINESS LONGITUDE']
    if all(c in df2.columns for c in req_geo):
        geo = df2.dropna(subset=req_geo)
        if not geo.empty:
            map_type = st.radio("Map View",
                ["Both","Customer Only","Business Only"], horizontal=True, key="del_map")
            center = ([geo['CUSTOMER LATITUDE'].mean(), geo['CUSTOMER LONGITUDE'].mean()]
                      if city_sel else [-6.8018, 39.2801])
            m = folium.Map(location=center, zoom_start=13)
            if map_type != "Business Only":
                HeatMap(geo[['CUSTOMER LATITUDE','CUSTOMER LONGITUDE']].values.tolist(),
                        radius=12, blur=10).add_to(m)
            if map_type != "Customer Only":
                HeatMap(geo[['BUSINESS LATITUDE','BUSINESS LONGITUDE']].values.tolist(),
                        radius=15, blur=12).add_to(m)
            folium.LayerControl().add_to(m)

            top_n_del = st.slider("Top restaurants on map", 5, 30, 10, key="del_top_n")
            rp = (geo.groupby(['BUSINESS NAME','BUSINESS LATITUDE','BUSINESS LONGITUDE'])
                  .agg(Orders=('ID','count'), Sales=('SUBTOTAL','sum'),
                       AvgDT=('Average Delivery Time','mean'))
                  .reset_index().sort_values('Orders', ascending=False))
            for _, r in rp.head(top_n_del).iterrows():
                folium.CircleMarker(
                    [r['BUSINESS LATITUDE'], r['BUSINESS LONGITUDE']],
                    radius=7, color='navy', fill=True, fill_opacity=0.8,
                    popup=f"<b>{r['BUSINESS NAME']}</b><br>Orders: {int(r['Orders'])}<br>"
                          f"Avg DT: {r['AvgDT']:.1f} min"
                ).add_to(m)
            st.components.v1.html(m._repr_html_(), height=500)
    else:
        st.info("Geo columns not found.")

    # PDF report
    st.divider()
    if st.button("🖨️ Generate Delivery PDF Report"):
        pdf_d = BytesIO()
        with PdfPages(pdf_d) as pdf:
            plt.figure(figsize=(11,8)); plt.axis('off')
            plt.text(0.5,0.6,"Piki Delivery Performance Report",fontsize=24,ha='center')
            plt.text(0.5,0.45,f"{date_range[0]} → {date_range[1]}",fontsize=14,ha='center')
            pdf.savefig(); plt.close()
            for area_name, cities in [("Dar es Salaam", DAR_CITIES), ("Regional", REGIONAL_CITIES)]:
                for metric, title in [
                    ('Average Delivery Time','Avg Delivery Time'),
                    ('Driver in Business','Vendor Prep Time'),
                    ('Pickup to Customer','Pickup→Customer'),
                ]:
                    plt.figure(figsize=(10,5))
                    for city in cities:
                        cdf = df2[df2['BUSINESS CITY']==city]
                        if cdf.empty: continue
                        wk = cdf.groupby(cdf['DELIVERY DATE'].dt.to_period('W-SUN'))[metric].mean().reset_index()
                        wk.columns = ['P', metric]; wk = wk.sort_values('P')
                        plt.plot([f"W{i+1}" for i in range(len(wk))], wk[metric], marker='o', label=city)
                    plt.title(f"{title} — {area_name}"); plt.ylabel("Min"); plt.legend(); plt.grid(True)
                    pdf.savefig(); plt.close()
        st.download_button("📥 Download Delivery PDF",
                           data=pdf_d.getvalue(),
                           file_name="Delivery_Performance_Report.pdf",
                           mime="application/pdf")


# ═══════════════════════════════════════════════════════════════
# TAB 3 — RIDER ATTENDANCE
# ═══════════════════════════════════════════════════════════════
with tab3:
    st.markdown('<div class="section-header">🚴 Driver Attendance & Analysis</div>', unsafe_allow_html=True)

    df3 = df.copy()
    df3['DELIVERY DATE'] = pd.to_datetime(df3['DELIVERY DATE'], errors='coerce')

    # Zone map from full raw dataset for accuracy
    _zone_src = raw.copy()
    _zone_src['DELIVERY DATE'] = pd.to_datetime(_zone_src['DELIVERY DATE'], errors='coerce')
    zone_map = (_zone_src.groupby('DRIVER NAME')['BUSINESS CITY']
                .agg(lambda x: x.mode().iloc[0] if not x.mode().empty else None))
    df3['WORKING ZONE'] = df3['DRIVER NAME'].map(zone_map)
    df3['ISO_Week'] = df3['DELIVERY DATE'].dt.isocalendar().week
    df3['ISO_Year'] = df3['DELIVERY DATE'].dt.isocalendar().year
    df3['Day of Week'] = df3['DELIVERY DATE'].dt.day_name()

    # ── Week selector — default latest ──
    _att_wk = (df3.groupby(['ISO_Year','ISO_Week']).size().reset_index()[['ISO_Year','ISO_Week']]
               .sort_values(['ISO_Year','ISO_Week']))
    _att_wk['Label'] = (_att_wk['ISO_Year'].astype(str) + "-W"
                        + _att_wk['ISO_Week'].astype(str).str.zfill(2))
    att_labels = _att_wk['Label'].tolist()
    sel_week_att = st.selectbox("📅 Select ISO Week (default = latest)",
                                att_labels, index=len(att_labels)-1, key="att_week")
    _ayr = int(sel_week_att.split("-W")[0]); _awn = int(sel_week_att.split("-W")[1])
    df_week = df3[(df3['ISO_Year']==_ayr) & (df3['ISO_Week']==_awn)]

    # ── Build attendance pivot ──
    pivot_rows = []
    for _, tr in TARGET_RIDERS.iterrows():
        city = tr['Business City']
        row  = {'WORKING ZONE': city}
        city_df = df_week[df_week['WORKING ZONE'] == city]
        deficits, surplus = [], []
        for day in DAY_NAMES:
            dtype  = 'Weekend' if day in ['Saturday','Sunday'] else 'Weekday'
            std    = tr[f'{dtype} Active Riders']
            actual = city_df[city_df['Day of Week']==day]['DRIVER NAME'].nunique()
            row[day] = f"✅ {actual}" if actual >= std else f"⚠️ {actual}/{std}"
            if actual < std:
                deficits.append(std - actual)
            else:
                surplus.append(actual - std)
        row['Avg Deficiency'] = round(sum(deficits)/len(deficits), 1) if deficits else 0.0
        row['Avg Surplus']    = round(sum(surplus)/len(surplus), 1)   if surplus  else 0.0
        row['Status'] = (f"➕ Add {int(round(sum(deficits)/len(deficits)))} rider(s)"
                         if deficits else "✅ Sufficient")
        pivot_rows.append(row)

    att_pivot = pd.DataFrame(pivot_rows)

    # ── 4 summary KPI metrics ──
    n_deficient = len(att_pivot[att_pivot['Avg Deficiency'] > 0])
    n_ok        = len(att_pivot) - n_deficient
    worst_city  = (att_pivot.nlargest(1, 'Avg Deficiency')['WORKING ZONE'].values[0]
                   if n_deficient else "—")
    _ok_zones   = att_pivot[att_pivot['Avg Deficiency'] == 0]
    best_city   = (_ok_zones.nlargest(1, 'Avg Surplus')['WORKING ZONE'].values[0]
                   if not _ok_zones.empty else "—")

    _a1, _a2, _a3, _a4 = st.columns(4)
    _a1.metric("✅ Cities at Target",    n_ok)
    _a2.metric("⚠️ Cities Understaffed", n_deficient)
    _a3.metric("🔴 Worst Zone",          worst_city)
    _a4.metric("🟢 Best Zone",           best_city)

    # Show pivot without surplus column for clean display
    _disp_cols = ['WORKING ZONE'] + DAY_NAMES + ['Avg Deficiency','Status']
    st.dataframe(att_pivot[_disp_cols], use_container_width=True)
    st.download_button("⬇️ Download Attendance Report",
                       data=excel_bytes(att_pivot, "Attendance"),
                       file_name=f"attendance_{sel_week_att}.xlsx",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

    # ── Per-zone individual charts ──
    st.subheader("📊 Daily Active Drivers by Zone")
    daily_drivers = (df_week.groupby(['WORKING ZONE','Day of Week'])['DRIVER NAME']
                     .nunique().reset_index(name='Active Drivers'))
    daily_drivers['Day of Week'] = pd.Categorical(daily_drivers['Day of Week'],
                                                   categories=DAY_NAMES, ordered=True)
    daily_drivers = daily_drivers.sort_values(['WORKING ZONE','Day of Week'])

    for group_name, group_cities in [("🏙️ Dar es Salaam", DAR_CITIES),
                                      ("🌍 Regional", REGIONAL_CITIES)]:
        active_zones = [z for z in group_cities
                        if z in daily_drivers['WORKING ZONE'].values or
                           z in att_pivot['WORKING ZONE'].values]
        if not active_zones:
            continue
        st.markdown(f"#### {group_name}")
        # 2 charts per row
        for i in range(0, len(active_zones), 2):
            _cols = st.columns(2)
            for j, zone in enumerate(active_zones[i:i+2]):
                _zd = (daily_drivers[daily_drivers['WORKING ZONE']==zone]
                       .set_index('Day of Week').reindex(DAY_NAMES))
                _tr = TARGET_RIDERS[TARGET_RIDERS['Business City']==zone]
                if _tr.empty:
                    continue
                _wt = int(_tr['Weekday Active Riders'].values[0])
                _wet = int(_tr['Weekend Active Riders'].values[0])
                _targets = [_wet if d in ['Saturday','Sunday'] else _wt for d in DAY_NAMES]
                _actual  = _zd['Active Drivers'].fillna(0).values

                with _cols[j]:
                    fig_z, ax_z = plt.subplots(figsize=(6, 3.5))
                    _colors = ['#28a745' if a >= t else '#dc3545'
                               for a, t in zip(_actual, _targets)]
                    ax_z.bar(DAY_NAMES, _actual, color=_colors, alpha=0.8, label='Actual')
                    ax_z.step(range(len(DAY_NAMES)), _targets, where='mid',
                              color='black', linestyle='--', lw=1.5, label='Target')
                    ax_z.set_title(zone, fontsize=11, fontweight='bold')
                    ax_z.set_ylabel("Drivers"); ax_z.set_ylim(bottom=0)
                    ax_z.set_xticklabels([d[:3] for d in DAY_NAMES], fontsize=8)
                    ax_z.legend(fontsize=7); ax_z.grid(True, alpha=0.2, axis='y')
                    plt.tight_layout()
                    st.pyplot(fig_z); plt.close()

    # ── AI Insight — Attendance ──
    with st.spinner("Generating attendance insight…"):
        ins3, ctx3 = build_attendance_insight(att_pivot, sel_week_att, df_week)
    ai_block("rider_attendance", ctx3, ins3)

    st.divider()

    # ════════════════════════════════════════════════════
    # DRIVER PERFORMANCE REVIEW — Last 8 Weeks
    # ════════════════════════════════════════════════════
    st.markdown('<div class="section-header">🏆 Driver Performance Review — Last 8 Weeks</div>', unsafe_allow_html=True)

    # ── Compute delivery stage metrics for completed orders ──
    _dr_df = raw.copy()
    _dr_df['DELIVERY DATE'] = pd.to_datetime(_dr_df['DELIVERY DATE'], errors='coerce')
    _dr_df['Week'] = _dr_df['DELIVERY DATE'].dt.to_period('W-SUN').apply(lambda r: r.start_time)
    _dr_df = compute_delivery_stages(_dr_df)

    # Working zone map
    _dr_zone = (_dr_df.groupby('DRIVER NAME')['BUSINESS CITY']
                .agg(lambda x: x.mode().iloc[0] if not x.mode().empty else "Unknown"))

    # ─── Section A: Attendance — last 8 weeks ───────────────
    st.markdown("### 📅 A. Weekly Attendance (Last 8 Weeks)")
    _weekdays_order = ['Monday','Tuesday','Wednesday','Thursday','Friday','Saturday','Sunday']
    _recent_8_weeks = _dr_df['Week'].drop_duplicates().sort_values(ascending=False).head(8)

    _all_att = []
    for _wk in _recent_8_weeks:
        _wk_data = _dr_df[_dr_df['Week'] == _wk]
        _iso_w = int(_wk.isocalendar()[1])
        _wk_label = f"W{_iso_w}"
        _pivot = pd.pivot_table(_wk_data, values='ID', index='DRIVER NAME',
                                columns=_wk_data['DELIVERY DATE'].dt.day_name(),
                                aggfunc='count', fill_value=0)
        _pivot = _pivot.reindex(columns=_weekdays_order, fill_value=0)
        _pivot = _pivot.applymap(lambda x: '✔' if x > 0 else '—')
        _pivot['Days'] = (_pivot == '✔').sum(axis=1)
        _pivot['Orders'] = _wk_data.groupby('DRIVER NAME')['ID'].count()
        _pivot['Week'] = _wk_label
        _pivot = _pivot.reset_index()
        _all_att.append(_pivot)

    if _all_att:
        _att_all = pd.concat(_all_att, ignore_index=True)
        _att_all['Working Zone'] = _att_all['DRIVER NAME'].map(_dr_zone)
        _att_cols = ['Week','DRIVER NAME','Working Zone'] + _weekdays_order + ['Days','Orders']
        _att_all = _att_all[[c for c in _att_cols if c in _att_all.columns]]

        # Filter by zone
        _perf_zones = sorted(_att_all['Working Zone'].dropna().unique())
        _zone_filter = st.multiselect("Filter by Working Zone", _perf_zones,
                                      placeholder="All zones", key="dr_zone_filter")
        _att_show = _att_all[_att_all['Working Zone'].isin(_zone_filter)] if _zone_filter else _att_all

        # Color-code rows: many days = green, few days = red
        def _style_att(v):
            if v == '✔': return 'background-color:#d4edda;color:#155724'
            if v == '—':  return 'background-color:#fff3cd;color:#856404'
            return ''

        st.dataframe(_att_show.style.applymap(_style_att,
                     subset=[c for c in _weekdays_order if c in _att_show.columns]),
                     use_container_width=True, height=400)
        st.download_button("⬇️ Download Attendance (8 weeks)",
                           data=excel_bytes(_att_all, "Attendance"),
                           file_name="Driver_Attendance_8W.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

        # ── Visualisations ──
        _v1, _v2, _v3 = st.columns(3)
        with _v1:
            st.markdown("**Days worked distribution**")
            _days_dist = _att_all.groupby('DRIVER NAME')['Days'].mean().round(1)
            _fd, _ad = plt.subplots(figsize=(5,3))
            _days_dist.value_counts().sort_index().plot(kind='bar', ax=_ad,
                color='#4d96ff', edgecolor='white')
            _ad.set_xlabel("Avg days/week"); _ad.set_ylabel("# Drivers")
            _ad.set_title("Days Worked Distribution"); plt.tight_layout()
            st.pyplot(_fd); plt.close()

        with _v2:
            st.markdown("**Attendance rate by day**")
            _day_rate = _att_all[[d for d in _weekdays_order if d in _att_all.columns]].apply(
                lambda col: (col=='✔').sum() / len(col) * 100)
            _fr, _ar = plt.subplots(figsize=(5,3))
            _day_rate.plot(kind='bar', ax=_ar, color=['#28a745' if v>=60 else '#dc3545' for v in _day_rate])
            _ar.set_ylabel("Attendance %"); _ar.set_ylim(0,100)
            _ar.set_title("Attendance Rate by Day")
            _ar.set_xticklabels([d[:3] for d in _day_rate.index], rotation=0)
            plt.tight_layout(); st.pyplot(_fr); plt.close()

        with _v3:
            st.markdown("**Worked vs Missed (overall)**")
            _total_worked = (_att_all[[d for d in _weekdays_order if d in _att_all.columns]] == '✔').values.sum()
            _total_missed = (_att_all[[d for d in _weekdays_order if d in _att_all.columns]] == '—').values.sum()
            _fp, _ap = plt.subplots(figsize=(4,3))
            _ap.pie([_total_worked, _total_missed], labels=['Worked','Missed'],
                    colors=['#28a745','#ffc107'], autopct='%1.0f%%',
                    startangle=90, wedgeprops={'edgecolor':'white','lw':2})
            _ap.set_title("Overall Attendance"); plt.tight_layout()
            st.pyplot(_fp); plt.close()

    # ─── Section B: KPI Performance — last 8 weeks ──────────
    st.markdown("### 📊 B. Driver KPI Performance (Last 8 Weeks)")
    st.caption("Only clean completed deliveries used for time KPIs (outliers excluded).")

    _dr_comp = _dr_df[_dr_df['STATE'].isin(['Delivery Completed By Driver','Completed'])].copy()

    def _cat_issues(row):
        checks = [('Accepted by Business',30),('Assigned Time',30),('Accepted by Driver',45),
                  ('Driver to Business',45),('Driver in Business',90),('Pickup to Customer',45),
                  ('Average Delivery Time',100)]
        return ", ".join(c for c,l in checks
                         if pd.isnull(row.get(c,0)) or row.get(c,0) < 0 or row.get(c,0) > l)

    _dr_comp['Issues'] = _dr_comp.apply(_cat_issues, axis=1)
    _dr_comp_clean = _dr_comp[_dr_comp['Issues'] == ''].copy()

    _recent_8_kpi = _dr_comp_clean['Week'].drop_duplicates().sort_values(ascending=False).head(8)
    _all_kpis = []

    def _iso_w(ts):
        ic = ts.isocalendar()
        return ic.week if hasattr(ic,'week') else ic[1]

    for _wk in _recent_8_kpi:
        _wk_data = _dr_comp_clean[_dr_comp_clean['Week'] == _wk].copy()
        if 'DISTANCE (km)' not in _wk_data.columns: _wk_data['DISTANCE (km)'] = 0.0
        _kpi = _wk_data.groupby('DRIVER NAME').agg(
            Avg_DT=('Average Delivery Time','mean'),
            Accepted_Biz=('Accepted by Business','mean'),
            Assigned_T=('Assigned Time','mean'),
            Accepted_Drv=('Accepted by Driver','mean'),
            Drv_to_Biz=('Driver to Business','mean'),
            Drv_in_Biz=('Driver in Business','mean'),
            Pickup_Cust=('Pickup to Customer','mean'),
            Total_Orders=('ID','count'),
            Total_KM=('DISTANCE (km)','sum'),
            Avg_KM=('DISTANCE (km)','mean')
        ).round(1).reset_index()
        _kpi.columns = ['DRIVER NAME','Avg DT (min)','Accepted by Biz','Assigned Time',
                        'Accepted by Driver','Driver→Business','Driver in Biz','Pickup→Customer',
                        'Total Orders','Total KM','Avg KM/Order']
        _kpi['Week'] = f"W{int(_iso_w(_wk))}"; _kpi['Working Zone'] = _kpi['DRIVER NAME'].map(_dr_zone)
        _all_kpis.append(_kpi)

    _kpi_all = pd.DataFrame()
    if _all_kpis:
        _kpi_all = pd.concat(_all_kpis, ignore_index=True)
        _kpi_all = _kpi_all[['Week','DRIVER NAME','Working Zone','Total Orders',
                              'Avg DT (min)','Accepted by Biz','Assigned Time','Accepted by Driver',
                              'Driver→Business','Driver in Biz','Pickup→Customer','Total KM','Avg KM/Order']]

        # Sort most-recent week first per driver
        _kpi_all['_wn'] = _kpi_all['Week'].str.extract(r'(\d+)').astype(int)
        _kpi_all = _kpi_all.sort_values(['DRIVER NAME','_wn'], ascending=[True,False]).drop(columns='_wn')

        _kpi_zone_f = st.multiselect("Filter by Working Zone (KPI table)", _perf_zones,
                                      placeholder="All zones", key="kpi_zone_filter")
        _kpi_show = _kpi_all[_kpi_all['Working Zone'].isin(_kpi_zone_f)] if _kpi_zone_f else _kpi_all

        # Color-code DT column
        def _color_dt(v):
            try:
                f = float(v)
                if f <= 40: return 'background-color:#d4edda;color:#155724'
                if f <= 55: return 'background-color:#fff3cd;color:#856404'
                return 'background-color:#f8d7da;color:#721c24'
            except: return ''

        st.dataframe(_kpi_show.style.applymap(_color_dt, subset=['Avg DT (min)']),
                     use_container_width=True, height=440)
        st.download_button("⬇️ Download Driver KPIs (8 weeks)",
                           data=excel_bytes(_kpi_all, "Driver KPIs"),
                           file_name="Driver_KPIs_8W.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

        # ── Top / Bottom performers visual ──
        st.markdown("#### 🏅 Top & Bottom Performers (8-Week Average Delivery Time)")
        _perf_sum = (_kpi_all.groupby(['DRIVER NAME','Working Zone'])['Avg DT (min)']
                     .mean().round(1).reset_index()
                     .rename(columns={'Avg DT (min)':'8W Avg DT (min)'})
                     .sort_values('8W Avg DT (min)'))
        _pg1, _pg2 = st.columns(2)
        with _pg1:
            st.markdown("🟢 **Top 10 Fastest Riders**")
            _top10 = _perf_sum.head(10)
            _ftop, _atop = plt.subplots(figsize=(6,3.5))
            _bars_top = _atop.barh(_top10['DRIVER NAME'], _top10['8W Avg DT (min)'], color='#28a745')
            _atop.bar_label(_bars_top, fmt='%.1f', padding=3, fontsize=8)
            _atop.axvline(45, color='green', lw=1.5, linestyle='--', label='Target')
            _atop.set_xlabel("Avg DT (min)"); _atop.invert_yaxis()
            _atop.set_title("Fastest Riders"); _atop.legend(fontsize=7); plt.tight_layout()
            st.pyplot(_ftop); plt.close()
            st.dataframe(_top10[['DRIVER NAME','Working Zone','8W Avg DT (min)']],
                         use_container_width=True)
        with _pg2:
            st.markdown("🔴 **Bottom 10 — Need Coaching**")
            _bot10 = _perf_sum.tail(10).sort_values('8W Avg DT (min)', ascending=False)
            _fbot, _abot = plt.subplots(figsize=(6,3.5))
            _bars_bot = _abot.barh(_bot10['DRIVER NAME'], _bot10['8W Avg DT (min)'], color='#dc3545')
            _abot.bar_label(_bars_bot, fmt='%.1f', padding=3, fontsize=8)
            _abot.axvline(55, color='red', lw=1.5, linestyle=':', label='Alert')
            _abot.set_xlabel("Avg DT (min)"); _abot.invert_yaxis()
            _abot.set_title("Needs Coaching"); _abot.legend(fontsize=7); plt.tight_layout()
            st.pyplot(_fbot); plt.close()
            st.dataframe(_bot10[['DRIVER NAME','Working Zone','8W Avg DT (min)']],
                         use_container_width=True)

        # ── Weekly trend: top 10 by volume ──
        st.markdown("#### 📈 Delivery Time Trend — Top 10 Riders by Volume")
        _top_vol = _kpi_all.groupby('DRIVER NAME')['Total Orders'].sum().nlargest(10).index.tolist()
        _td = _kpi_all[_kpi_all['DRIVER NAME'].isin(_top_vol)]
        _fig_tr, _ax_tr = plt.subplots(figsize=(13,5))
        for _rn in _top_vol:
            _rd = _td[_td['DRIVER NAME']==_rn].sort_values('Week')
            if _rd.empty: continue
            _ax_tr.plot(_rd['Week'], _rd['Avg DT (min)'], marker='o', lw=1.5, label=_rn)
        _ax_tr.axhline(45, color='green', lw=2, linestyle='--', label='Target (45 min)')
        _ax_tr.axhline(55, color='red', lw=1.5, linestyle=':', label='Alert (55 min)')
        _ax_tr.fill_between(range(len(_kpi_all['Week'].unique())), 0, 45, alpha=0.05, color='green')
        _ax_tr.set_xlabel("Week"); _ax_tr.set_ylabel("Avg DT (min)")
        _ax_tr.set_title("Weekly Delivery Time Trend — Top 10 by Volume")
        _ax_tr.legend(fontsize=7, ncol=4); _ax_tr.grid(True, alpha=0.3)
        plt.tight_layout(); st.pyplot(_fig_tr); plt.close()

    # ─── Section C: Regional Bonus Calculator ───────────────
    st.markdown("### 💰 C. Regional Rider Bonus Calculator")
    st.caption("Calculates bonus eligibility based on order volume vs city average and delivery time (target < 50 min)")

    _BONUS = 15000
    _regional_df = raw.copy()
    _regional_df['DELIVERY DATE'] = pd.to_datetime(_regional_df['DELIVERY DATE'], errors='coerce')
    _regional_df['Week'] = _regional_df['DELIVERY DATE'].dt.to_period('W-SUN').apply(lambda r: r.start_time)

    _bonus_comp = compute_delivery_stages(_regional_df)
    _bonus_comp = _bonus_comp[_bonus_comp['STATE'].isin(['Delivery Completed By Driver','Completed'])].copy()

    # Bonus week selector
    _bonus_weeks_avail = sorted(_bonus_comp['Week'].dropna().unique(), reverse=True)
    _bonus_week_opts   = [str(w.date()) for w in _bonus_weeks_avail]
    _sel_bonus_week_str = st.selectbox("Select week for bonus calculation (default = latest)",
                                        _bonus_week_opts, index=0, key="bonus_week_sel")
    _sel_bonus_week = _bonus_weeks_avail[_bonus_week_opts.index(_sel_bonus_week_str)]

    _bonus_reg = _regional_df[
        (_regional_df['Week'] == _sel_bonus_week) &
        (_regional_df['BUSINESS CITY'].isin(REGIONAL_CITIES))
    ].copy()
    _bonus_comp_reg = _bonus_comp[
        (_bonus_comp['Week'] == _sel_bonus_week) &
        (_bonus_comp['BUSINESS CITY'].isin(REGIONAL_CITIES))
    ].copy()

    if _bonus_reg.empty:
        st.info("No regional data for the selected week.")
    else:
        _drivers_reg = pd.Index(sorted(
            set(_bonus_reg['DRIVER NAME'].dropna()) | set(_bonus_comp_reg['DRIVER NAME'].dropna())))

        _tot_ord = _bonus_reg.groupby('DRIVER NAME')['ID'].count().reindex(_drivers_reg, fill_value=0)
        _avg_dt  = _bonus_comp_reg.groupby('DRIVER NAME')['Average Delivery Time'].mean().reindex(_drivers_reg, fill_value=np.nan)
        _wzone   = (_bonus_reg.groupby('DRIVER NAME')['BUSINESS CITY']
                    .agg(lambda x: x.mode().iloc[0] if not x.mode().empty else "Unknown")
                    .reindex(_drivers_reg, fill_value="Unknown"))

        # City average orders per driver
        _city_ord = _bonus_reg.groupby('BUSINESS CITY')['ID'].count()
        _city_drv = _bonus_reg.groupby('BUSINESS CITY')['DRIVER NAME'].nunique()
        _avg_city = (_city_ord / _city_drv).fillna(0)

        _bonus_df = pd.DataFrame({
            'Rider Name': _drivers_reg,
            'Working Zone': _wzone.values,
            'Total Orders': _tot_ord.values,
            'Avg Delivery Time (min)': _avg_dt.round(1).values
        })
        _bonus_df['City Avg Orders'] = _bonus_df['Working Zone'].map(_avg_city).round(1)
        _bonus_df['Availability Eligible'] = _bonus_df.apply(
            lambda r: '✅ Yes' if r['Total Orders'] > r['City Avg Orders'] else '❌ No', axis=1)
        _bonus_df['DT Eligible'] = _bonus_df['Avg Delivery Time (min)'].apply(
            lambda x: '✅ Yes' if pd.notna(x) and x < 50 else '❌ No')
        _bonus_df['Availability Bonus'] = _bonus_df['Availability Eligible'].apply(
            lambda x: _BONUS if x == '✅ Yes' else 0)
        _bonus_df['DT Bonus'] = _bonus_df['DT Eligible'].apply(
            lambda x: _BONUS if x == '✅ Yes' else 0)
        _bonus_df['Total Bonus (TZS)'] = _bonus_df['Availability Bonus'] + _bonus_df['DT Bonus']

        # Summary metrics
        _b1, _b2, _b3, _b4 = st.columns(4)
        _b1.metric("👥 Eligible Riders",     f"{len(_bonus_df[_bonus_df['Total Bonus (TZS)']>0])}")
        _b2.metric("💰 Total Bonus Payout",  f"{_bonus_df['Total Bonus (TZS)'].sum():,.0f} TZS")
        _b3.metric("⚡ Avg Orders/Rider",    f"{_bonus_df['Total Orders'].mean():.1f}")
        _b4.metric("⏱ Avg DT (region)",     f"{_avg_dt.mean():.1f} min" if not _avg_dt.isna().all() else "—")

        st.dataframe(_bonus_df.sort_values('Total Bonus (TZS)', ascending=False),
                     use_container_width=True)

        # Bonus breakdown chart
        _fig_bon, _ax_bon = plt.subplots(figsize=(12,4))
        _top_bon = _bonus_df.sort_values('Total Bonus (TZS)', ascending=False).head(20)
        _bars_b  = _ax_bon.bar(_top_bon['Rider Name'], _top_bon['Total Bonus (TZS)'],
                               color=['#28a745' if v == _BONUS*2 else ('#ffc107' if v == _BONUS else '#dc3545')
                                      for v in _top_bon['Total Bonus (TZS)']])
        _ax_bon.set_ylabel("Bonus (TZS)"); _ax_bon.set_ylim(0, _BONUS * 2.5)
        _ax_bon.set_title(f"Regional Bonus Breakdown — Week of {_sel_bonus_week_str}")
        plt.xticks(rotation=45, ha='right', fontsize=8); plt.tight_layout()
        st.pyplot(_fig_bon); plt.close()

        st.download_button("⬇️ Download Bonus Report",
                           data=excel_bytes(_bonus_df, "Bonus"),
                           file_name=f"Regional_Bonus_{_sel_bonus_week_str}.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

        # AI insight for bonus
        _bonus_ctx = (f"REGIONAL BONUS REPORT — Week {_sel_bonus_week_str}\n"
                      f"Total riders assessed: {len(_bonus_df)}\n"
                      f"Eligible for bonus: {len(_bonus_df[_bonus_df['Total Bonus (TZS)']>0])}\n"
                      f"Total payout: {_bonus_df['Total Bonus (TZS)'].sum():,.0f} TZS\n"
                      f"Avg delivery time: {_avg_dt.mean():.1f} min\n\n"
                      + _bonus_df.sort_values('Total Bonus (TZS)', ascending=False).head(10).to_string(index=False))
        _bonus_prompt = (
            "Senior BI analyst for a Tanzanian food delivery company.\n\n"
            + _bonus_ctx + "\n\n"
            "Provide:\n"
            "1. **Bonus Summary** — What % of riders earned full bonus? Partial? None?\n"
            "2. **Performance Patterns** — Which zones are performing best?\n"
            "3. **Underperformers** — Who needs coaching and on which metric?\n"
            "4. **Trend Alert** — Is regional delivery time improving or declining?\n"
            "5. **Actions** — 2 specific ops actions for next week.\nUse real numbers."
        )
        with st.spinner("Generating bonus insight…"):
            _bonus_ins = claude_insight(_bonus_prompt, max_tokens=700)
        ai_block("rider_bonus", _bonus_ctx, _bonus_ins)

        # ─── Section D: Delivery Time Trends pivot ───────────
        st.markdown("### 📈 D. Driver Delivery Time Trends (8 Weeks Pivot)")
        _trend_pivot = (_kpi_all.pivot_table(index='DRIVER NAME', columns='Week',
                                              values='Avg DT (min)', aggfunc='mean')
                        .round(1).reset_index() if _all_kpis else pd.DataFrame())
        if not _trend_pivot.empty:
            _trend_pivot['Working Zone'] = _trend_pivot['DRIVER NAME'].map(_dr_zone)
            _trend_pivot['Avg DT (overall)'] = (_kpi_all.groupby('DRIVER NAME')['Avg DT (min)']
                                                   .mean().round(1).reindex(_trend_pivot['DRIVER NAME']).values)
            st.dataframe(_trend_pivot.sort_values('Avg DT (overall)'), use_container_width=True)
            st.download_button("⬇️ Download DT Trends Pivot",
                               data=excel_bytes(_trend_pivot, "DT Trends"),
                               file_name="Driver_DT_Trends_8W.xlsx",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")


# ═══════════════════════════════════════════════════════════════
# TAB 4 — PRODUCTS & GEO
# ═══════════════════════════════════════════════════════════════
with tab4:
    st.markdown('<div class="section-header">📦 Product Trends & Geographic Analysis</div>', unsafe_allow_html=True)

    df4 = compute_delivery_stages(df)

    # ── Product aggregation ──
    product_totals     = defaultdict(int)
    weekly_prod_totals = defaultdict(lambda: defaultdict(int))
    prod_biz_map       = defaultdict(set)

    # Optional product filter within this tab
    prod_filter = st.multiselect("Filter by Product (optional)",
                                  sorted(set(PRODUCT_MAPPING.values())),
                                  key="prod_tab_filter")

    for _, row in df4.iterrows():
        try:
            wk_period = row['DELIVERY DATE'].to_period('W-SUN').start_time
        except Exception:
            continue
        bname = row.get('BUSINESS NAME', '')
        for pname, qty in extract_products(row.get('PRODUCTS', '')):
            pstd = standardize_product(pname)
            if prod_filter and pstd not in prod_filter:
                continue
            product_totals[pstd]                   += qty
            weekly_prod_totals[wk_period][pstd]    += qty
            prod_biz_map[pstd].add(bname)

    if product_totals:
        total_prod_df = pd.DataFrame(product_totals.items(), columns=['Product','Total Quantity'])
        total_prod_df['Businesses Selling']    = total_prod_df['Product'].apply(lambda x: len(prod_biz_map[x]))
        total_prod_df['Associated Businesses'] = total_prod_df['Product'].apply(
            lambda x: ", ".join(sorted(prod_biz_map[x])))
        total_prod_df = total_prod_df.sort_values('Total Quantity', ascending=False)
    else:
        total_prod_df = pd.DataFrame(columns=['Product','Total Quantity','Businesses Selling','Associated Businesses'])
        st.warning("No product data found. Check that the PRODUCTS column has data in format '1 x Item Name'.")

    # ── Business performance ──
    biz_perf = (df4.groupby('BUSINESS NAME')
                .agg(Total_Orders=('ID','count'), Total_Sales=('SUBTOTAL','sum'),
                     Avg_DT=('Average Delivery Time','mean'))
                .reset_index()
                .sort_values('Total_Orders', ascending=False)
                .head(10)
                .rename(columns={'Avg_DT':'Avg Delivery (min)'}))
    biz_perf['Avg Delivery (min)'] = biz_perf['Avg Delivery (min)'].round(1)

    # ── Two column layout ──
    pc1, pc2 = st.columns(2)

    with pc1:
        st.subheader("🏆 Top 10 Businesses")
        st.dataframe(biz_perf, use_container_width=True)
        fig_biz, ax_biz = plt.subplots(figsize=(7, 4))
        ax_biz.barh(biz_perf['BUSINESS NAME'], biz_perf['Total_Orders'], color='#1f77b4')
        ax_biz.set_xlabel("Orders"); ax_biz.invert_yaxis()
        ax_biz.set_title("Top 10 by Orders"); plt.tight_layout()
        st.pyplot(fig_biz); plt.close()

    with pc2:
        st.subheader("📦 Top 15 Products")
        st.dataframe(total_prod_df.head(15)[['Product','Total Quantity','Businesses Selling']],
                     use_container_width=True)
        top15 = total_prod_df.head(15)
        fig_prod, ax_prod = plt.subplots(figsize=(7, 4))
        ax_prod.barh(top15['Product'], top15['Total Quantity'], color='#2ca02c')
        ax_prod.set_xlabel("Quantity"); ax_prod.invert_yaxis()
        ax_prod.set_title("Top 15 Products"); plt.tight_layout()
        st.pyplot(fig_prod); plt.close()

    # Downloads
    dc1, dc2 = st.columns(2)
    dc1.download_button("⬇️ Download Business Report",
                        data=excel_bytes(biz_perf, "Top Businesses"),
                        file_name="Top_Businesses.xlsx",
                        mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    dc2.download_button("⬇️ Download Product Trend",
                        data=excel_bytes(total_prod_df, "Products"),
                        file_name="Total_Product_Trend.xlsx",
                        mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

    st.divider()

    # ── Weekly Product Movement ──
    st.subheader("📆 Weekly Product Movement")
    wp_rows = [[w, p, q] for w, prods in weekly_prod_totals.items()
                          for p, q in prods.items()]
    wp_df = pd.DataFrame(wp_rows, columns=['Week','Product','Quantity'])
    if not wp_df.empty:
        # Pivot: products × weeks for top 10
        top_prods = total_prod_df.head(10)['Product'].tolist()
        wp_pivot = (wp_df[wp_df['Product'].isin(top_prods)]
                    .pivot_table(index='Product', columns='Week',
                                 values='Quantity', aggfunc='sum', fill_value=0))
        st.dataframe(wp_pivot, use_container_width=True)

        # Line chart — top 8
        fig_wp, ax_wp = plt.subplots(figsize=(13, 5))
        for prod in top_prods[:8]:
            prod_data = wp_df[wp_df['Product']==prod].sort_values('Week')
            if prod_data.empty: continue
            ax_wp.plot([str(w.date()) for w in prod_data['Week']],
                       prod_data['Quantity'], marker='o', label=prod)
        ax_wp.set_xlabel("Week"); ax_wp.set_ylabel("Quantity Sold")
        ax_wp.set_title("Weekly Product Trend — Top 8 Products")
        ax_wp.legend(fontsize=8, ncol=2); ax_wp.grid(True, alpha=0.3)
        plt.xticks(rotation=45, ha='right'); plt.tight_layout()
        st.pyplot(fig_wp); plt.close()

    # AI
    with st.spinner("Generating product insight…"):
        ins4, ctx4 = build_product_insight(total_prod_df, biz_perf, wp_df)
    ai_block("products", ctx4, ins4)

    st.divider()

    # ── Geographic Tool ──
    st.subheader("🗺️ Customer & Business Density + Area Analysis")
    req_geo = ['CUSTOMER LATITUDE','CUSTOMER LONGITUDE','BUSINESS LATITUDE','BUSINESS LONGITUDE']
    if not all(c in df4.columns for c in req_geo):
        st.info("Geo columns not found in dataset.")
    else:
        geo4 = df4.dropna(subset=req_geo)
        if geo4.empty:
            st.info("No valid geo data for current filter.")
        else:
            map4_type = st.radio("Map View",
                ["Both","Customer Only","Business Only"], horizontal=True, key="geo4_type")
            center4 = ([geo4['CUSTOMER LATITUDE'].mean(), geo4['CUSTOMER LONGITUDE'].mean()]
                       if city_sel else [-6.8018, 39.2801])
            m4 = folium.Map(location=center4, zoom_start=13)

            if map4_type != "Business Only":
                HeatMap(geo4[['CUSTOMER LATITUDE','CUSTOMER LONGITUDE']].values.tolist(),
                        radius=12, blur=10, name="Customers").add_to(m4)
            if map4_type != "Customer Only":
                HeatMap(geo4[['BUSINESS LATITUDE','BUSINESS LONGITUDE']].values.tolist(),
                        radius=15, blur=12, name="Businesses").add_to(m4)

            rp4 = (geo4.groupby(['BUSINESS NAME','BUSINESS LATITUDE','BUSINESS LONGITUDE'])
                   .agg(Orders=('ID','count'), Sales=('SUBTOTAL','sum'),
                        AvgDT=('Average Delivery Time','mean'))
                   .reset_index().sort_values('Orders', ascending=False))

            # Slider BEFORE building map so value is known before rendering
            top_n4 = st.slider("Top restaurants on map", 5, 50, 20, key="geo4_top")

            for _, r in rp4.head(top_n4).iterrows():
                folium.Marker(
                    [r['BUSINESS LATITUDE'], r['BUSINESS LONGITUDE']],
                    icon=folium.Icon(color='blue', icon='cutlery', prefix='fa'),
                    popup=folium.Popup(
                        f"<b>{r['BUSINESS NAME']}</b><br>"
                        f"Orders: {int(r['Orders'])}<br>"
                        f"Sales: {int(r['Sales']):,} TZS<br>"
                        f"Avg DT: {r['AvgDT']:.1f} min",
                        max_width=200
                    ),
                    tooltip=r['BUSINESS NAME']
                ).add_to(m4)

            Draw(draw_options={"polyline":False,"polygon":True,"circle":False,
                               "rectangle":False,"marker":False,"circlemarker":False},
                 edit_options={"edit":True,"remove":True}).add_to(m4)
            folium.LayerControl().add_to(m4)

            map4_data = st_folium(m4, height=580, width=1200)

            # Polygon area analysis
            if map4_data and map4_data.get("all_drawings"):
                coords = map4_data["all_drawings"][-1]["geometry"]["coordinates"][0]
                poly   = Polygon([(c[1], c[0]) for c in coords])
                geo4 = geo4.copy()
                geo4["in_poly"] = geo4.apply(
                    lambda r: poly.contains(Point(r["CUSTOMER LATITUDE"], r["CUSTOMER LONGITUDE"])), axis=1)
                area_df = geo4[geo4["in_poly"]]

                if not area_df.empty:
                    st.subheader("📍 Selected Area Summary")
                    a1_, a2_, a3_ = st.columns(3)
                    a1_.metric("Orders in Area", f"{len(area_df):,}")
                    a2_.metric("Sales in Area", f"{area_df['SUBTOTAL'].sum()/1e6:.2f}M TZS")
                    a3_.metric("Avg Delivery", f"{area_df['Average Delivery Time'].mean():.1f} min")

                    area_biz = (area_df.groupby("BUSINESS NAME")
                                .agg(Orders=("ID","count"), Sales=("SUBTOTAL","sum"),
                                     AvgDT=("Average Delivery Time","mean"))
                                .reset_index().sort_values("Orders", ascending=False))
                    st.dataframe(area_biz, use_container_width=True)
                    st.download_button("⬇️ Download Area Data",
                                       data=area_df.to_csv(index=False).encode(),
                                       file_name="selected_area.csv", mime="text/csv")

                    # Area AI insight
                    area_ctx = (f"AREA ANALYSIS: {len(area_df):,} orders | "
                                f"{area_df['SUBTOTAL'].sum()/1e6:.2f}M TZS sales | "
                                f"{area_df['Average Delivery Time'].mean():.1f} min avg DT\n\n"
                                f"Top businesses in area:\n{area_biz.head(10).to_string(index=False)}")
                    area_prompt = f"""Senior BI analyst for Tanzanian food delivery.
{area_ctx}
Provide:
1. Zone Health – Is this area well-served?
2. Top Business Performance – Who drives orders/revenue here?
3. Delivery Efficiency – Is avg delivery time acceptable?
4. Growth Opportunity – Should more businesses/riders be deployed here?
5. Action – One specific recommendation.
Use real numbers."""
                    with st.spinner("Analyzing selected area…"):
                        area_ins = claude_insight(area_prompt, 600)
                    ai_block("geo_area", area_ctx, area_ins)
                else:
                    st.warning("No orders inside selected area.")

            # Customer DB table
            st.subheader("📊 Top Customer Locations")
            cust_db = (geo4.groupby(['CUSTOMER LATITUDE','CUSTOMER LONGITUDE'])
                       .agg(Orders=('ID','count'), Sales=('SUBTOTAL','sum'))
                       .reset_index().sort_values('Orders', ascending=False))
            st.dataframe(cust_db.head(20), use_container_width=True)
            st.download_button("⬇️ Download Customer DB",
                               data=excel_bytes(cust_db, "Customers"),
                               file_name="Customer_Locations.xlsx",
                               mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

# ═══════════════════════════════════════════════════════════════
# TAB 5 — PIKI PARTY STORE
# ═══════════════════════════════════════════════════════════════
with tab5:
    st.markdown("""
    <div style="background:linear-gradient(135deg,#ff6b6b,#ffd93d,#6bcb77,#4d96ff);
                padding:20px 24px; border-radius:14px; margin-bottom:20px;">
        <h2 style="color:white;margin:0;text-shadow:1px 1px 3px rgba(0,0,0,0.4);">
            🎉 Piki Party Store — Intelligence Dashboard
        </h2>
        <p style="color:rgba(255,255,255,0.92);margin:6px 0 0 0;font-size:15px;">
            Product trends · Category analysis · Customer insights
        </p>
    </div>
    """, unsafe_allow_html=True)

    # ── Filter to Piki Party only ──
    _pp_df = raw.copy()
    _pp_df['DELIVERY DATE'] = pd.to_datetime(_pp_df['DELIVERY DATE'], errors='coerce')
    _pp_df['DELIVERY TIME'] = pd.to_datetime(_pp_df['DELIVERY TIME'], errors='coerce')
    _pp_df['HOUR'] = _pp_df['DELIVERY TIME'].dt.hour
    _pp_df = _pp_df[_pp_df['HOUR'].isin(OPERATING_HOURS)]

    _pp_df = _pp_df[_pp_df['BUSINESS NAME'].str.strip().str.lower() == 'piki party'].copy()

    if _pp_df.empty:
        st.warning("No 'Piki Party' orders found in the uploaded data. Check that BUSINESS NAME contains 'Piki Party'.")
        st.stop()

    _iso = _pp_df['DELIVERY DATE'].dt.isocalendar()
    _pp_df['ISO_Year'] = _iso.year
    _pp_df['ISO_Week'] = _iso.week

    # ── Load category master ──
    _cat_loaded = False
    _product_category_map = {}
    try:
        _cdf = pd.read_csv("Products Category.csv", encoding='utf-8')
    except Exception:
        try:
            _cdf = pd.read_csv("Products Category.csv", encoding='latin1')
        except Exception:
            _cdf = pd.DataFrame(columns=['Product','Category'])
            st.info("Products Category.csv not found — categories will show as UNCATEGORIZED.")

    if not _cdf.empty:
        _cdf['Product']  = _cdf['Product'].str.strip().str.lower()
        _cdf['Category'] = _cdf['Category'].str.strip()
        _product_category_map = dict(zip(_cdf['Product'], _cdf['Category']))
        _cat_loaded = True

    # ── KPI Summary ──
    _pp_comp = _pp_df[_pp_df['STATE'].isin(['Completed','Delivery Completed By Driver'])]
    _pp_fail = _pp_df[_pp_df['STATE'] == 'Delivery Failed By Driver']
    _pp_rej  = _pp_df[_pp_df['STATE'].str.contains('Reject', na=False)]

    _pk1,_pk2,_pk3,_pk4,_pk5 = st.columns(5)
    _pk1.metric("📦 Total Orders",    f"{len(_pp_df):,}")
    _pk2.metric("✅ Completed",        f"{len(_pp_comp):,}")
    _pk3.metric("❌ Failed",           f"{len(_pp_fail)}")
    _pk4.metric("🚫 Rejected",         f"{len(_pp_rej)}")
    _pk5.metric("💰 Total Sales",      f"{_pp_comp['SUBTOTAL'].sum()/1e6:.2f}M TZS")

    # ── Filters row ──
    st.markdown("---")
    st.markdown("#### 🔎 Filters")
    _pf1,_pf2,_pf3,_pf4 = st.columns(4)

    with _pf1:
        _pp_states = sorted(_pp_df['STATE'].dropna().unique())
        _state_sel = st.multiselect("Order Status", _pp_states, default=_pp_states, key="pp_state")

    with _pf2:
        _all_cats = sorted(set(_product_category_map.values())) if _product_category_map else []
        _cat_sel  = st.multiselect("Category", _all_cats, key="pp_cat")

    with _pf3:
        _pp_date_range = st.date_input("Date Range",
            [_pp_df['DELIVERY DATE'].min().date(), _pp_df['DELIVERY DATE'].max().date()],
            key="pp_dates")

    with _pf4:
        _pp_hour_opt = st.selectbox("Time Period",
            ["All Day","Morning (7-11)","Afternoon (12-16)","Evening (17-22)","Late Night (23-2)"],
            key="pp_hour")

    # Apply filters
    if _state_sel:
        _pp_df = _pp_df[_pp_df['STATE'].isin(_state_sel)]
    if len(_pp_date_range) == 2:
        _pp_df = _pp_df[
            (_pp_df['DELIVERY DATE'] >= pd.to_datetime(_pp_date_range[0])) &
            (_pp_df['DELIVERY DATE'] <= pd.to_datetime(_pp_date_range[1]))]
    if _pp_hour_opt == "Morning (7-11)":
        _pp_df = _pp_df[_pp_df['HOUR'].between(7,11)]
    elif _pp_hour_opt == "Afternoon (12-16)":
        _pp_df = _pp_df[_pp_df['HOUR'].between(12,16)]
    elif _pp_hour_opt == "Evening (17-22)":
        _pp_df = _pp_df[_pp_df['HOUR'].between(17,22)]
    elif _pp_hour_opt == "Late Night (23-2)":
        _pp_df = _pp_df[(_pp_df['HOUR']>=23)|(_pp_df['HOUR']<=2)]

    _pp_comp = _pp_df[_pp_df['STATE'].isin(['Completed','Delivery Completed By Driver'])]

    # ────────────────────────────────────────────────
    # WEEKLY ORDERS & SALES TREND
    # ────────────────────────────────────────────────
    st.markdown("---")
    st.markdown('<div class="section-header">📈 Weekly Orders & Sales Trend</div>', unsafe_allow_html=True)

    _pp_weekly = (_pp_comp.groupby(['ISO_Year','ISO_Week'])
                  .agg(Total_Orders=('ID','count'), Total_Sales=('SUBTOTAL','sum'))
                  .reset_index()
                  .sort_values(['ISO_Year','ISO_Week']))
    _pp_weekly['Week_Label'] = (_pp_weekly['ISO_Year'].astype(str) + "-W"
                                + _pp_weekly['ISO_Week'].astype(str).str.zfill(2))

    if not _pp_weekly.empty:
        _fw, _ax1p = plt.subplots(figsize=(12,5))
        _ax1p.plot(_pp_weekly['Week_Label'], _pp_weekly['Total_Orders'],
                   marker='o', color='#4d96ff', lw=2, label='Orders')
        _ax1p.set_ylabel("Orders", color='#4d96ff'); _ax1p.grid(True, alpha=0.3)
        _ax2p = _ax1p.twinx()
        _ax2p.bar(_pp_weekly['Week_Label'], _pp_weekly['Total_Sales'],
                  alpha=0.3, color='#6bcb77', label='Sales')
        _ax2p.yaxis.set_major_formatter(fmt_millions); _ax2p.set_ylabel("Sales (TZS)")
        _l1,_lb1 = _ax1p.get_legend_handles_labels()
        _l2,_lb2 = _ax2p.get_legend_handles_labels()
        _ax1p.legend(_l1+_l2, _lb1+_lb2, loc='upper left')
        plt.title("Piki Party — Weekly Orders & Sales"); plt.xticks(rotation=35, ha='right')
        plt.tight_layout(); st.pyplot(_fw); plt.close()
        st.dataframe(_pp_weekly[['Week_Label','Total_Orders','Total_Sales']].rename(
            columns={'Week_Label':'Week','Total_Orders':'Orders','Total_Sales':'Sales (TZS)'}),
            use_container_width=True)
    else:
        st.info("No completed orders in selected period.")

    # ────────────────────────────────────────────────
    # PRODUCT ANALYSIS
    # ────────────────────────────────────────────────
    st.markdown("---")
    st.markdown('<div class="section-header">📦 Product & Category Analysis</div>', unsafe_allow_html=True)

    # Build product-week matrix
    _pp_prod_totals = defaultdict(int)
    _pp_wk_prod     = defaultdict(lambda: defaultdict(int))

    for _, _row in _pp_comp.iterrows():
        _wk = int(_row['ISO_Week'])
        for _pn, _qty in extract_products(_row.get('PRODUCTS','')):
            _ps = standardize_product(_pn)
            _pp_prod_totals[_ps]      += _qty
            _pp_wk_prod[_ps][_wk]     += _qty

    if _pp_prod_totals:
        _week_cols_pp = sorted(_pp_weekly['ISO_Week'].unique().astype(int))[-8:]

        _pp_matrix_rows = []
        for _prod, _total in _pp_prod_totals.items():
            _r = {'Product': _prod,
                  'Category': _product_category_map.get(_prod.lower(), 'UNCATEGORIZED')}
            for _w in _week_cols_pp:
                _r[f'W{_w}'] = _pp_wk_prod[_prod].get(_w, 0)
            _r['Total Qty'] = _total
            _pp_matrix_rows.append(_r)

        _pp_matrix = pd.DataFrame(_pp_matrix_rows).sort_values('Total Qty', ascending=False)

        if _cat_sel:
            _pp_matrix = _pp_matrix[_pp_matrix['Category'].isin(_cat_sel)]

        _wcols_disp = [f'W{w}' for w in _week_cols_pp]

        # Display with ❌ for zeros
        _pp_display = _pp_matrix.copy()
        for _c in _wcols_disp:
            _pp_display[_c] = _pp_display[_c].apply(lambda x: "❌" if x==0 else int(x))

        _pt1, _pt2 = st.tabs(["🔥 Top Selling Items", "📊 Category Rankings"])

        with _pt1:
            st.dataframe(_pp_display[['Product','Category']+_wcols_disp+['Total Qty']],
                         use_container_width=True)

        with _pt2:
            _cat_rank = (_pp_matrix.groupby('Category')[_wcols_disp+['Total Qty']]
                         .sum().reset_index().sort_values('Total Qty', ascending=False))
            _cat_rank = _cat_rank[_cat_rank['Category'] != 'UNCATEGORIZED']
            _cat_disp = _cat_rank.copy()
            for _c in _wcols_disp:
                _cat_disp[_c] = _cat_disp[_c].apply(lambda x: "❌" if x==0 else int(x))
            st.dataframe(_cat_disp, use_container_width=True)

        # ── Charts ──
        _vc1, _vc2 = st.columns(2)

        with _vc1:
            st.markdown("##### 🏆 Top 10 Products")
            _top10p = _pp_matrix.head(10)
            _fpt, _apt = plt.subplots(figsize=(6,4))
            _bars = _apt.barh(_top10p['Product'], _top10p['Total Qty'],
                              color=plt.cm.Set3(np.linspace(0,1,len(_top10p))))
            _apt.invert_yaxis(); _apt.set_xlabel("Qty")
            _apt.bar_label(_bars, padding=3, fontsize=8)
            plt.tight_layout(); st.pyplot(_fpt); plt.close()

        with _vc2:
            st.markdown("##### 🥧 Category Share")
            _cat_pie = _pp_matrix.groupby('Category')['Total Qty'].sum().reset_index()
            _cat_pie = _cat_pie[_cat_pie['Category'] != 'UNCATEGORIZED']
            _total_qty = _cat_pie['Total Qty'].sum()
            _major = _cat_pie[_cat_pie['Total Qty']/_total_qty >= 0.015]
            _others_v = _cat_pie[_cat_pie['Total Qty']/_total_qty < 0.015]['Total Qty'].sum()
            if _others_v > 0:
                _major = pd.concat([_major, pd.DataFrame({'Category':['Others'],'Total Qty':[_others_v]})])
            _fpc, _apc = plt.subplots(figsize=(6,4))
            _apc.pie(_major['Total Qty'], labels=_major['Category'],
                     autopct='%1.1f%%', startangle=90,
                     colors=plt.cm.Set3(np.linspace(0,1,len(_major))))
            _apc.axis('equal'); plt.tight_layout(); st.pyplot(_fpc); plt.close()

        # ── Category Trend ──
        st.markdown("##### 📈 Category Weekly Trend")
        if len(_wcols_disp) >= 2 and not _cat_rank.empty:
            _fct, _act = plt.subplots(figsize=(12,4))
            for _, _crow in _cat_rank.iterrows():
                _vals = [_pp_matrix[_pp_matrix['Category']==_crow['Category']][_c].sum()
                         for _c in _wcols_disp]
                _act.plot([c.replace('W','W') for c in _wcols_disp], _vals,
                          marker='o', lw=2, label=_crow['Category'])
            _act.set_xlabel("Week"); _act.set_ylabel("Qty"); _act.grid(True, alpha=0.3)
            _act.legend(fontsize=8, ncol=3); plt.xticks(rotation=30)
            plt.title("Category Volume by Week"); plt.tight_layout()
            st.pyplot(_fct); plt.close()

        # ── WoW Growth ──
        if len(_wcols_disp) >= 2:
            st.markdown("##### 📊 Week-over-Week Category Growth %")
            _last_w, _prev_w = _wcols_disp[-1], _wcols_disp[-2]
            _cat_rank = _cat_rank.copy()
            _cat_rank['WoW %'] = ((_cat_rank[_last_w] - _cat_rank[_prev_w])
                                   / _cat_rank[_prev_w].replace(0, np.nan) * 100).fillna(0)
            _gwow = _cat_rank.sort_values('WoW %', ascending=False)
            _fwow, _awow = plt.subplots(figsize=(10,4))
            _colors_wow = ['#28a745' if v >= 0 else '#dc3545' for v in _gwow['WoW %']]
            _awow.bar(_gwow['Category'], _gwow['WoW %'], color=_colors_wow)
            _awow.axhline(0, color='black', lw=0.8)
            _awow.set_ylabel("Growth %"); _awow.set_title(f"WoW Growth: {_prev_w} → {_last_w}")
            plt.xticks(rotation=35, ha='right'); plt.tight_layout()
            st.pyplot(_fwow); plt.close()

        # ── Growth vs Volume bubble ──
        st.markdown("##### 🫧 Category: Growth Trajectory vs Volume")
        if len(_wcols_disp) >= 3 and not _cat_rank.empty:
            _slopes = []
            for _, _cr in _cat_rank.iterrows():
                _v = [_pp_matrix[_pp_matrix['Category']==_cr['Category']][_c].sum()
                      for _c in _wcols_disp]
                _slopes.append(np.polyfit(range(len(_v)), _v, 1)[0] if sum(_v) > 0 else 0)
            _cat_rank['Slope'] = _slopes
            _fbub, _abub = plt.subplots(figsize=(10,5))
            _abub.scatter(_cat_rank['Total Qty'], _cat_rank['Slope'],
                          s=(_cat_rank['Total Qty']/max(_cat_rank['Total Qty'].max(),1)*800+50),
                          c=plt.cm.Set2(np.linspace(0,1,len(_cat_rank))), alpha=0.8, edgecolors='white', lw=1.5)
            for _, _cr in _cat_rank.iterrows():
                _abub.annotate(_cr['Category'], (_cr['Total Qty'], _cr['Slope']),
                               fontsize=8, ha='center', va='bottom')
            _abub.axhline(0, color='gray', lw=1, linestyle='--')
            _abub.set_xlabel("Total Volume"); _abub.set_ylabel("Trend (slope)")
            _abub.set_title("Growth Trajectory vs Volume — bigger bubble = more volume")
            plt.tight_layout(); st.pyplot(_fbub); plt.close()

    else:
        st.info("No product data could be extracted from PRODUCTS column.")

    # ────────────────────────────────────────────────
    # TOP ORDERS BY VALUE
    # ────────────────────────────────────────────────
    st.markdown("---")
    st.markdown('<div class="section-header">💰 Top Orders by Value</div>', unsafe_allow_html=True)

    _top_ord = _pp_comp.sort_values('SUBTOTAL', ascending=False).copy()
    _top_ord['Order Date']       = _top_ord['DELIVERY DATE'].dt.date
    _top_ord['Products Ordered'] = _top_ord['PRODUCTS'].apply(format_products_clean)
    _top_ord_view = _top_ord[['ID','Order Date','CUSTOMER NAME','Products Ordered','SUBTOTAL']].head(20)
    _top_ord_view = _top_ord_view.rename(columns={'ID':'Order ID','CUSTOMER NAME':'Customer',
                                                   'SUBTOTAL':'Value (TZS)'})
    st.dataframe(_top_ord_view, use_container_width=True)

    # ────────────────────────────────────────────────
    # AI INSIGHT
    # ────────────────────────────────────────────────
    st.markdown("---")
    if not _pp_weekly.empty and _pp_prod_totals:
        _top5_str = pd.DataFrame(_pp_prod_totals.items(), columns=['Product','Qty'])                      .sort_values('Qty', ascending=False).head(10).to_string(index=False)
        _pp_ctx = (f"PIKI PARTY STORE ANALYSIS\n"
                   f"Total completed orders: {len(_pp_comp):,}\n"
                   f"Total sales: {_pp_comp['SUBTOTAL'].sum()/1e6:.2f}M TZS\n"
                   f"Weeks available: {len(_pp_weekly)}\n\n"
                   f"TOP 10 PRODUCTS:\n{_top5_str}\n\n"
                   f"WEEKLY TREND (last 4 weeks):\n"
                   + _pp_weekly.tail(4)[['Week_Label','Total_Orders','Total_Sales']].to_string(index=False))
        _pp_prompt = (
            "You are a senior BI analyst for Piki, a Tanzanian food delivery company.\n"
            "You are analysing the Piki Party Store — a specialty party supply/catering store.\n\n"
            + _pp_ctx + "\n\n"
            "Provide a comprehensive analysis:\n"
            "1. **Store Performance** — Is Piki Party growing? Key trend observation.\n"
            "2. **Star Products** — Which products drive the most volume and why does it matter?\n"
            "3. **Category Health** — Any category growing or declining noticeably?\n"
            "4. **Customer Behaviour** — What does the order value distribution tell us?\n"
            "5. **Strategic Actions** — 3 specific recommendations to grow Piki Party sales.\n\n"
            "Be specific, use real numbers, write as a strategic advisor."
        )
        with st.spinner("Generating Piki Party insight…"):
            _pp_ins = claude_insight(_pp_prompt, max_tokens=900)
        ai_block("piki_party", _pp_ctx, _pp_ins)
    else:
        st.info("Upload more data to generate AI insights for Piki Party.")

    # ────────────────────────────────────────────────
    # DOWNLOADS
    # ────────────────────────────────────────────────
    st.markdown("---")
    st.markdown('<div class="section-header">⬇️ Export Reports</div>', unsafe_allow_html=True)

    if _pp_prod_totals:
        _dl1, _dl2 = st.columns(2)

        _exp_buf1 = io.BytesIO()
        with pd.ExcelWriter(_exp_buf1, engine='xlsxwriter') as _ew:
            _pp_display.to_excel(_ew, sheet_name='Top Items', index=False)
            if not _cat_rank.empty:
                _cat_disp.to_excel(_ew, sheet_name='Category Ranking', index=False)
            _top_ord_view.to_excel(_ew, sheet_name='Top Orders by Value', index=False)

        _dl1.download_button("⬇️ Filtered Results (Excel)",
                             data=_exp_buf1.getvalue(),
                             file_name="Piki_Party_Filtered.xlsx",
                             mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

        _exp_buf2 = io.BytesIO()
        with pd.ExcelWriter(_exp_buf2, engine='xlsxwriter') as _ew2:
            if not _cat_rank.empty:
                _cat_disp.to_excel(_ew2, sheet_name='CATEGORY_RANKING', index=False)
            for _cname in (_cat_rank['Category'].unique() if not _cat_rank.empty else []):
                _csheet = _pp_matrix[_pp_matrix['Category']==_cname].sort_values('Total Qty', ascending=False)
                _csheet.to_excel(_ew2, sheet_name=str(_cname)[:31], index=False)

        _dl2.download_button("⬇️ Full Category Report (All Sheets)",
                             data=_exp_buf2.getvalue(),
                             file_name="Piki_Party_Full_Report.xlsx",
                             mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")

# ─────────────────────────────────────────────────
# FOOTER
# ─────────────────────────────────────────────────
st.divider()
st.caption("Piki Business Intelligence Dashboard · Built with Streamlit & Claude AI · Tanzania 🇹🇿")
