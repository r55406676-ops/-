# -#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
iPhone Deals Bot — Telegram-бот, який шукає iPhone дешевше за ринок.

Джерела:  OLX (без ключів)  +  eBay (опційно, якщо задані EBAY_CLIENT_ID / EBAY_CLIENT_SECRET)
«Ринок»:  медіана цін схожих оголошень (модель + пам'ять + стан) за останні 14 днів.
Запуск:   9122853889:AAEnuXtgUxzEwhCpB6X4bUoZ9Bfe7fndBuc
=... python main.py
"""
from __future__ import annotations

import asyncio
import html
import json
import logging
import os
import random
import re
import sqlite3
import statistics
import time
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, timezone

import httpx
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, ReplyKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.ext import Application, CommandHandler, ContextTypes, MessageHandler, filters

log = logging.getLogger("iphone-bot")

# ═════════════════════ Налаштування (змінні середовища) ═════════════════════
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
OWNER_ID = os.getenv("OWNER_ID", "").strip()              # твій Telegram ID (бажано)
DATA_DIR = os.getenv("DATA_DIR", ".")                      # куди писати базу (змонтуй Volume)
PROXY_URL = os.getenv("PROXY_URL", "").strip() or None     # http://user:pass@host:port
PAGES_PER_QUERY = max(1, int(os.getenv("PAGES_PER_QUERY", "3")))

OLX_BASE = os.getenv("OLX_BASE", "https://www.olx.ua").rstrip("/")
OLX_CURRENCY = os.getenv("OLX_CURRENCY", "UAH").upper()
OLX_CATEGORY_ID = os.getenv("OLX_CATEGORY_ID", "").strip()  # необов'язково: відсікає аксесуари
OLX_MIN_PRICE = float(os.getenv("OLX_MIN_PRICE", "1500"))

EBAY_CLIENT_ID = os.getenv("EBAY_CLIENT_ID", "").strip()
EBAY_CLIENT_SECRET = os.getenv("EBAY_CLIENT_SECRET", "").strip()
EBAY_MARKETPLACE = os.getenv("EBAY_MARKETPLACE", "EBAY_US").strip()
EBAY_MIN_PRICE = float(os.getenv("EBAY_MIN_PRICE", "40"))

# Значення за замовчуванням (потім міняються командами в боті)
DEFAULTS = {
    "queries": ["iphone 12", "iphone 13", "iphone 14", "iphone 15", "iphone 16"],
    "discount": 20,   # мінімальна знижка від ринку, %
    "interval": 15,   # хвилин між автосканами
    "auto": 1,        # автопошук увімкнений
}
MIN_SAMPLES = 5            # скільки схожих оголошень треба, щоб оцінити ринок
MARKET_DAYS = 14           # за який період рахуємо ринок
MAX_ALERTS_PER_RUN = 8     # максимум карток за один автоскан
SUSPICIOUS_DISCOUNT = 35   # від цієї знижки — позначка ⚠️ (часто шахрайство)
MIN_PRICE_RATIO = 0.40     # дешевше 40% від ринку — ігноруємо (запчастини/обман)

SYMBOLS = {"UAH": "₴", "USD": "$", "EUR": "€", "PLN": "zł", "GBP": "£"}
FX = {"USD": 41.5, "EUR": 48.0}   # запасний курс; оновлюється з НБУ
_fx_ts = 0.0

BASE_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Safari/537.36",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "uk-UA,uk;q=0.9,en;q=0.8",
}

RAW: Counter = Counter()        # скільки оголошень віддали сайти (за скан)
REJECTED: Counter = Counter()   # чому відсіяли (за скан)


# ═════════════════════ Моделі даних ═════════════════════
@dataclass
class Listing:
    uid: str
    source: str
    title: str
    price: float          # у базовій валюті джерела
    currency: str
    url: str
    model: str            # "13 pro", "xr", "se 2022" ...
    storage: int          # ГБ
    state: str            # new / used / refurb
    location: str = ""
    photo: str = ""
    posted: str = ""
    orig: str = ""        # ціна в оригінальній валюті, якщо конвертували

    @property
    def group(self) -> str:
        return f"{self.source}|{self.currency}|{self.model}|{self.storage}|{self.state}"


@dataclass
class Deal:
    listing: Listing
    market: float
    n: int
    discount: float


@dataclass
class Report:
    raw: int = 0
    parsed: int = 0
    ready: int = 0
    thin: int = 0
    deals: list = field(default_factory=list)
    errors: list = field(default_factory=list)
    rejected: Counter = field(default_factory=Counter)


# ═════════════════════ Розбір назв: модель, пам'ять, стан, дефекти ═════════════════════
_CYR = [
    (r"[іi]phone", "iphone"),
    (r"\b(?:айфон|іфон|ифон)\w*", "iphone"),
    (r"\bпро\s*макс\b", "pro max"),
    (r"\bпро\b", "pro"),
    (r"\bмакс\b", "max"),
    (r"\bплюс\b", "plus"),
    (r"\b(?:міні|мини)\b", "mini"),
    (r"\b(?:аїр|аир|эйр|ейр)\b", "air"),
    (r"(?<=\d)\s*(?:гб|гигабайт\w*|гігабайт\w*)\b", "gb"),
    (r"\bгб\b", "gb"),
    (r"(?<=\d)\s*тб\b", "tb"),
]
STORAGES = {16, 32, 64, 128, 256, 512, 1024, 2048}
BARE_STORAGES = {64, 128, 256, 512}   # числа без «GB» у назві, яким віримо

ACCESSORY_RE = re.compile(
    r"^\W*(?:чохо?л|чехо?л|case|скло|стекл|плівк|пленк|захисн|кабел|зарядк|зарядн|адаптер|навушн|"
    r"дисплей|екран|корпус|акумулятор|аккумулятор|батаре|шлейф|материнськ|плата|"
    r"куплю|скуплю|викуп|выкуп)"
    r"|\b(?:для|for)\s+(?:apple\s+)?iphone"
)
FAKE_RE = re.compile(r"муляж|макет\b|dummy|replica|реплік|реплик|\bкопі|\bкопия|\bcopy\b|\bhdc\b")
_NEG = r"(?<!не)(?<!не )(?<!без )(?<!нет )(?<!ні )"
DEFECT_RE = re.compile(
    _NEG + r"(?:запчаст|на розбір|на разбор|розборк|разборк|донор|залочен|заблокован|activation lock|"
    r"icloud lock|блок активац|не працю|не работа|не вмика|не включа|не заряджа|не заряжа|мертв|утопл|"
    r"розбит|разбит|битий|битый|без дисплея|без экрана|без екрана|на ремонт|потребує ремонт|требует ремонт)"
)
DEFECT_EN_RE = re.compile(
    r"for parts|parts only|not working|broken|cracked|damaged|icloud lock|activation lock|"
    r"blacklist|bad esn|\blocked\b|faulty|read desc|case only|screen only"
)


def norm(text: str) -> str:
    t = (text or "").lower().replace("ё", "е")
    for pat, rep in _CYR:
        t = re.sub(pat, rep, t)
    return re.sub(r"pro\s*max", "pro max", t)


def strip_html(s: str) -> str:
    s = re.sub(r"<[^>]+>", " ", s or "")
    return re.sub(r"\s+", " ", html.unescape(s)).strip()


def rej(reason: str):
    REJECTED[reason] += 1
    return None


def parse_model(title: str):
    """Повертає (модель, решта токенів) або None. «iPhone 13 Pro Max 256» -> ("13 pro max", ["256"])."""
    t = norm(title)
    m = re.search(r"iphone", t)
    if not m:
        return None
    toks = re.findall(r"[a-z]+|\d+", t[m.end(): m.end() + 45])
    if not toks:
        return None
    first, rest = toks[0], toks[1:]
    if first.isdigit():
        n = int(first)
        if not 6 <= n <= 25:
            return None
        model = str(n)
        if n <= 8 and rest[:1] == ["s"]:
            model, rest = model + "s", rest[1:]
        if rest[:2] == ["pro", "max"] and n >= 11:
            model, rest = model + " pro max", rest[2:]
        elif rest[:1] == ["pro"] and n >= 11:
            model, rest = model + " pro", rest[1:]
        elif rest[:1] in (["plus"], ["mini"], ["air"]):
            model, rest = model + " " + rest[0], rest[1:]
        elif rest[:1] == ["max"] and n >= 11:
            model, rest = model + " pro max", rest[1:]
        elif rest[:1] == ["e"] and n >= 16:
            model, rest = model + "e", rest[1:]
        if rest[:1] and rest[0].isdigit():            # «iphone 11 12» — незрозуміло яка модель
            n2 = int(rest[0])
            if 6 <= n2 <= 25 and n2 not in STORAGES and rest[1:2] not in (["gb"], ["tb"]):
                return None
        return model, rest
    if first in ("x", "xr"):
        return first, rest
    if first == "xs":
        return ("xs max", rest[1:]) if rest[:1] == ["max"] else ("xs", rest)
    if first == "air":
        return "air", rest
    if first == "se":
        gen = {"2": "2020", "3": "2022", "2016": "2016", "2020": "2020", "2022": "2022"}
        y = gen.get(rest[0]) if rest else None
        return (f"se {y}", rest[1:]) if y else ("se", rest)
    return None


def _storages_in(t: str) -> set:
    vals = set()
    for num, unit in re.findall(r"(?<![\d.])(\d{1,4})\s*(gb|tb)\b", t):
        v = int(num) * (1024 if unit == "tb" else 1)
        if v in STORAGES:
            vals.add(v)
    return vals


def parse_storage(title: str, rest: list, desc: str):
    vals = _storages_in(norm(title))
    if len(vals) == 1:
        return vals.pop()
    if len(vals) > 1:                                  # «128/256 GB» — не знаємо яка
        return None
    for tok in rest[:3]:
        if tok.isdigit() and int(tok) in BARE_STORAGES:
            return int(tok)
    vals = _storages_in(norm(desc[:500]))
    return vals.pop() if len(vals) == 1 else None


def infer_state(site_state, title: str) -> str:
    t = norm(title)
    if re.search(r"refurb|відновлен|восстановлен", t):
        return "refurb"
    if site_state in ("new", "used"):
        return site_state
    if re.search(r"sealed|запакован|запечатан|неактивован|не активован", t):
        return "new"
    return "used"


# ═════════════════════ Валюти ═════════════════════
async def refresh_fx(client) -> None:
    """Курс НБУ — щоб порівнювати оголошення в $ та ₴ між собою."""
    global _fx_ts
    if OLX_CURRENCY != "UAH" or time.time() - _fx_ts < 6 * 3600:
        return
    try:
        r = await client.get("https://bank.gov.ua/NBUStatService/v1/statdirectory/exchange?json")
        r.raise_for_status()
        for row in r.json():
            if row.get("cc") in FX:
                FX[row["cc"]] = float(row["rate"])
        _fx_ts = time.time()
    except Exception as e:
        log.warning("Курс НБУ не оновлено: %s", e)
        _fx_ts = time.time() - 5 * 3600     # спробуємо ще раз за годину


def to_base(value: float, cur: str, base: str):
    if cur == base:
        return value
    if base == "UAH" and cur in FX:
        return value * FX[cur]
    return None


# ═════════════════════ Джерела ═════════════════════
def parse_olx_offer(ad: dict):
    title = str(ad.get("title") or "").strip()
    desc = strip_html(ad.get("description") or "")
    if ad.get("status") not in (None, "active"):
        return rej("неактивні")
    nt = norm(title)
    if ACCESSORY_RE.search(nt) or FAKE_RE.search(nt):
        return rej("аксесуари/копії")
    if DEFECT_RE.search(norm(title + " " + desc[:600])):
        return rej("дефекти/запчастини")
    pm = parse_model(title)
    if not pm:
        return rej("без моделі")
    model, rest = pm
    storage = parse_storage(title, rest, desc)
    if not storage:
        return rej("без об'єму пам'яті")

    price, cur, site_state = None, "", None
    for p in ad.get("params") or []:
        v = p.get("value")
        if not isinstance(v, dict):
            continue
        if p.get("key") == "price":
            price, cur = v.get("value"), str(v.get("currency") or "").upper()
        elif p.get("key") == "state":
            site_state = v.get("key")
    if not isinstance(price, (int, float)) or price <= 0:
        return rej("без ціни")
    base = to_base(float(price), cur, OLX_CURRENCY)
    if base is None:
        return rej("інша валюта")
    if base < OLX_MIN_PRICE:
        return rej("надто дешеві")

    loc = ad.get("location") or {}
    city = ((loc.get("city") or {}).get("name")) or ((loc.get("region") or {}).get("name")) or ""
    photo = ""
    photos = ad.get("photos") or []
    if photos and isinstance(photos[0], dict):
        photo = str(photos[0].get("link") or "").replace("{width}", "800").replace("{height}", "600")
    orig = "" if cur == OLX_CURRENCY else f"{price:,.0f} {SYMBOLS.get(cur, cur)}".replace(",", "\u202f")
    return Listing(
        uid=f"olx:{ad.get('id')}", source="OLX", title=title, price=base, currency=OLX_CURRENCY,
        url=str(ad.get("url") or ""), model=model, storage=storage,
        state=infer_state(site_state, title), location=city, photo=photo,
        posted=str(ad.get("created_time") or ""), orig=orig,
    )


class OLX:
    name = "OLX"

    async def search(self, client, query: str) -> list:
        out = []
        for page in range(PAGES_PER_QUERY):
            params = {"offset": page * 50, "limit": 50, "query": query, "sort_by": "created_at:desc"}
            if OLX_CATEGORY_ID:
                params["category_id"] = OLX_CATEGORY_ID
            r = await client.get(f"{OLX_BASE}/api/v1/offers/", params=params)
            if r.status_code != 200:
                raise RuntimeError(f"HTTP {r.status_code}")
            data = (r.json() or {}).get("data") or []
            RAW[self.name] += len(data)
            for ad in data:
                li = parse_olx_offer(ad)
                if li:
                    out.append(li)
            if len(data) < 50:
                break
            await asyncio.sleep(random.uniform(0.8, 1.6))
        return out


def parse_ebay_item(it: dict):
    title = str(it.get("title") or "").strip()
    nt = norm(title)
    if ACCESSORY_RE.search(nt) or FAKE_RE.search(nt) or DEFECT_EN_RE.search(nt):
        return rej("аксесуари/дефекти")
    cid = str(it.get("conditionId") or "")
    if cid == "7000" or "parts" in str(it.get("condition") or "").lower():
        return rej("на запчастини")
    pm = parse_model(title)
    if not pm:
        return rej("без моделі")
    model, rest = pm
    storage = parse_storage(title, rest, "")
    if not storage:
        return rej("без об'єму пам'яті")
    pr = it.get("price") or {}
    try:
        price = float(pr.get("value"))
    except (TypeError, ValueError):
        return rej("без ціни")
    cur = str(pr.get("currency") or "USD").upper()
    if price < EBAY_MIN_PRICE:
        return rej("надто дешеві")
    state = "new" if cid in ("1000", "1500") else "refurb" if cid.startswith("2") else "used"
    return Listing(
        uid=f"ebay:{it.get('itemId')}", source="eBay", title=title, price=price, currency=cur,
        url=str(it.get("itemWebUrl") or ""), model=model, storage=storage, state=state,
        location=str((it.get("itemLocation") or {}).get("country") or ""),
        photo=str((it.get("image") or {}).get("imageUrl") or ""),
        posted=str(it.get("itemCreationDate") or ""),
    )


class Ebay:
    name = "eBay"

    def __init__(self):
        self._token, self._exp = "", 0.0

    async def _auth(self, client) -> str:
        if self._token and time.time() < self._exp - 120:
            return self._token
        r = await client.post(
            "https://api.ebay.com/identity/v1/oauth2/token",
            auth=(EBAY_CLIENT_ID, EBAY_CLIENT_SECRET),
            data={"grant_type": "client_credentials", "scope": "https://api.ebay.com/oauth/api_scope"},
        )
        if r.status_code != 200:
            raise RuntimeError(f"eBay auth HTTP {r.status_code}")
        j = r.json()
        self._token, self._exp = j["access_token"], time.time() + int(j.get("expires_in", 7200))
        return self._token

    async def search(self, client, query: str) -> list:
        token = await self._auth(client)
        headers = {"Authorization": f"Bearer {token}", "X-EBAY-C-MARKETPLACE-ID": EBAY_MARKETPLACE}
        out = []
        for page in range(PAGES_PER_QUERY):
            params = {"q": query, "category_ids": "9355", "limit": "100", "offset": str(page * 100),
                      "sort": "newlyListed", "filter": "buyingOptions:{FIXED_PRICE}"}
            r = await client.get("https://api.ebay.com/buy/browse/v1/item_summary/search",
                                 params=params, headers=headers)
            if r.status_code != 200:
                raise RuntimeError(f"eBay HTTP {r.status_code}")
            items = (r.json() or {}).get("itemSummaries") or []
            RAW[self.name] += len(items)
            for it in items:
                li = parse_ebay_item(it)
                if li:
                    out.append(li)
            if len(items) < 100:
                break
            await asyncio.sleep(random.uniform(0.5, 1.0))
        return out


SOURCES = [OLX()] + ([Ebay()] if EBAY_CLIENT_ID and EBAY_CLIENT_SECRET else [])


# ═════════════════════ База даних ═════════════════════
SCHEMA = """
CREATE TABLE IF NOT EXISTS kv (k TEXT PRIMARY KEY, v TEXT);
CREATE TABLE IF NOT EXISTS items (
  uid TEXT PRIMARY KEY, grp TEXT, price REAL, title TEXT, url TEXT,
  first_seen REAL, last_seen REAL, alerted INTEGER DEFAULT 0
);
CREATE INDEX IF NOT EXISTS idx_items_grp ON items(grp, last_seen);
"""


def market_price(prices: list):
    """Медіана без викидів. None, якщо даних замало."""
    if len(prices) < MIN_SAMPLES:
        return None
    m1 = statistics.median(prices)
    clean = [p for p in prices if 0.5 * m1 <= p <= 1.8 * m1]
    if len(clean) < MIN_SAMPLES:
        return None
    return statistics.median(clean), len(clean)


class DB:
    def __init__(self, path: str):
        self.c = sqlite3.connect(path)
        self.c.executescript(SCHEMA)

    def get(self, key: str, default=None):
        r = self.c.execute("SELECT v FROM kv WHERE k=?", (key,)).fetchone()
        return json.loads(r[0]) if r else default

    def set(self, key: str, value) -> None:
        self.c.execute(
            "INSERT INTO kv(k, v) VALUES(?, ?) ON CONFLICT(k) DO UPDATE SET v=excluded.v",
            (key, json.dumps(value, ensure_ascii=False)),
        )
        self.c.commit()

    def upsert_many(self, listings, now: float) -> None:
        for li in listings:
            self.c.execute(
                """INSERT INTO items(uid, grp, price, title, url, first_seen, last_seen, alerted)
                   VALUES(?, ?, ?, ?, ?, ?, ?, 0)
                   ON CONFLICT(uid) DO UPDATE SET
                     alerted = CASE WHEN excluded.price < items.price * 0.9 THEN 0 ELSE items.alerted END,
                     price = excluded.price, title = excluded.title, url = excluded.url,
                     grp = excluded.grp, last_seen = excluded.last_seen""",
                (li.uid, li.group, li.price, li.title, li.url, now, now),
            )
        self.c.commit()

    def markets(self, now: float) -> dict:
        prices: dict = {}
        for g, p in self.c.execute("SELECT grp, price FROM items WHERE last_seen >= ?",
                                   (now - MARKET_DAYS * 86400,)):
            prices.setdefault(g, []).append(p)
        return {g: market_price(v) for g, v in prices.items()}

    def alerted(self, uid: str) -> bool:
        r = self.c.execute("SELECT alerted FROM items WHERE uid=?", (uid,)).fetchone()
        return bool(r and r[0])

    def mark_alerted(self, uid: str) -> None:
        self.c.execute("UPDATE items SET alerted=1 WHERE uid=?", (uid,))
        self.c.commit()

    def cleanup(self, now: float) -> None:
        self.c.execute("DELETE FROM items WHERE last_seen < ?", (now - 30 * 86400,))
        self.c.commit()

    def reset_items(self) -> None:
        self.c.execute("DELETE FROM items")
        self.c.commit()


def get_settings(db: DB) -> dict:
    s = {k: (list(v) if isinstance(v, list) else v) for k, v in DEFAULTS.items()}
    for k in s:
        v = db.get("s_" + k)
        if v is not None:
            s[k] = v
    return s


def get_owner(db: DB):
    if OWNER_ID.isdigit():
        return int(OWNER_ID)
    v = db.get("owner")
    return int(v) if v else None


# ═════════════════════ Скан і пошук вигідних пропозицій ═════════════════════
async def run_scan(app) -> Report:
    db: DB = app.bot_data["db"]
    s = get_settings(db)
    now = time.time()
    db.set("last_scan", now)          # навіть якщо скан впаде — повторимо через інтервал, а не щосекунди
    RAW.clear()
    REJECTED.clear()
    rep = Report()
    found: dict = {}

    async with httpx.AsyncClient(proxy=PROXY_URL, timeout=httpx.Timeout(25.0),
                                 headers=BASE_HEADERS, follow_redirects=True) as client:
        await refresh_fx(client)
        for src in SOURCES:
            fails = 0
            for q in s["queries"]:
                try:
                    for li in await src.search(client, q):
                        found[li.uid] = li
                    fails = 0
                except Exception as e:
                    fails += 1
                    rep.errors.append(f"{src.name} «{q}»: {str(e)[:60] or type(e).__name__}")
                    if fails >= 2:     # два збої поспіль — далі не мучимо
                        break
                await asyncio.sleep(random.uniform(0.8, 1.6))

    db.upsert_many(found.values(), now)
    markets = db.markets(now)
    for li in found.values():
        mk = markets.get(li.group)
        if not mk:
            continue
        med, n = mk
        disc = (1 - li.price / med) * 100
        if disc >= s["discount"] and li.price >= med * MIN_PRICE_RATIO:
            rep.deals.append(Deal(li, med, n, disc))
    groups = {li.group for li in found.values()}
    rep.ready = sum(1 for g in groups if markets.get(g))
    rep.thin = len(groups) - rep.ready
    rep.raw, rep.parsed, rep.rejected = sum(RAW.values()), len(found), Counter(REJECTED)
    # спершу «правдоподібні» знижки, підозріло дешеві — в кінець
    rep.deals.sort(key=lambda d: (d.discount >= SUSPICIOUS_DISCOUNT, -d.discount))
    db.cleanup(now)
    return rep


# ═════════════════════ Оформлення повідомлень ═════════════════════
STATE_UA = {"new": "новий", "used": "вживаний", "refurb": "відновлений"}


def esc(s) -> str:
    return html.escape(str(s), quote=False)


def fmt_price(v: float, cur: str) -> str:
    return f"{v:,.0f}".replace(",", "\u202f") + " " + SYMBOLS.get(cur, cur)


def pretty_model(model: str) -> str:
    words = [w.upper() if w in ("x", "xs", "xr", "se") else w.capitalize() for w in model.split()]
    return "iPhone " + " ".join(words)


def pretty_name(model: str, storage: int, state: str) -> str:
    st = f"{storage // 1024} TB" if storage >= 1024 else f"{storage} GB"
    return f"{pretty_model(model)} {st}, {STATE_UA.get(state, state)}"


def ago(iso: str) -> str:
    if not iso:
        return ""
    try:
        dt = datetime.fromisoformat(iso.replace("Z", "+00:00"))
    except ValueError:
        return ""
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    mins = int((datetime.now(timezone.utc) - dt).total_seconds() // 60)
    if mins < 2:
        return "щойно"
    if mins < 60:
        return f"{mins} хв тому"
    if mins < 1440:
        return f"{mins // 60} год тому"
    return f"{mins // 1440} дн тому"


def format_deal(d: Deal) -> str:
    li = d.listing
    plausible = d.discount < SUSPICIOUS_DISCOUNT
    price_line = f"💰 <b>{fmt_price(li.price, li.currency)}</b>"
    if li.orig:
        price_line += f" ({esc(li.orig)})"
    price_line += f" · ринок ≈ {fmt_price(d.market, li.currency)} (n={d.n})"
    meta = " · ".join(x for x in (li.location, li.source, ago(li.posted)) if x)
    lines = [
        f"{'🔥' if plausible else '⚠️'} <b>−{d.discount:.0f}%</b> · {esc(pretty_name(li.model, li.storage, li.state))}",
        price_line,
        f"📍 {esc(meta)}",
        f"<i>{esc(li.title[:110])}</i>",
    ]
    if not plausible:
        lines.append("⚠️ Підозріло дешево: перевір продавця, не плати наперед.")
    return "\n".join(lines)


async def send_deal(bot, chat_id: int, d: Deal) -> None:
    text = format_deal(d)
    kb = None
    if d.listing.url.startswith("http"):
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("Відкрити оголошення ↗", url=d.listing.url)]])
    if d.listing.photo:
        try:
            await bot.send_photo(chat_id, d.listing.photo, caption=text,
                                 parse_mode=ParseMode.HTML, reply_markup=kb)
            return
        except Exception as e:
            log.info("Фото не відправилось (%s), шлю текстом", e)
    await bot.send_message(chat_id, text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def push_deals(bot, chat_id: int, deals: list, db: DB, only_new: bool, limit: int) -> int:
    sent = 0
    for d in deals:
        if only_new and db.alerted(d.listing.uid):
            continue
        try:
            await send_deal(bot, chat_id, d)
        except Exception as e:
            log.warning("Не вдалося надіслати: %s", e)
            continue
        db.mark_alerted(d.listing.uid)
        sent += 1
        if sent >= limit:
            break
        await asyncio.sleep(0.6)
    return sent


def summary(rep: Report, shown: int, discount: int) -> str:
    head = "⚠️ Скан із помилками" if rep.errors and not rep.parsed else "✅ Готово"
    out = [f"{head}: переглянуто {rep.raw} оголошень, підходящих {rep.parsed}."]
    if rep.deals:
        out.append(f"🔥 Вигідних (−{discount}%+): {len(rep.deals)}"
                   + (f", показано {shown}" if shown < len(rep.deals) else ""))
    elif rep.ready:
        out.append(f"Нічого дешевшого за ринок на {discount}%+ зараз немає.")
    if rep.thin:
        out.append(f"ℹ️ У {rep.thin} групах ще мало даних для оцінки ринку "
                   f"(треба ≥{MIN_SAMPLES} схожих) — бот накопичує статистику.")
    if rep.rejected:
        out.append("Відсіяно: " + ", ".join(f"{k} {v}" for k, v in rep.rejected.most_common(4)))
    if rep.errors:
        out.append("⚠️ " + "; ".join(rep.errors[:3]))
        if any(x in e for e in rep.errors for x in ("403", "429")):
            out.append("Схоже, сайт блокує IP хостингу — додай PROXY_URL (див. README).")
    return "\n".join(out)


# ═════════════════════ Telegram: команди ═════════════════════
KEYBOARD = ReplyKeyboardMarkup(
    [["🔎 Скан", "📊 Ринок"], ["🔔 Авто", "⚙️ Налаштування"]], resize_keyboard=True
)


def _db(context) -> DB:
    return context.application.bot_data["db"]


async def guard(update: Update, context) -> bool:
    user, msg = update.effective_user, update.effective_message
    if not user or not msg:
        return False
    owner = get_owner(_db(context))
    if owner is None:
        await msg.reply_text("Натисни /start, щоб зареєструватись як власник бота.")
        return False
    if user.id != owner:
        await msg.reply_text("🔒 Це приватний бот.")
        return False
    return True


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    db, user, msg = _db(context), update.effective_user, update.effective_message
    owner = get_owner(db)
    if owner is None:
        db.set("owner", user.id)
        owner = user.id
    if user.id != owner:
        await msg.reply_text("🔒 Це приватний бот.")
        return
    s = get_settings(db)
    text = (
        "👋 <b>iPhone Deals Bot</b>\n"
        f"Шукаю iPhone дешевше за ринок ({', '.join(x.name for x in SOURCES)}) і шлю сюди.\n"
        f"Автопошук: {'увімкнено' if s['auto'] else 'вимкнено'}, кожні {s['interval']} хв.\n\n"
        "🔎 <b>Скан</b> — перевірити зараз\n"
        "📊 <b>Ринок</b> — поточні ринкові ціни\n"
        "🔔 <b>Авто</b> — вкл/викл пошук у фоні\n"
        "⚙️ <b>Налаштування</b>\n\n"
        "/models 13, 14 pro — які моделі шукати\n"
        "/discount 25 — мін. знижка від ринку, %\n"
        "/interval 10 — як часто сканувати, хв (від 5)\n"
        "/market 13 — ціни ринку по моделі\n"
        "/reset — очистити базу оголошень"
    )
    if not OWNER_ID:
        text += (f"\n\nТвій Telegram ID: <code>{user.id}</code>. Додай його у змінну OWNER_ID на хостингу, "
                 "щоб бот не втратив власника після перезапуску.")
    await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=KEYBOARD)


async def cmd_scan(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await guard(update, context):
        return
    app, msg, db = context.application, update.effective_message, _db(context)
    lock = app.bot_data["lock"]
    if lock.locked():
        await msg.reply_text("⏳ Скан уже триває, зачекай хвилинку.")
        return
    await msg.reply_text("⏳ Шукаю… (зазвичай 30–60 секунд)")
    async with lock:
        rep = await run_scan(app)
    shown = await push_deals(context.bot, update.effective_chat.id, rep.deals, db, only_new=False, limit=10)
    await msg.reply_text(summary(rep, shown, get_settings(db)["discount"]))


async def cmd_auto(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await guard(update, context):
        return
    db, args = _db(context), [a.lower() for a in (context.args or [])]
    cur = get_settings(db)["auto"]
    new = 1 if args[:1] == ["on"] else 0 if args[:1] == ["off"] else (0 if cur else 1)
    db.set("s_auto", new)
    await update.effective_message.reply_text("🔔 Автопошук увімкнено" if new else "🔕 Автопошук вимкнено")


async def cmd_settings(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await guard(update, context):
        return
    db = _db(context)
    s = get_settings(db)
    last = float(db.get("last_scan", 0) or 0)
    last_txt = f"{int((time.time() - last) // 60)} хв тому" if last else "ще не було"
    await update.effective_message.reply_text(
        "⚙️ <b>Налаштування</b>\n"
        f"Моделі: {esc(', '.join(s['queries']))}\n"
        f"Знижка від ринку: від {s['discount']}%\n"
        f"Інтервал: {s['interval']} хв · Авто: {'так' if s['auto'] else 'ні'}\n"
        f"Джерела: {esc(', '.join(x.name for x in SOURCES))}\n"
        f"Останній скан: {last_txt}",
        parse_mode=ParseMode.HTML,
    )


async def cmd_models(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await guard(update, context):
        return
    db, msg = _db(context), update.effective_message
    parts = (msg.text or "").split(None, 1)
    raw = parts[1] if len(parts) > 1 else ""
    items = []
    for p in re.split(r"[,;\n]+", raw):
        p = " ".join(p.split())[:40]
        if not p:
            continue
        if not re.search(r"iphon|айфон|іфон", p, re.I):
            p = "iphone " + p
        items.append(p.lower())
    if not items:
        cur = ", ".join(get_settings(db)["queries"])
        await msg.reply_text(f"Зараз шукаю: {cur}\n\nЩоб змінити: /models 12, 13 pro, 14 pro max")
        return
    items = list(dict.fromkeys(items))[:12]
    db.set("s_queries", items)
    await msg.reply_text("✅ Тепер шукаю: " + ", ".join(items))


async def _set_int(update, context, key: str, lo: int, hi: int, label: str):
    if not await guard(update, context):
        return
    msg, args = update.effective_message, context.args or []
    if not args or not args[0].isdigit() or not lo <= int(args[0]) <= hi:
        await msg.reply_text(f"Вкажи число від {lo} до {hi}. Зараз: {get_settings(_db(context))[key]}")
        return
    _db(context).set("s_" + key, int(args[0]))
    await msg.reply_text(f"✅ {label}: {int(args[0])}")


async def cmd_discount(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _set_int(update, context, "discount", 5, 60, "Мінімальна знижка, %")


async def cmd_interval(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await _set_int(update, context, "interval", 5, 180, "Інтервал, хв")


async def cmd_market(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await guard(update, context):
        return
    flt = " ".join(context.args or []).lower().strip()
    rows = []
    for g, mk in _db(context).markets(time.time()).items():
        if not mk:
            continue
        src, cur, model, storage, state = g.split("|")
        name = pretty_name(model, int(storage), state)
        if flt and flt not in name.lower():
            continue
        num = re.match(r"\d+", model)
        rows.append(((src, int(num.group()) if num else 0, model, int(storage), state),
                     f"{name} — {fmt_price(mk[0], cur)} · n={mk[1]} · {src}"))
    if not rows:
        await update.effective_message.reply_text(
            "Поки немає даних для оцінки ринку. Натисни 🔎 Скан — бот збере оголошення.")
        return
    rows.sort(key=lambda r: r[0])
    lines = [r[1] for r in rows[:40]]
    extra = f"\n…і ще {len(rows) - 40}. Звузь: /market 13 pro" if len(rows) > 40 else ""
    await update.effective_message.reply_text("📊 Ринок (медіана цін оголошень)\n" + "\n".join(lines) + extra)


async def cmd_reset(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await guard(update, context):
        return
    _db(context).reset_items()
    await update.effective_message.reply_text("🗑 Базу оголошень очищено. Ринок накопичиться знову після сканів.")


async def on_error(update, context):
    log.error("Помилка: %s", context.error)


# ═════════════════════ Автоскан у фоні ═════════════════════
async def auto_tick(app) -> None:
    db: DB = app.bot_data["db"]
    s, owner = get_settings(db), get_owner(db)
    if not owner or not s["auto"]:
        return
    if time.time() - float(db.get("last_scan", 0) or 0) < s["interval"] * 60:
        return
    lock = app.bot_data["lock"]
    if lock.locked():
        return
    async with lock:
        rep = await run_scan(app)
    await push_deals(app.bot, owner, rep.deals, db, only_new=True, limit=MAX_ALERTS_PER_RUN)
    if rep.errors and not rep.parsed:
        if time.time() - float(db.get("last_err_notice", 0) or 0) > 6 * 3600:
            db.set("last_err_notice", time.time())
            await app.bot.send_message(
                owner, "⚠️ Автоскан не отримав жодного оголошення:\n" + "\n".join(rep.errors[:3])
                + "\n\nЯкщо це 403/429 — додай PROXY_URL (див. README).")


async def auto_loop(app) -> None:
    await asyncio.sleep(10)
    while True:
        try:
            await auto_tick(app)
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("Помилка автоскану")
        await asyncio.sleep(30)


async def post_init(app) -> None:
    app.bot_data["lock"] = asyncio.Lock()
    app.bot_data["task"] = asyncio.create_task(auto_loop(app))
    log.info("Бот запущено. Джерела: %s", ", ".join(x.name for x in SOURCES))


async def post_shutdown(app) -> None:
    task = app.bot_data.get("task")
    if task:
        task.cancel()


def main() -> None:
    if not BOT_TOKEN:
        raise SystemExit("Не задано BOT_TOKEN — токен від @BotFather (змінна середовища).")
    logging.basicConfig(format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO)
    logging.getLogger("httpx").setLevel(logging.WARNING)   # щоб токен не світився в логах
    os.makedirs(DATA_DIR, exist_ok=True)

    app = (Application.builder().token(BOT_TOKEN).concurrent_updates(True)
           .post_init(post_init).post_shutdown(post_shutdown).build())
    app.bot_data["db"] = DB(os.path.join(DATA_DIR, "deals.db"))

    for name, fn in (("start", cmd_start), ("help", cmd_start), ("scan", cmd_scan), ("auto", cmd_auto),
                     ("settings", cmd_settings), ("models", cmd_models), ("discount", cmd_discount),
                     ("interval", cmd_interval), ("market", cmd_market), ("reset", cmd_reset)):
        app.add_handler(CommandHandler(name, fn))
    for label, fn in (("🔎 Скан", cmd_scan), ("📊 Ринок", cmd_market),
                      ("🔔 Авто", cmd_auto), ("⚙️ Налаштування", cmd_settings)):
        app.add_handler(MessageHandler(filters.Text([label]), fn))
    app.add_error_handler(on_error)
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
