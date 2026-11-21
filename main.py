import asyncio
import hashlib
import hmac
import json
import logging
import os
import random
import re
import time
import unicodedata
from collections import defaultdict
from urllib.parse import parse_qsl

import asyncpg
from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.filters import Command, CommandObject, CommandStart
from aiogram.types import (BufferedInputFile, CallbackQuery, InlineKeyboardButton, InlineKeyboardMarkup,
                           FSInputFile, InputMediaPhoto, Message, WebAppInfo)

TOKEN = os.getenv("BOT_TOKEN")
DATABASE_URL = os.getenv("DATABASE_URL")
if not TOKEN:
    raise ValueError("Ошибка: BOT_TOKEN не найден в переменных окружения!")
if not DATABASE_URL:
    raise ValueError("Ошибка: DATABASE_URL не найден в переменных окружения!")

# Адрес мини-приложения: Render сам задаёт RENDER_EXTERNAL_URL
WEBAPP_URL = os.getenv("WEBAPP_URL") or (os.getenv("RENDER_EXTERNAL_URL", "").rstrip("/") + "/app")
if WEBAPP_URL == "/app":
    raise ValueError("Не удалось определить адрес. Задай переменную WEBAPP_URL.")

INTERESTS = {"Музыка", "Кино", "Путешествия", "Спорт", "Игры", "Арт", "Книги", "Кухня",
             "Фото", "Танцы", "Походы", "Технологии"}
MOODS = {"Не сплю", "В наушниках", "Хочу кофе", "Свободен вечером", "Хочу гулять", "Ищу компанию",
         "Настроен поболтать", "Хочу в кино", "Скучаю", "Романтичное"}
SUPER_COST = 25
VERIFY_BONUS = 50
REWIND_COST = 25
CHANNEL_BONUS = 30
MAX_PHOTOS = 3
REF_BONUS = 10           # вайбов за приглашённого друга
REPORT_LIMIT = 10        # жалоб в сутки с одного аккаунта
FREE_SWIPES = 20         # бесплатных свайпов за окно (не накапливаются)
SWIPE_WINDOW = "4 hours" # длина окна; отсчёт идёт от первого свайпа в окне
SWIPE_PACKS = {10: 20, 20: 35, 50: 85}   # свайпов: цена в вайбах
SKIP_RETURN = "1 day"       # через сколько вернётся анкета после пропуска (свайп вверх)
PASS_RETURN = "32 hours"    # через сколько вернётся анкета после дизлайка
UNAME_COOLDOWN = "3 hours"               # как часто можно менять username
STREAK_SWIPES = 15       # свайпов (любых) в день, чтобы засчитать заход
STREAK_LIKES = 0         # лайки для серии не нужны
REF_SWIPES = 7           # приглашённый «активен»: минимум свайпов (любых)...
REF_LIKES = 3            # ...и минимум лайков
LOCATIONS = {            # код страны: (название, города)
    "KZ": ("Казахстан", ["Алматы", "Астана"]),
    "RU": ("Россия", ["Москва", "Санкт-Петербург", "Краснодар"]),
    "BY": ("Беларусь", ["Минск"]),
    "UA": ("Украина", ["Киев"]),
    "AM": ("Армения", ["Ереван", "Гюмри"]),
}
STREAK_BONUS = [5, 10, 20, 25, 30, 35, 40]   # 8-й день и дальше: 40
CHANNEL = (os.getenv("CHANNEL", "") or "@kivodate").strip()   # публичный канал, по умолчанию @kivodate
TODAY = "(now() AT TIME ZONE 'Europe/Moscow')::date"   # «день» по Москве
REMIND_HOURS = 4        # напоминание о серии: когда до конца дня осталось не больше стольких часов
REMIND_MIN_LEFT = 1800  # ...но не позже, чем за 30 минут до конца дня (секунды)
REMIND_MIN_STREAK = 2   # напоминаем, только если серия уже не короче стольких дней
VNOW = "(extract(epoch from clock_timestamp())::bigint % 1000000000)::int"   # версия фото (сбрасывает кэш)
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
PHOTO_KEY = hashlib.sha256(TOKEN.encode() + b"photo").digest()
ADMIN_ID = int(os.getenv("ADMIN_ID") or 0)  # твой Telegram id: сюда приходят селфи и жалобы
REASONS = ["Фейк или чужие фото", "Спам или реклама", "Оскорбления или угрозы",
           "Похоже, что нет 18 лет", "Другое"]
# жест: (эмодзи, описание, имя файла-примера рядом с main.py)
GESTURES = [("👍", "большой палец вверх", "verify_thumb.mp4"),
            ("🤘", "«рок-н-ролл»: указательный палец и мизинец вверх", "verify_rock.mp4"),
            ("🤙", "«позвони мне»: большой палец и мизинец, как телефонная трубка", "verify_call.mp4"),
            ("✌️", "знак «мир»: два пальца буквой V", "verify_peace.mp4")]
BANNED = set()
awaiting = {}  # кто сейчас должен прислать кружок: id -> (эмодзи, описание жеста)
EXAMPLE_NOTES = {}       # имя файла примера -> file_id кружка после первой отправки
reject_wait = {}  # админ -> кому он пишет причину отказа
BOT_USERNAME = ""
USERNAME_RE = re.compile(r"[A-Za-z0-9_]{3,20}")   # username: англ. буквы, цифры и _ (fullmatch)
PERSONA_BASE = 5_000_000_000_000_000   # id анкет, созданных админом (больше любого Telegram id)
PERSONAS = {}        # id анкеты админа -> id админа
ADMIN_ACTIVE = {}    # id админа -> id анкеты, от имени которой он сейчас работает
PL_SQL = ("(SELECT array_agg(p.slot::text || ':' || p.v::text ORDER BY p.slot) "
          "FROM user_photos p WHERE p.user_id=u.telegram_id) AS pl")

# ---------- ФИЛЬТР КОНТАКТОВ ----------
# Запрещаем ники, ссылки, почту, телефоны и названия мессенджеров в анкете.
CTRL = re.compile(r"[\u0000-\u0008\u000b-\u001f\u007f\u200b-\u200f\u202a-\u202e\u2060-\u2064\ufeff\u00ad]")
LOOK = str.maketrans("аеорсухкіј", "aeopcyxkij")   # кириллица, похожая на латиницу
CONTACT_WORDS = ("telegram", "телеграм", "телега", "whatsapp", "ватсап", "вотсап", "вацап", "viber",
                 "вайбер", "instagram", "инстаграм", "инста", "insta", "snapchat", "снапчат",
                 "discord", "дискорд", "tiktok", "тикток", "username", "юзернейм", "никнейм")
CONTACT_SHORT = re.compile(r"(?<!\w)(тг|tg|вк|vk|wa|ig|inst|инст|ник|nick)(?!\w)")
CONTACT_PATTERNS = [
    re.compile(r"@"),                                                     # @nick, почта
    re.compile(r"https?:|www\.|tg://|(?<!\w)t\s*[.·,]\s*me(?!\w)"),        # ссылки
    re.compile(r"(?<![\w-])[\w-]+\.(com|ru|me|org|net|io|gg|ly|su|xyz)(?!\w)"),   # домены
    re.compile(r"(?:\d[\s\-().+]*){9,}"),                                  # телефон
    re.compile(r"(?<!\w)[a-z][a-z0-9]*_[a-z0-9_]{2,}(?!\w)"),              # ivan_petrov
]
CONTACT_MSG = "Нельзя указывать ники, ссылки и контакты. Общайтесь в чате после взаимной симпатии."


def place_label(country, city):
    name = LOCATIONS[country][0] if country in LOCATIONS else ""
    return ", ".join(x for x in (city, name) if x) or "город не указан"


RESERVED_NAMES = ("admin", "moderator", "support", "kivo", "telegram", "official")


def username_problem(u):
    """Username теперь виден всем: нельзя выдавать себя за администрацию или светить телефон."""
    low = u.lower()
    if any(w in low for w in RESERVED_NAMES):
        return "Это имя зарезервировано, выбери другое"
    if sum(ch.isdigit() for ch in u) >= 9:
        return "В username не должно быть номера телефона"
    return ""


def fmt_wait(sec):
    h, m = divmod((int(sec) + 59) // 60, 60)
    return ((f"{h} ч " if h else "") + (f"{m} мин" if m else "")).strip() or "меньше минуты"


def clean_text(s, limit):
    return CTRL.sub("", str(s or "")).strip()[:limit]


def find_contact(text, words=True):
    t = unicodedata.normalize("NFKC", text or "")
    t = CTRL.sub("", t).lower()
    for v in (t, t.translate(LOOK)):
        if any(p.search(v) for p in CONTACT_PATTERNS):
            return True
        if words and (any(w in v for w in CONTACT_WORDS) or CONTACT_SHORT.search(v)):
            return True
    return False


router = Router()
bot = Bot(token=TOKEN)
pool = None


# ---------- БАЗА ДАННЫХ ----------
async def init_db():
    global pool
    pool = await asyncpg.create_pool(
        DATABASE_URL, min_size=1, max_size=5,
        statement_cache_size=0, max_inactive_connection_lifetime=60,
    )
    async with pool.acquire() as c:
        await c.execute("""CREATE TABLE IF NOT EXISTS users (
            telegram_id BIGINT PRIMARY KEY, name TEXT, age INTEGER, city TEXT, bio TEXT,
            photo TEXT, interests TEXT, verified INTEGER DEFAULT 0, vibes INTEGER DEFAULT 20)""")
        await c.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS mood TEXT")
        await c.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS last_bonus DATE")
        await c.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS banned INTEGER DEFAULT 0")
        await c.execute("""CREATE TABLE IF NOT EXISTS likes (
            user_id BIGINT, target_id BIGINT, action TEXT, PRIMARY KEY (user_id, target_id))""")
        await c.execute("""CREATE TABLE IF NOT EXISTS blocks (
            user_id BIGINT, target_id BIGINT, PRIMARY KEY (user_id, target_id))""")
        await c.execute("""CREATE TABLE IF NOT EXISTS reports (
            user_id BIGINT, target_id BIGINT, created TIMESTAMPTZ DEFAULT now(),
            PRIMARY KEY (user_id, target_id))""")
        await c.execute("""CREATE TABLE IF NOT EXISTS messages (
            id BIGSERIAL PRIMARY KEY, a BIGINT, b BIGINT, sender BIGINT, text TEXT,
            created TIMESTAMPTZ DEFAULT now())""")
        await c.execute("ALTER TABLE reports ADD COLUMN IF NOT EXISTS reason TEXT")
        await c.execute("""CREATE TABLE IF NOT EXISTS verifications (
            user_id BIGINT PRIMARY KEY, status TEXT, created TIMESTAMPTZ DEFAULT now())""")
        BANNED.update(r["telegram_id"] for r in
                      await c.fetch("SELECT telegram_id FROM users WHERE banned=1"))
        for q in ("ALTER TABLE users ADD COLUMN IF NOT EXISTS hidden INTEGER DEFAULT 0",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS pref_min INTEGER DEFAULT 18",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS pref_max INTEGER DEFAULT 99",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS streak INTEGER DEFAULT 0",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS last_streak_day DATE",
                  "ALTER TABLE likes ADD COLUMN IF NOT EXISTS created TIMESTAMPTZ DEFAULT now()",
                  "ALTER TABLE messages ADD COLUMN IF NOT EXISTS read_at TIMESTAMPTZ",
                  "ALTER TABLE verifications ADD COLUMN IF NOT EXISTS comment TEXT",
                  "CREATE TABLE IF NOT EXISTS photos (user_id BIGINT PRIMARY KEY, data BYTEA, v INTEGER DEFAULT 1)",
                  "CREATE TABLE IF NOT EXISTS user_photos (user_id BIGINT, slot SMALLINT, data BYTEA, "
                  "v INTEGER DEFAULT 1, PRIMARY KEY (user_id, slot))",
                  # старые одиночные фото переезжают в первый слот
                  "INSERT INTO user_photos (user_id, slot, data, v) SELECT user_id, 0, data, v FROM photos "
                  "ON CONFLICT DO NOTHING",
                  "DELETE FROM photos WHERE EXISTS (SELECT 1 FROM user_photos x WHERE x.user_id=photos.user_id)",
                  "CREATE TABLE IF NOT EXISTS daily (user_id BIGINT, day DATE, likes INTEGER DEFAULT 0, "
                  "passes INTEGER DEFAULT 0, PRIMARY KEY (user_id, day))",
                  "CREATE TABLE IF NOT EXISTS tasks (user_id BIGINT, task TEXT, PRIMARY KEY (user_id, task))",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS earned INTEGER DEFAULT 20",
                  "CREATE TABLE IF NOT EXISTS referrals (invitee BIGINT PRIMARY KEY, referrer BIGINT, "
                  "created TIMESTAMPTZ DEFAULT now(), joined BOOLEAN DEFAULT false, claimed BOOLEAN DEFAULT false)",
                  "CREATE INDEX IF NOT EXISTS referrals_referrer ON referrals (referrer)",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS country TEXT",
                  "CREATE INDEX IF NOT EXISTS users_country_city ON users (country, city)",
                  "ALTER TABLE referrals ADD COLUMN IF NOT EXISTS activated BOOLEAN DEFAULT false",
                  # уже выплаченные по старым правилам рефералы второй раз не оплачиваем
                  "UPDATE referrals SET activated=true WHERE claimed AND NOT activated",
                  # username (уникальный без учёта регистра), анкеты админа, активная анкета админа
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS username TEXT",
                  "CREATE UNIQUE INDEX IF NOT EXISTS users_username_lower ON users (lower(username))",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS owner BIGINT",
                  "CREATE TABLE IF NOT EXISTS admin_state (admin_id BIGINT PRIMARY KEY, active BIGINT)",
                  "CREATE SEQUENCE IF NOT EXISTS persona_seq",
                  # пол ('m' / 'f') и кого показывать ('m' / 'f' / 'any')
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS gender TEXT",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS looking TEXT",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS sw_start TIMESTAMPTZ",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS sw_used INTEGER DEFAULT 0",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS sw_bonus INTEGER DEFAULT 0",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS streak_remind_day DATE",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS remind_off INTEGER DEFAULT 0",
                  "ALTER TABLE users ADD COLUMN IF NOT EXISTS uname_changed TIMESTAMPTZ"):
            await c.execute(q)
        first_run = await c.fetchval("SELECT to_regclass('vibe_log') IS NULL")
        await c.execute("""CREATE TABLE IF NOT EXISTS vibe_log (
            id BIGSERIAL PRIMARY KEY, user_id BIGINT NOT NULL, delta INTEGER NOT NULL,
            reason TEXT NOT NULL, note TEXT, created TIMESTAMPTZ DEFAULT now())""")
        await c.execute("CREATE INDEX IF NOT EXISTS vibe_log_user ON vibe_log (user_id, id DESC)")
        if first_run:   # один раз: текущий баланс становится «стартовым» в истории
            await c.execute("INSERT INTO vibe_log (user_id, delta, reason) "
                            "SELECT telegram_id, vibes, 'start' FROM users WHERE age IS NOT NULL AND vibes<>0")
        PERSONAS.clear()
        for r in await c.fetch("SELECT telegram_id, owner FROM users WHERE owner IS NOT NULL"):
            PERSONAS[r["telegram_id"]] = r["owner"]
        if ADMIN_ID:
            act = await c.fetchval("SELECT active FROM admin_state WHERE admin_id=$1", ADMIN_ID)
            if act in PERSONAS:
                ADMIN_ACTIVE[ADMIN_ID] = act
        # старые анкеты со свободным вводом: если город совпал со справочником, проставляем страну
        known = {city.lower(): (city, code) for code, (_, cities) in LOCATIONS.items() for city in cities}
        for r in await c.fetch("SELECT DISTINCT city FROM users WHERE country IS NULL AND city IS NOT NULL"):
            hit = known.get(r["city"].strip().lower())
            if hit:
                await c.execute("UPDATE users SET city=$2, country=$3 WHERE country IS NULL AND city=$1",
                                r["city"], hit[0], hit[1])


# ---------- ПРОВЕРКА ПОДПИСИ TELEGRAM ----------
def check_init_data(init_data):
    try:
        data = dict(parse_qsl(init_data, keep_blank_values=True))
        got_hash = data.pop("hash", "")
        check = "\n".join(f"{k}={v}" for k, v in sorted(data.items()))
        secret = hmac.new(b"WebAppData", TOKEN.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, got_hash):
            return None
        if time.time() - int(data.get("auth_date", 0)) > 86400:
            return None
        return json.loads(data["user"])
    except Exception:
        return None


hits = defaultdict(list)


def limited(uid):
    now = time.time()
    if len(hits) > 5000:   # не копим память под давно ушедших
        for k in [k for k, v in hits.items() if not v or now - v[-1] > 60]:
            del hits[k]
    h = [t for t in hits[uid] if now - t < 60]
    h.append(now)
    hits[uid] = h
    return len(h) > 120


def err(msg, status=400):
    return web.json_response({"error": msg}, status=status)


async def body(request):
    try:
        d = await request.json()
    except Exception:
        return {}
    return d if isinstance(d, dict) else {}


@web.middleware
async def auth(request, handler):
    if not request.path.startswith("/api/"):
        return await handler(request)
    user = check_init_data(request.headers.get("X-Init-Data", ""))
    if not user:
        return err("Открой приложение через Telegram", 401)
    real = int(user["id"])
    if real in BANNED:
        return err("Аккаунт заблокирован", 403)
    if limited(real):
        return err("Слишком часто, подожди минуту", 429)
    request["real"] = real   # настоящий Telegram id
    # админ работает от имени выбранной анкеты, остальные всегда от своего имени
    request["uid"] = ADMIN_ACTIVE.get(real, real) if (ADMIN_ID and real == ADMIN_ID) else real
    uid = request["uid"]
    request["tg_name"] = user.get("first_name", "")
    resp = await handler(request)
    resp.headers["Cache-Control"] = "no-store"   # чтобы список пар и сообщения не залипали в кэше webview
    return resp


def photo_token(uid):
    return hmac.new(PHOTO_KEY, str(uid).encode(), hashlib.sha256).hexdigest()[:24]


def photo_url(uid, slot, v):
    return f"/p/{uid}/{photo_token(uid)}?s={slot}&v={v}"


def photo_urls(uid, pl):
    """pl: список строк «слот:версия» из SQL, по порядку слотов."""
    out = []
    for x in pl or []:
        slot, v = x.split(":")
        out.append(photo_url(uid, int(slot), int(v)))
    return out


def prof(u):
    ph = photo_urls(u["telegram_id"], u.get("pl"))
    return {"id": u["telegram_id"], "name": u["name"], "age": u["age"], "username": u["username"] or "",
            "bio": u["bio"], "mood": u["mood"], "verified": u["verified"] == 1,
            "photo": ph[0] if ph else None, "photos": ph,
            "interests": [x for x in (u["interests"] or "").split(",") if x]}


# Условие «пара»: взаимная симпатия ИЛИ суперлайк от любого из двоих, без блокировок; {o} — id второго человека, $1 — я
MATCH_SQL = """(
   (EXISTS (SELECT 1 FROM likes x WHERE x.user_id=$1 AND x.target_id={o} AND x.action IN ('like','super'))
    AND EXISTS (SELECT 1 FROM likes y WHERE y.user_id={o} AND y.target_id=$1 AND y.action IN ('like','super')))
   OR EXISTS (SELECT 1 FROM likes s WHERE s.action='super'
              AND ((s.user_id=$1 AND s.target_id={o}) OR (s.user_id={o} AND s.target_id=$1))))
 AND NOT EXISTS (SELECT 1 FROM blocks b WHERE (b.user_id=$1 AND b.target_id={o}) OR (b.user_id={o} AND b.target_id=$1))
 AND NOT EXISTS (SELECT 1 FROM users z WHERE z.telegram_id={o} AND z.banned=1)"""


async def is_matched(c, uid, other):
    return bool(await c.fetchval("SELECT 1 WHERE " + MATCH_SQL.format(o="$2"), uid, other))


# ---------- API ----------
SWIPE_WIN = f"(sw_start IS NULL OR sw_start + interval '{SWIPE_WINDOW}' <= now())"   # окно закончилось или не начиналось


async def swipe_info(c, uid):
    r = await c.fetchrow(
        f"SELECT COALESCE(sw_bonus,0) AS bonus, CASE WHEN {SWIPE_WIN} THEN 0 ELSE COALESCE(sw_used,0) END AS used, "
        f"CASE WHEN {SWIPE_WIN} THEN 0 ELSE GREATEST(0, extract(epoch from "
        f"(sw_start + interval '{SWIPE_WINDOW}' - now())))::int END AS wait FROM users WHERE telegram_id=$1", uid)
    free = max(0, FREE_SWIPES - r["used"])
    return {"free_left": free, "free_max": FREE_SWIPES, "bonus": r["bonus"], "left": free + r["bonus"],
            "reset_in": r["wait"]}


async def take_swipe(c, uid):
    """Тратит один свайп: сначала бесплатный из текущего окна, потом купленный. Атомарно."""
    ok = await c.fetchval(
        f"UPDATE users SET sw_used = CASE WHEN {SWIPE_WIN} THEN 1 ELSE COALESCE(sw_used,0)+1 END, "
        f"sw_start = CASE WHEN {SWIPE_WIN} THEN now() ELSE sw_start END "
        f"WHERE telegram_id=$1 AND ({SWIPE_WIN} OR COALESCE(sw_used,0) < $2) RETURNING 1", uid, FREE_SWIPES)
    if ok:
        return True
    return bool(await c.fetchval(
        "UPDATE users SET sw_bonus=sw_bonus-1 WHERE telegram_id=$1 AND COALESCE(sw_bonus,0)>0 RETURNING 1", uid))


async def day_info(c, uid):
    d = await c.fetchrow(f"SELECT likes, passes FROM daily WHERE user_id=$1 AND day={TODAY}", uid)
    u = await c.fetchrow(f"SELECT streak, last_streak_day, {TODAY} AS today FROM users WHERE telegram_id=$1", uid)
    likes, passes = (d["likes"], d["passes"]) if d else (0, 0)
    last, today = u["last_streak_day"], u["today"]
    eff = u["streak"] if last and (today - last).days <= 1 else 0
    return {"done_likes": likes, "done_swipes": likes + passes,
            "need_likes": STREAK_LIKES, "need_swipes": STREAK_SWIPES, "claimed": last == today,
            "streak": eff, "reward": STREAK_BONUS[min(eff + 1, 7) - 1],
            "swipes": await swipe_info(c, uid)}


async def log_vibes(c, uid, delta, reason, note=None):
    """Запись в историю вайбов. Вызывается в той же транзакции, что и изменение баланса."""
    if delta:
        await c.execute("INSERT INTO vibe_log (user_id, delta, reason, note) VALUES ($1,$2,$3,$4)",
                        uid, delta, reason, note)


async def claim_streak(c, uid):
    info = await day_info(c, uid)
    if info["claimed"] or info["done_swipes"] < STREAK_SWIPES or info["done_likes"] < STREAK_LIKES:
        return None
    n = info["streak"] + 1
    bonus = STREAK_BONUS[min(n, 7) - 1]
    async with c.transaction():
        done = await c.fetchval(   # атомарно: награда за день выдаётся один раз
            f"UPDATE users SET streak=$2, last_streak_day={TODAY}, vibes=vibes+$3, earned=earned+$3 "
            f"WHERE telegram_id=$1 AND last_streak_day IS DISTINCT FROM {TODAY} RETURNING 1", uid, n, bonus)
        if not done:
            return None
        await log_vibes(c, uid, bonus, "streak", str(n))
    return {"day": n, "bonus": bonus}


async def ref_info(c, uid):
    r = await c.fetchrow(
        "SELECT count(*) FILTER (WHERE joined) AS invited, "
        "count(*) FILTER (WHERE activated) AS active FROM referrals WHERE referrer=$1", uid)
    return {"invited": r["invited"], "active": r["active"], "earned": r["active"] * REF_BONUS,
            "pending": r["invited"] - r["active"]}


async def check_referral(c, uid):
    """Приглашённый стал «активным»: >= REF_SWIPES свайпов (любых) и >= REF_LIKES лайков.
    Награду пригласившему выдаём ровно один раз: флаг activated переключается атомарным UPDATE."""
    if not await c.fetchval("SELECT 1 FROM referrals WHERE invitee=$1 AND joined AND NOT activated", uid):
        return None
    st = await c.fetchrow(
        "SELECT count(*) AS swipes, count(*) FILTER (WHERE action IN ('like','super')) AS likes "
        "FROM likes WHERE user_id=$1", uid)
    if st["swipes"] < REF_SWIPES or st["likes"] < REF_LIKES:
        return None
    referrer = await c.fetchval(
        "UPDATE referrals SET activated=true, claimed=true "
        "WHERE invitee=$1 AND joined AND NOT activated RETURNING referrer", uid)
    if not referrer:
        return None
    await c.execute("UPDATE users SET vibes=vibes+$2, earned=earned+$2 WHERE telegram_id=$1", referrer, REF_BONUS)
    await log_vibes(c, referrer, REF_BONUS, "ref")
    return referrer


def ident(request):
    return {"uid": request["uid"], "is_admin": bool(ADMIN_ID) and request["real"] == ADMIN_ID,
            "persona": request["uid"] in PERSONAS}


async def api_me_get(request):
    uid = request["uid"]
    async with pool.acquire() as c:
        u = await c.fetchrow("SELECT u.*, (SELECT array_agg(p.slot::text || ':' || p.v::text ORDER BY p.slot) FROM user_photos p WHERE p.user_id=u.telegram_id) AS pl, COALESCE(GREATEST(0, extract(epoch from "
                             f"(u.uname_changed + interval '{UNAME_COOLDOWN}' - now()))), 0)::int AS uwait "
                             "FROM users u WHERE telegram_id=$1", uid)
        if not u or u["age"] is None:
            rows = await c.fetch("SELECT slot, v FROM user_photos WHERE user_id=$1 ORDER BY slot", uid)
            ph = [photo_url(uid, r["slot"], r["v"]) for r in rows]
            return web.json_response(dict(
                ident(request), exists=False, username="",
                name=request["tg_name"] if request["uid"] == request["real"] else "",
                photo=ph[0] if ph else None, photos=ph))
        v = await c.fetchrow("SELECT status, comment FROM verifications WHERE user_id=$1", uid)
        done = await c.fetchval("SELECT 1 FROM tasks WHERE user_id=$1 AND task='channel'", uid)
        got = await claim_streak(c, uid)   # норма уже выполнена, а свайпов больше нет: засчитываем при заходе
        vibes_now = await c.fetchval("SELECT vibes FROM users WHERE telegram_id=$1", uid)
        info = await day_info(c, uid)
        st = await c.fetchrow(
            "SELECT count(*) FILTER (WHERE action IN ('like','super')) AS likes, "
            "count(*) FILTER (WHERE action='pass') AS passes FROM likes WHERE target_id=$1", uid)
        mt = await c.fetchval("SELECT count(*) FROM users u WHERE u.age IS NOT NULL AND "
                              + MATCH_SQL.format(o="u.telegram_id"), uid)
        ref = await ref_info(c, uid)
    stats = {"likes": st["likes"], "passes": st["passes"], "matches": mt}
    return web.json_response(dict(
        prof(u), exists=True, stats=stats, vibes=vibes_now, info=info, bot=BOT_USERNAME,
        earned=u["earned"] or 0, ref=ref, ref_link=f"https://t.me/{BOT_USERNAME}?start=ref_{uid}",
        channel=CHANNEL.lstrip("@"), channel_done=bool(done), example=bool(example_gestures()),
        examples=[{"e": g[0], "d": g[1]} for g in example_gestures()],
        streak_claimed=got, hidden=u["hidden"] == 1, pref_min=u["pref_min"], pref_max=u["pref_max"],
        vstatus=v["status"] if v else None, vcomment=v["comment"] if v else None,
        username=u["username"] or "", gender=u["gender"] or "", looking=u["looking"] or "",
        uname_wait=u["uwait"],
        **ident(request)))


async def api_me_post(request):
    uid = request["uid"]
    d = await body(request)
    name = clean_text(d.get("name"), 30)
    bio = clean_text(d.get("bio"), 140)
    mood = d.get("mood") if d.get("mood") in MOODS else None
    raw = d.get("interests") if isinstance(d.get("interests"), list) else []
    ints = [i for i in raw if i in INTERESTS][:8]
    try:
        lo = max(18, min(99, int(d.get("pref_min", 18))))
        hi = max(lo, min(99, int(d.get("pref_max", 99))))
    except (TypeError, ValueError):
        lo, hi = 18, 99
    hidden = 1 if d.get("hidden") else 0
    try:
        age = int(d.get("age"))
    except (TypeError, ValueError):
        age = 0
    if not name:
        return err("Заполни имя")
    if age < 18 or age > 99:
        return err("KIVO только для тех, кому 18 и больше")
    gender = d.get("gender") if d.get("gender") in ("m", "f") else None
    looking = d.get("looking") if d.get("looking") in ("m", "f", "any") else None
    if not gender:
        return err("Укажи свой пол")
    if not looking:
        return err("Укажи, кого показывать в ленте")
    if find_contact(bio) or find_contact(name, words=False):
        return err(CONTACT_MSG)
    uname = str(d.get("username") or "").strip()
    async with pool.acquire() as c:
        row = await c.fetchrow(
            f"SELECT age, username, COALESCE(GREATEST(0, extract(epoch from "
            f"(uname_changed + interval '{UNAME_COOLDOWN}' - now()))), 0)::int AS wait "
            "FROM users WHERE telegram_id=$1", uid)
        existing = row["age"] if row else None
        cur_un = row["username"] if row else None
        changing = False
        if not cur_un or (uname and uname != cur_un):   # первая установка или смена
            if not USERNAME_RE.fullmatch(uname):
                return err("Username: от 3 до 20 символов, только английские буквы, цифры и _")
            if username_problem(uname):
                return err(username_problem(uname))
            if cur_un and row["wait"] > 0:
                return err("Username можно менять раз в 3 часа. Следующая смена через " + fmt_wait(row["wait"]))
            if await c.fetchval("SELECT 1 FROM users WHERE lower(username)=lower($1) AND telegram_id<>$2", uname, uid):
                return err("Этот username уже занят")
            changing = True
        if existing is None and not d.get("adult"):
            return err("Подтверди, что тебе есть 18 лет")
        if not await c.fetchval("SELECT 1 FROM user_photos WHERE user_id=$1", uid):
            return err("Добавь фото в анкету")
        try:
            await c.execute(
                """INSERT INTO users (telegram_id, name, age, bio, interests, mood, vibes,
                                      hidden, pref_min, pref_max, username, gender, looking, uname_changed)
                   VALUES ($1,$2,$3,$4,$5,$6,20,$7,$8,$9,$10,$11,$12, now())
                   ON CONFLICT (telegram_id) DO UPDATE
                   SET name=$2, age=$3, bio=$4, interests=$5, mood=$6,
                       hidden=$7, pref_min=$8, pref_max=$9,
                       username=CASE WHEN $13::boolean THEN $10 ELSE users.username END,
                       uname_changed=CASE WHEN $13::boolean THEN now() ELSE users.uname_changed END,
                       gender=$11, looking=$12""",
                uid, name, age, bio, ",".join(ints), mood, hidden, lo, hi, uname if changing else None,
                gender, looking, changing)
        except asyncpg.UniqueViolationError:   # два человека одновременно заняли один username
            return err("Этот username уже занят")
        if existing is None:   # первая анкета: приглашение «в процессе», награда придёт после активности
            await c.execute("UPDATE referrals SET joined=true WHERE invitee=$1 AND NOT joined", uid)
            await log_vibes(c, uid, 20, "signup")
    return web.json_response({"ok": True})


async def api_feed(request):
    """Лента: сначала суперлайки мне, затем все остальные в случайном порядке.
    Уже оценённые, заблокированные, скрытые и я сам исключены."""
    uid = request["uid"]
    async with pool.acquire() as c:
        rows = await c.fetch(f"""
            SELECT u.*, (l.action = 'super') AS sup,
                   (SELECT array_agg(ph2.slot::text || ':' || ph2.v::text ORDER BY ph2.slot) FROM user_photos ph2 WHERE ph2.user_id=u.telegram_id) AS pl
            FROM users u
            CROSS JOIN (SELECT pref_min, pref_max, gender, looking
                        FROM users WHERE telegram_id=$1) me
            LEFT JOIN likes l ON l.user_id = u.telegram_id AND l.target_id = $1
            WHERE u.telegram_id <> $1 AND u.age >= 18 AND u.banned = 0 AND u.hidden = 0
              AND COALESCE(l.action, '') <> 'super'
              AND EXISTS (SELECT 1 FROM user_photos ph WHERE ph.user_id=u.telegram_id)
              AND u.age BETWEEN me.pref_min AND me.pref_max
              AND (me.looking IS NULL OR me.looking = 'any' OR u.gender = me.looking)
              AND (u.looking IS NULL OR u.looking = 'any' OR u.looking = me.gender)
              AND NOT EXISTS (SELECT 1 FROM likes s WHERE s.user_id=$1 AND s.target_id=u.telegram_id
                              AND NOT ((s.action='skip' AND s.created < now() - interval '{SKIP_RETURN}')
                                    OR (s.action='pass' AND s.created < now() - interval '{PASS_RETURN}')))
              AND NOT EXISTS (SELECT 1 FROM blocks b WHERE (b.user_id=$1 AND b.target_id=u.telegram_id)
                                                        OR (b.user_id=u.telegram_id AND b.target_id=$1))
            ORDER BY (l.action = 'super') DESC NULLS LAST, random()
            LIMIT 20""", uid)
    return web.json_response({"items": [dict(prof(r), super=bool(r["sup"])) for r in rows]})


async def tg_send(target, text):
    """Анкеты, созданные админом, не настоящие аккаунты: их уведомления приходят админу."""
    try:
        owner = PERSONAS.get(target)
        if owner:
            async with pool.acquire() as c:
                nm = await c.fetchval("SELECT name FROM users WHERE telegram_id=$1", target)
            await bot.send_message(owner, f"🎭 Анкета «{nm or target}»\n{text}")
        else:
            await bot.send_message(target, text)
    except Exception:
        pass


async def notify(target, name=None):
    who = f": {name}" if name else ""
    await tg_send(target, f"💫 У тебя новая пара в KIVO{who}! Открой приложение, чтобы написать.")


async def notify_msg(target, name):
    await tg_send(target, f"💬 {name} написал(а) тебе в KIVO. Открой приложение, чтобы ответить.")


async def api_swipe(request):
    uid = request["uid"]
    d = await body(request)
    try:
        target = int(d.get("target"))
    except (TypeError, ValueError):
        return err("Некорректный запрос")
    action = d.get("action")
    if action not in ("like", "pass", "super", "skip") or target == uid:
        return err("Некорректный запрос")
    col = "passes" if action in ("pass", "skip") else "likes"   # пропуск (skip) считается как дизлайк в счётчике дня
    match, got, ref_paid = False, None, None
    async with pool.acquire() as c:
        async with c.transaction():
            if not await c.fetchval(
                    "SELECT 1 FROM users u WHERE u.telegram_id=$2 AND u.age>=18 AND u.banned=0 AND u.hidden=0 "
                    "AND NOT EXISTS (SELECT 1 FROM blocks b WHERE (b.user_id=$1 AND b.target_id=u.telegram_id) "
                    "OR (b.user_id=u.telegram_id AND b.target_id=$1))", uid, target):
                return err("Анкета не найдена", 404)
            if not await c.fetchval("SELECT 1 FROM users WHERE telegram_id=$1 AND age IS NOT NULL", uid):
                return err("Сначала создай анкету", 403)
            await c.execute(f"INSERT INTO daily (user_id, day) VALUES ($1, {TODAY}) ON CONFLICT DO NOTHING", uid)
            # блокируем строку: свайпы одного человека обрабатываются по очереди
            await c.fetchval(f"SELECT {col} FROM daily WHERE user_id=$1 AND day={TODAY} FOR UPDATE", uid)
            ins = await c.fetchval(
                "INSERT INTO likes (user_id,target_id,action) VALUES ($1,$2,$3) "
                "ON CONFLICT (user_id,target_id) DO UPDATE SET action=EXCLUDED.action, created=now() "
                f"WHERE (likes.action='skip' AND likes.created < now() - interval '{SKIP_RETURN}') "
                f"OR (likes.action='pass' AND likes.created < now() - interval '{PASS_RETURN}') "
                "RETURNING 1", uid, target, action)   # старый пропуск или дизлайк можно заменить новой оценкой
            if ins:
                if not await take_swipe(c, uid):   # исключение откатывает и сам свайп
                    raise web.HTTPTooManyRequests(
                        text=json.dumps({"error": "Свайпы закончились", "code": "no_swipes"}, ensure_ascii=False),
                        content_type="application/json")
                if action == "super":
                    paid = await c.fetchval(
                        "UPDATE users SET vibes=vibes-$2 WHERE telegram_id=$1 AND vibes>=$2 RETURNING 1",
                        uid, SUPER_COST)
                    if not paid:
                        raise web.HTTPPaymentRequired(
                            text=json.dumps({"error": "Не хватает вайбов"}), content_type="application/json")
                    await log_vibes(c, uid, -SUPER_COST, "super")
                await c.execute(f"UPDATE daily SET {col}={col}+1 WHERE user_id=$1 AND day={TODAY}", uid)
                if action not in ("pass", "skip"):
                    match = await is_matched(c, uid, target)
                got = await claim_streak(c, uid)   # заход засчитывается, когда набрано и свайпов, и лайков
                ref_paid = await check_referral(c, uid)
        vibes = await c.fetchval("SELECT vibes FROM users WHERE telegram_id=$1", uid)
        info = await day_info(c, uid)
        myname = await c.fetchval("SELECT name FROM users WHERE telegram_id=$1", uid) if match else None
    if match:
        asyncio.create_task(notify(target, myname))
    if ref_paid:
        asyncio.create_task(notify_ref(ref_paid))
    return web.json_response({"match": match, "vibes": vibes, "streak": got, "info": info})


async def api_vibes_history(request):
    """История вайбов: новые сверху, по 30 записей. Следующая страница: ?before=<id последней записи>."""
    uid = request["uid"]
    before = int_or_none(request.query.get("before"))
    async with pool.acquire() as c:
        rows = await c.fetch(
            "SELECT id, delta, reason, note, extract(epoch from created)::bigint AS ts FROM vibe_log "
            "WHERE user_id=$1 AND ($2::bigint IS NULL OR id<$2) ORDER BY id DESC LIMIT 31", uid, before)
    items = [{"id": r["id"], "delta": r["delta"], "reason": r["reason"], "note": r["note"], "ts": r["ts"]}
             for r in rows[:30]]
    return web.json_response({"items": items, "more": len(rows) > 30})


async def api_rewind(request):
    """Платный возврат к прошлой анкете (свайп вниз): снимает дизлайк, пропуск или лайк,
    если это не привело к паре. Суперлайк и анкеты, с которыми уже есть пара, вернуть нельзя."""
    uid = request["uid"]
    d = await body(request)
    target = int_or_none(d.get("target"))
    if target is None or target == uid:
        return err("Некорректный запрос")
    async with pool.acquire() as c:
        async with c.transaction():
            ok = await c.fetchval("""SELECT 1 FROM users u
                WHERE u.telegram_id=$2 AND u.age>=18 AND u.banned=0 AND u.hidden=0
                  AND NOT EXISTS (SELECT 1 FROM blocks b WHERE (b.user_id=$1 AND b.target_id=u.telegram_id)
                                  OR (b.user_id=u.telegram_id AND b.target_id=$1))""", uid, target)
            if not ok:
                return err("Эту анкету вернуть нельзя", 404)
            act = await c.fetchval(
                "SELECT action FROM likes WHERE user_id=$1 AND target_id=$2 FOR UPDATE", uid, target)
            if act not in ("pass", "skip", "like"):
                return err("Эту анкету вернуть нельзя", 404)
            if act == "like" and await is_matched(c, uid, target):
                return err("Вы уже пара, вернуть анкету нельзя", 409)
            paid = await c.fetchval("UPDATE users SET vibes=vibes-$2 WHERE telegram_id=$1 AND vibes>=$2 "
                                    "RETURNING 1", uid, REWIND_COST)
            if not paid:
                return err(f"Не хватает вайбов: возврат стоит {REWIND_COST}", 402)
            await log_vibes(c, uid, -REWIND_COST, "rewind")
            await c.execute("DELETE FROM likes WHERE user_id=$1 AND target_id=$2", uid, target)
            col = "likes" if act == "like" else "passes"
            await c.execute(f"UPDATE daily SET {col}=GREATEST({col}-1,0) WHERE user_id=$1 AND day={TODAY}", uid)
        u = await c.fetchrow("SELECT u.*, (SELECT array_agg(ph2.slot::text || ':' || ph2.v::text ORDER BY ph2.slot) FROM user_photos ph2 WHERE ph2.user_id=u.telegram_id) AS pl "
                             "FROM users u WHERE telegram_id=$1", target)
        vibes = await c.fetchval("SELECT vibes FROM users WHERE telegram_id=$1", uid)
        info = await day_info(c, uid)
    return web.json_response({"item": dict(prof(u), super=False), "vibes": vibes, "info": info})


async def api_swipes_buy(request):
    uid = request["uid"]
    pack = int_or_none((await body(request)).get("pack"))
    if pack not in SWIPE_PACKS:
        return err("Некорректный запрос")
    price = SWIPE_PACKS[pack]
    async with pool.acquire() as c:
        async with c.transaction():
            ok = await c.fetchval(
                "UPDATE users SET vibes=vibes-$2, sw_bonus=COALESCE(sw_bonus,0)+$3 "
                "WHERE telegram_id=$1 AND age IS NOT NULL AND vibes>=$2 RETURNING 1", uid, price, pack)
            if ok:
                await log_vibes(c, uid, -price, "swipes", str(pack))
        if not ok:
            return err(f"Не хватает вайбов: пакет стоит {price}", 402)
        vibes = await c.fetchval("SELECT vibes FROM users WHERE telegram_id=$1", uid)
        info = await day_info(c, uid)
    return web.json_response({"vibes": vibes, "info": info})


async def api_matches(request):
    uid = request["uid"]
    async with pool.acquire() as c:
        rows = await c.fetch(
            """SELECT u.*, (SELECT array_agg(ph2.slot::text || ':' || ph2.v::text ORDER BY ph2.slot) FROM user_photos ph2 WHERE ph2.user_id=u.telegram_id) AS pl,
                      lm.id AS last_id, lm.text AS last, lm.sender AS last_sender, lm.ts AS last_ts
               FROM users u
               LEFT JOIN LATERAL (
                   SELECT m.id, m.text, m.sender, extract(epoch from m.created)::bigint AS ts
                   FROM messages m
                   WHERE m.a=LEAST($1::bigint,u.telegram_id) AND m.b=GREATEST($1::bigint,u.telegram_id)
                   ORDER BY m.id DESC LIMIT 1) lm ON true
               WHERE u.age IS NOT NULL AND """ + MATCH_SQL.format(o="u.telegram_id")
            + " ORDER BY lm.id DESC NULLS FIRST", uid)   # новые пары без переписки сверху, дальше по последнему сообщению
    return web.json_response({"items": [
        dict(prof(r), last=r["last"], last_id=r["last_id"], last_me=r["last_sender"] == uid, last_ts=r["last_ts"])
        for r in rows]})


async def api_profile(request):
    """Страница собеседника: только для пары (взаимная симпатия или суперлайк, без блокировок)."""
    uid = request["uid"]
    other = int_or_none(request.query.get("id"))
    if other is None:
        return err("Некорректный запрос")
    async with pool.acquire() as c:
        if not await is_matched(c, uid, other):
            return err("Профиль недоступен", 403)
        u = await c.fetchrow(
            "SELECT u.*, (SELECT array_agg(ph2.slot::text || ':' || ph2.v::text ORDER BY ph2.slot) "
            "FROM user_photos ph2 WHERE ph2.user_id=u.telegram_id) AS pl "
            "FROM users u WHERE telegram_id=$1 AND age IS NOT NULL", other)
        if not u:
            return err("Профиль не найден", 404)
        st = await c.fetchrow(
            "SELECT count(*) FILTER (WHERE action IN ('like','super')) AS likes, "
            "count(*) FILTER (WHERE action='pass') AS passes FROM likes WHERE target_id=$1", other)
        mt = await c.fetchval("SELECT count(*) FROM users u WHERE u.age IS NOT NULL AND "
                              + MATCH_SQL.format(o="u.telegram_id"), other)
    return web.json_response({"profile": dict(prof(u), gender=u["gender"] or ""),
                              "stats": {"likes": st["likes"], "passes": st["passes"], "matches": mt}})


async def api_messages_get(request):
    uid = request["uid"]
    try:
        other = int(request.query.get("with"))
    except (TypeError, ValueError):
        return err("Некорректный запрос")
    async with pool.acquire() as c:
        if not await is_matched(c, uid, other):
            return err("Чат недоступен", 403)
        # помечаем входящие как прочитанные
        await c.execute(
            """UPDATE messages SET read_at=now()
               WHERE a=LEAST($1::bigint,$2::bigint) AND b=GREATEST($1::bigint,$2::bigint)
                 AND sender=$2 AND read_at IS NULL""", uid, other)
        rows = await c.fetch(
            """SELECT id, sender, text, ts, rd FROM (
                   SELECT id, sender, text,
                          extract(epoch from created)::bigint AS ts,
                          (read_at IS NOT NULL) AS rd
                   FROM messages
                   WHERE a=LEAST($1::bigint,$2::bigint) AND b=GREATEST($1::bigint,$2::bigint)
                   ORDER BY id DESC LIMIT 100) t ORDER BY id""", uid, other)
    return web.json_response({"items": [
        {"id": r["id"], "me": r["sender"] == uid, "text": r["text"], "ts": r["ts"], "read": bool(r["rd"])}
        for r in rows]})


async def api_messages_post(request):
    uid = request["uid"]
    d = await body(request)
    try:
        other = int(d.get("to"))
    except (TypeError, ValueError):
        return err("Некорректный запрос")
    text = str(d.get("text", "")).strip()[:500]
    if not text:
        return err("Пустое сообщение")
    async with pool.acquire() as c:
        if not await is_matched(c, uid, other):
            return err("Чат недоступен", 403)
        # уведомляем в бота, только если от меня в этом чате давно не было сообщений (без спама)
        quiet = await c.fetchval(
            "SELECT coalesce(max(created) < now() - interval '10 minutes', true) FROM messages "
            "WHERE a=LEAST($1::bigint,$2::bigint) AND b=GREATEST($1::bigint,$2::bigint) AND sender=$1", uid, other)
        mid = await c.fetchval("INSERT INTO messages (a,b,sender,text) VALUES (LEAST($1::bigint,$2::bigint),"
                               "GREATEST($1::bigint,$2::bigint),$1,$3) RETURNING id", uid, other, text)
        myname = await c.fetchval("SELECT name FROM users WHERE telegram_id=$1", uid) if quiet else None
    if quiet:
        asyncio.create_task(notify_msg(other, myname or "Новая пара"))
    return web.json_response({"ok": True, "id": mid})


async def send_profile_to_admin(uid):
    """Анкета человека для модератора: фото, описание, возраст и статистика. Простой текст, без разметки."""
    if not ADMIN_ID:
        return
    try:
        async with pool.acquire() as c:
            u = await c.fetchrow("SELECT * FROM users WHERE telegram_id=$1", uid)
            if not u:
                await bot.send_message(ADMIN_ID, f"Анкета id {uid}: пользователь не найден.")
                return
            photos = [bytes(r["data"]) for r in await c.fetch(
                "SELECT data FROM user_photos WHERE user_id=$1 ORDER BY slot", uid)]
            got = await c.fetchrow(
                "SELECT count(*) FILTER (WHERE action IN ('like','super')) AS likes, "
                "count(*) FILTER (WHERE action='pass') AS passes FROM likes WHERE target_id=$1", uid)
            gave = await c.fetchrow(
                "SELECT count(*) FILTER (WHERE action IN ('like','super')) AS likes, "
                "count(*) FILTER (WHERE action='super') AS supers, "
                "count(*) FILTER (WHERE action='pass') AS passes, "
                "count(*) FILTER (WHERE action='skip') AS skips FROM likes WHERE user_id=$1", uid)
            mt = await c.fetchval("SELECT count(*) FROM users u WHERE u.age IS NOT NULL AND "
                                  + MATCH_SQL.format(o="u.telegram_id"), uid)
            reps = await c.fetch("SELECT reason, count(*) AS n FROM reports WHERE target_id=$1 "
                                 "GROUP BY reason ORDER BY n DESC", uid)
            made = await c.fetchval("SELECT count(*) FROM reports WHERE user_id=$1", uid)
            ref = await ref_info(c, uid)
        status = ["подтверждена ✅" if u["verified"] == 1 else "не подтверждена"]
        if u["banned"] == 1:
            status.append("ЗАБЛОКИРОВАНА 🚫")
        if u["hidden"] == 1:
            status.append("скрыта из ленты")
        who = {"m": "парень", "f": "девушка"}.get(u["gender"] or "", "пол не указан")
        look = {"m": "парней", "f": "девушек", "any": "всех"}.get(u["looking"] or "", "не указано")
        rep_total = sum(r["n"] for r in reps)
        lines = [
            f"👤 {u['name'] or '-'}, {u['age'] or '?'} · {u['city'] or 'город не указан'}",
            f"{who}, ищет: {look}",
            f"@{u['username'] or '-'} · id {uid}",
            "Анкета: " + ", ".join(status),
            f"Настроение: {u['mood']}" if u["mood"] else None,
            f"О себе: {u['bio']}" if u["bio"] else "О себе: не заполнено",
            f"Интересы: {u['interests'].replace(',', ', ')}" if u["interests"] else None,
            "",
            f"💎 Вайбы: {u['vibes']} · серия входов: {u['streak'] or 0} дн.",
            f"❤️ Получил: лайков {got['likes']}, дизлайков {got['passes']}, пар {mt}",
            f"👉 Поставил: лайков {gave['likes']} (суперлайков {gave['supers']}), "
            f"дизлайков {gave['passes']}, пропусков {gave['skips']}",
            f"🚩 Жалоб на него: {rep_total}" + (" (" + ", ".join(f"{r['reason'] or 'Другое'}: {r['n']}" for r in reps) + ")" if reps else "")
            + f" · сам подавал жалоб: {made}",
            f"👥 Друзей: приглашено {ref['invited']}, активных {ref['active']}",
        ]
        text = "\n".join(x for x in lines if x is not None)[:4000]
        cap = text if len(text) <= 1000 else None   # подпись к фото максимум 1024 символа
        if len(photos) == 1:
            await bot.send_photo(ADMIN_ID, BufferedInputFile(photos[0], "p0.jpg"), caption=cap)
        elif len(photos) > 1:
            await bot.send_media_group(ADMIN_ID, [
                InputMediaPhoto(media=BufferedInputFile(p, f"p{i}.jpg"), caption=cap if i == 0 else None)
                for i, p in enumerate(photos[:10])])
        if not (photos and cap):
            await bot.send_message(ADMIN_ID, text)
    except Exception as e:
        logging.exception("send_profile_to_admin failed")
        try:   # чтобы сбой был виден сразу, без захода в логи Render
            await bot.send_message(ADMIN_ID, f"⚠️ Не удалось собрать анкету id {uid}: {type(e).__name__}: {str(e)[:300]}")
        except Exception:
            pass


async def notify_admin(target, name, n, reason, reporter=None):
    if not ADMIN_ID:
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🚫 Заблокировать аккаунт", callback_data=f"ban:{target}"),
        InlineKeyboardButton(text="✅ Не блокировать", callback_data=f"dis:{target}")]])
    await send_profile_to_admin(target)   # сначала анкета, кнопки решения остаются в самом низу
    try:
        who = ""
        if reporter:
            async with pool.acquire() as c:
                r = await c.fetchrow("SELECT name, username FROM users WHERE telegram_id=$1", reporter)
            who = f"\nПожаловался: {(r['name'] if r else None) or '-'}, @{(r['username'] if r else None) or '-'} (id {reporter})"
        await bot.send_message(ADMIN_ID, f"🚩 Жалоба на {name} (id {target})\nПричина: {reason}\n"
                                         f"Всего жалоб: {n}{who}", reply_markup=kb)
    except Exception:
        pass


async def api_report(request):
    uid = request["uid"]
    d = await body(request)
    try:
        target = int(d.get("target"))
    except (TypeError, ValueError):
        return err("Некорректный запрос")
    if target == uid:
        return err("Некорректный запрос")
    reason = d.get("reason") if d.get("reason") in REASONS else "Другое"
    async with pool.acquire() as c:
        await c.execute("INSERT INTO blocks VALUES ($1,$2) ON CONFLICT DO NOTHING", uid, target)
        recent = await c.fetchval(
            "SELECT count(*) FROM reports WHERE user_id=$1 AND created > now() - interval '1 day'", uid)
        if d.get("report") and recent < REPORT_LIMIT:   # лимит жалоб в сутки
            new = await c.fetchval(
                "INSERT INTO reports (user_id,target_id,reason) VALUES ($1,$2,$3) "
                "ON CONFLICT DO NOTHING RETURNING 1", uid, target, reason)
            if new:
                info = await c.fetchrow(
                    "SELECT name, (SELECT count(*) FROM reports WHERE target_id=$1) AS n "
                    "FROM users WHERE telegram_id=$1", target)
                if info:
                    asyncio.create_task(notify_admin(target, info["name"], info["n"], reason, uid))
    return web.json_response({"ok": True})


async def api_username(request):
    u = str(request.query.get("u", "")).strip()
    if not USERNAME_RE.fullmatch(u):
        return web.json_response({"ok": False, "reason": "3–20 символов: английские буквы, цифры и _"})
    if username_problem(u):
        return web.json_response({"ok": False, "reason": username_problem(u)})
    async with pool.acquire() as c:
        taken = await c.fetchval("SELECT 1 FROM users WHERE lower(username)=lower($1) AND telegram_id<>$2",
                                 u, request["uid"])
    return web.json_response({"ok": not taken, "reason": "Этот username уже занят" if taken else ""})


# ---------- АДМИН-ПАНЕЛЬ ----------
def admin_only(fn):
    async def wrap(request):
        if not (ADMIN_ID and request["real"] == ADMIN_ID):
            return err("Нет доступа", 403)
        return await fn(request)
    return wrap


def brief(r):
    ph = photo_urls(r["telegram_id"], r.get("pl"))
    return {"id": r["telegram_id"], "name": r["name"], "username": r["username"], "age": r["age"],
            "verified": r["verified"] == 1, "banned": r["banned"] == 1, "photo": ph[0] if ph else None}


async def save_active(c, pid):
    if pid:
        ADMIN_ACTIVE[ADMIN_ID] = pid
    else:
        ADMIN_ACTIVE.pop(ADMIN_ID, None)
    await c.execute("INSERT INTO admin_state (admin_id, active) VALUES ($1,$2) "
                    "ON CONFLICT (admin_id) DO UPDATE SET active=$2", ADMIN_ID, pid)


def int_or_none(v):
    try:
        return int(v)
    except (TypeError, ValueError):
        return None


async def api_admin_personas(request):
    async with pool.acquire() as c:
        rows = await c.fetch(f"SELECT u.*, {PL_SQL} FROM users u WHERE u.owner=$1 "
                             "ORDER BY u.telegram_id DESC", ADMIN_ID)
        main = await c.fetchrow(f"SELECT u.*, {PL_SQL} FROM users u WHERE u.telegram_id=$1", ADMIN_ID)
    m = brief(main) if main else {"id": ADMIN_ID, "name": None, "username": None, "age": None,
                                  "verified": False, "banned": False, "photo": None}
    return web.json_response({"active": ADMIN_ACTIVE.get(ADMIN_ID, ADMIN_ID), "main": m,
                              "items": [brief(r) for r in rows]})


async def api_admin_persona_new(request):
    """Новая пустая анкета: сразу становится активной, дальше её заполняют в обычной форме."""
    async with pool.acquire() as c:
        pid = PERSONA_BASE + await c.fetchval("SELECT nextval('persona_seq')")
        await c.execute("INSERT INTO users (telegram_id, owner) VALUES ($1,$2)", pid, ADMIN_ID)
        PERSONAS[pid] = ADMIN_ID
        await save_active(c, pid)
    return web.json_response({"id": pid})


async def api_admin_switch(request):
    pid = int_or_none((await body(request)).get("id"))
    if pid is None or (pid != ADMIN_ID and PERSONAS.get(pid) != ADMIN_ID):
        return err("Анкета не найдена", 404)
    async with pool.acquire() as c:
        await save_active(c, None if pid == ADMIN_ID else pid)
    return web.json_response({"ok": True})


async def api_admin_persona_delete(request):
    pid = int_or_none((await body(request)).get("id"))
    if pid is None or PERSONAS.get(pid) != ADMIN_ID:
        return err("Анкета не найдена", 404)
    async with pool.acquire() as c:
        async with c.transaction():
            for q in ("DELETE FROM user_photos WHERE user_id=$1", "DELETE FROM photos WHERE user_id=$1",
                      "DELETE FROM likes WHERE user_id=$1 OR target_id=$1",
                      "DELETE FROM blocks WHERE user_id=$1 OR target_id=$1",
                      "DELETE FROM reports WHERE user_id=$1 OR target_id=$1",
                      "DELETE FROM messages WHERE a=$1 OR b=$1", "DELETE FROM daily WHERE user_id=$1",
                      "DELETE FROM tasks WHERE user_id=$1", "DELETE FROM verifications WHERE user_id=$1",
                      "DELETE FROM referrals WHERE invitee=$1 OR referrer=$1",
                      "DELETE FROM users WHERE telegram_id=$1"):
                await c.execute(q, pid)
        was_active = ADMIN_ACTIVE.get(ADMIN_ID) == pid
        PERSONAS.pop(pid, None)
        BANNED.discard(pid)
        if was_active:
            await save_active(c, None)
    return web.json_response({"ok": True, "was_active": was_active})


async def api_admin_search(request):
    q = clean_text(request.query.get("q"), 40).lstrip("@")
    if not q:
        return web.json_response({"items": []})
    like = "%" + q.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_") + "%"   # «_» в username — не шаблон
    num = int(q) if q.isdigit() and len(q) < 19 else None
    async with pool.acquire() as c:
        rows = await c.fetch(
            f"""SELECT u.*, {PL_SQL}, (SELECT count(*) FROM reports r WHERE r.target_id=u.telegram_id) AS rep
                FROM users u
                WHERE u.username ILIKE $1 OR u.name ILIKE $1 OR u.telegram_id=$2
                ORDER BY (lower(u.username)=lower($3)) DESC, u.username NULLS LAST LIMIT 30""",
            like, num, q)
    return web.json_response({"items": [dict(brief(r), rep=r["rep"]) for r in rows]})


async def api_admin_user(request):
    uid = int_or_none(request.query.get("id"))
    if uid is None:
        return err("Некорректный запрос")
    async with pool.acquire() as c:
        u = await c.fetchrow(f"SELECT u.*, {PL_SQL} FROM users u WHERE u.telegram_id=$1", uid)
        if not u:
            return err("Пользователь не найден", 404)
        reps = await c.fetch("SELECT reason, count(*) AS n FROM reports WHERE target_id=$1 "
                             "GROUP BY reason ORDER BY n DESC", uid)
        chats = await c.fetch(
            """SELECT o.other, o.n, o.ts, u.name, u.username, u.banned, m.text AS last, m.sender
               FROM (SELECT CASE WHEN a=$1 THEN b ELSE a END AS other, count(*) AS n, max(id) AS lid,
                            max(extract(epoch from created))::bigint AS ts
                     FROM messages WHERE a=$1 OR b=$1 GROUP BY 1) o
               LEFT JOIN users u ON u.telegram_id=o.other
               JOIN messages m ON m.id=o.lid
               ORDER BY o.lid DESC LIMIT 100""", uid)
    info = dict(brief(u), bio=u["bio"], mood=u["mood"],
                interests=[x for x in (u["interests"] or "").split(",") if x],
                persona=uid in PERSONAS, vibes=u["vibes"], gender=u["gender"], looking=u["looking"])
    return web.json_response({
        "user": info,
        "reports": [{"reason": r["reason"] or "Другое", "n": r["n"]} for r in reps],
        "chats": [{"id": r["other"], "n": r["n"], "ts": r["ts"], "name": r["name"], "username": r["username"],
                   "banned": r["banned"] == 1, "last": (r["last"] or "")[:80], "from_user": r["sender"] == uid}
                  for r in chats]})


async def api_admin_chat(request):
    a, b = int_or_none(request.query.get("a")), int_or_none(request.query.get("b"))
    if a is None or b is None:
        return err("Некорректный запрос")
    async with pool.acquire() as c:
        rows = await c.fetch(
            """SELECT id, sender, text, extract(epoch from created)::bigint AS ts FROM messages
               WHERE a=LEAST($1::bigint,$2::bigint) AND b=GREATEST($1::bigint,$2::bigint)
               ORDER BY id DESC LIMIT 500""", a, b)
        names = {r["telegram_id"]: r for r in await c.fetch(
            "SELECT telegram_id, name, username FROM users WHERE telegram_id = ANY($1::bigint[])", [a, b])}

    def who(i):
        r = names.get(i)
        return {"id": i, "name": r["name"] if r else None, "username": r["username"] if r else None}
    return web.json_response({"a": who(a), "b": who(b), "items": [
        {"id": r["id"], "sender": r["sender"], "text": r["text"], "ts": r["ts"]} for r in reversed(rows)]})


async def api_admin_ban(request):
    d = await body(request)
    uid = int_or_none(d.get("id"))
    if uid is None:
        return err("Некорректный запрос")
    if uid == ADMIN_ID:
        return err("Себя заблокировать нельзя")
    await set_ban(uid, bool(d.get("on")))
    return web.json_response({"ok": True})


ADMIN_VIBES_MAX = 100_000


async def api_admin_vibes(request):
    """Начислить (delta > 0) или забрать (delta < 0) вайбы. Баланс не уходит ниже нуля."""
    d = await body(request)
    uid, delta = int_or_none(d.get("id")), int_or_none(d.get("delta"))
    if uid is None or not delta or abs(delta) > ADMIN_VIBES_MAX:
        return err("Некорректный запрос")
    async with pool.acquire() as c:
        async with c.transaction():
            old = await c.fetchval(
                "SELECT vibes FROM users WHERE telegram_id=$1 AND age IS NOT NULL FOR UPDATE", uid)
            vibes = None
            if old is not None:
                vibes = await c.fetchval(
                    "UPDATE users SET vibes=GREATEST(vibes+$2,0) WHERE telegram_id=$1 RETURNING vibes", uid, delta)
                await log_vibes(c, uid, vibes - old, "admin")
    if vibes is None:
        return err("Пользователь не найден или без анкеты", 404)
    logging.info("admin vibes: user=%s delta=%s balance=%s", uid, delta, vibes)
    return web.json_response({"ok": True, "vibes": vibes})


async def api_admin_verify(request):
    d = await body(request)
    uid = int_or_none(d.get("id"))
    if uid is None:
        return err("Некорректный запрос")
    async with pool.acquire() as c:
        ok = await c.fetchval("UPDATE users SET verified=$2 WHERE telegram_id=$1 RETURNING 1",
                              uid, 1 if d.get("on") else 0)
    return web.json_response({"ok": True}) if ok else err("Пользователь не найден", 404)


async def photos_of(c, uid):
    rows = await c.fetch("SELECT slot, v FROM user_photos WHERE user_id=$1 ORDER BY slot", uid)
    return [photo_url(uid, r["slot"], r["v"]) for r in rows]


async def api_photo_post(request):
    """Загрузка фото в слот 0..2. Слоты идут подряд: новое фото можно добавить только в первый свободный."""
    uid = request["uid"]
    try:
        slot = int(request.query.get("slot", "0"))
    except ValueError:
        return err("Некорректный запрос")
    data = await request.read()
    if len(data) > 600_000 or data[:3] != b"\xff\xd8\xff":
        return err("Нужна фотография в формате JPEG до 600 КБ")
    async with pool.acquire() as c:
        async with c.transaction():
            n = await c.fetchval("SELECT count(*) FROM user_photos WHERE user_id=$1", uid)
            if slot < 0 or slot >= MAX_PHOTOS or slot > n:
                return err("Некорректный запрос")
            await c.execute(
                f"INSERT INTO user_photos (user_id, slot, data, v) VALUES ($1,$2,$3,{VNOW}) "
                f"ON CONFLICT (user_id, slot) DO UPDATE SET data=$3, v={VNOW}", uid, slot, data)
        ph = await photos_of(c, uid)
    return web.json_response({"photos": ph, "photo": ph[0]})


async def api_photo_delete(request):
    uid = request["uid"]
    try:
        slot = int(request.query.get("slot", "-1"))
    except ValueError:
        return err("Некорректный запрос")
    async with pool.acquire() as c:
        async with c.transaction():
            n = await c.fetchval("SELECT count(*) FROM user_photos WHERE user_id=$1", uid)
            if n <= 1:
                return err("В анкете должно остаться хотя бы одно фото")
            if not await c.fetchval("DELETE FROM user_photos WHERE user_id=$1 AND slot=$2 RETURNING 1", uid, slot):
                return err("Фото не найдено", 404)
            for k in range(slot + 1, MAX_PHOTOS):   # сдвигаем оставшиеся, чтобы слоты шли подряд
                await c.execute(f"UPDATE user_photos SET slot=$2, v={VNOW} WHERE user_id=$1 AND slot=$3",
                                uid, k - 1, k)
        ph = await photos_of(c, uid)
    return web.json_response({"photos": ph, "photo": ph[0]})


async def photo_get(request):
    try:
        uid = int(request.match_info["uid"])
        slot = int(request.query.get("s", "0"))
    except ValueError:
        raise web.HTTPNotFound()
    if not hmac.compare_digest(photo_token(uid), request.match_info["tok"]):
        raise web.HTTPNotFound()
    async with pool.acquire() as c:
        data = await c.fetchval("SELECT data FROM user_photos WHERE user_id=$1 AND slot=$2", uid, slot)
    if not data:
        raise web.HTTPNotFound()
    return web.Response(body=bytes(data), content_type="image/jpeg",
                        headers={"Cache-Control": "private, max-age=86400",
                                 "X-Content-Type-Options": "nosniff"})


def gesture_path(g):
    return os.path.join(BASE_DIR, g[2])


def example_gestures():
    """Жесты, для которых рядом с main.py лежит видео-пример (в порядке списка GESTURES)."""
    return [g for g in GESTURES if os.path.exists(gesture_path(g))]


def pick_gesture():
    """Случайный жест из тех, у кого есть пример. Если видео нет совсем, выбираем из всех жестов."""
    return random.choice(example_gestures() or GESTURES)


async def example_video(request):
    gs = example_gestures()
    n = int_or_none(request.match_info.get("n", "0"))
    if n is None or not 0 <= n < len(gs):
        return web.Response(status=404)
    return web.FileResponse(gesture_path(gs[n]), headers={"Cache-Control": "public, max-age=3600"})


async def api_channel(request):
    uid = request["uid"]
    if uid in PERSONAS:   # у анкет админа нет настоящего Telegram-аккаунта: подписку проверить нельзя
        return err("Для анкет админа это задание недоступно")
    if not CHANNEL:
        return err("Задание пока недоступно")
    try:
        m = await bot.get_chat_member(CHANNEL, uid)
    except Exception:
        return err("Не удалось проверить подписку, попробуй позже")
    if m.status not in ("member", "administrator", "creator"):
        return err("Подписка не найдена. Подпишись на канал и нажми «Проверить» ещё раз")
    async with pool.acquire() as c:
        if await c.fetchval("SELECT vibes FROM users WHERE telegram_id=$1 AND age IS NOT NULL", uid) is None:
            return err("Сначала создай анкету")
        new = await c.fetchval("INSERT INTO tasks VALUES ($1,'channel') ON CONFLICT DO NOTHING RETURNING 1", uid)
        if new:
            await c.execute("UPDATE users SET vibes=vibes+$2, earned=earned+$2 WHERE telegram_id=$1", uid, CHANNEL_BONUS)
            await log_vibes(c, uid, CHANNEL_BONUS, "channel")
        vibes = await c.fetchval("SELECT vibes FROM users WHERE telegram_id=$1", uid)
    return web.json_response({"vibes": vibes, "awarded": bool(new)})


async def notify_ref(referrer):
    try:
        await bot.send_message(referrer, f"🎉 Твой друг освоился в KIVO! +{REF_BONUS} вайбов уже на твоём счёте.")
    except Exception:
        pass


async def register_ref(uid, raw):
    try:
        ref = int(raw)
    except ValueError:
        return
    if ref == uid or not 0 < ref < 2 ** 62:
        return
    async with pool.acquire() as c:
        if await c.fetchval("SELECT 1 FROM users WHERE telegram_id=$1 AND age IS NOT NULL", uid):
            return   # уже зарегистрирован: приглашением не считается
        if not await c.fetchval("SELECT 1 FROM users WHERE telegram_id=$1 AND age IS NOT NULL AND banned=0", ref):
            return
        await c.execute("INSERT INTO referrals (invitee, referrer) VALUES ($1,$2) ON CONFLICT DO NOTHING", uid, ref)


# ---------- БОТ ----------
@router.message(CommandStart())
async def cmd_start(message: Message, command: CommandObject):
    if command.args == "verify":
        await start_verify(message)
        return
    if (command.args or "").startswith("ref_"):
        await register_ref(message.from_user.id, command.args[4:])
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⚡️ Открыть KIVO", web_app=WebAppInfo(url=WEBAPP_URL))]
    ])
    await message.answer(
        "👋 Добро пожаловать в **KIVO** — знакомства для тех, кому 18+.\n\n"
        "Нажми кнопку, создай анкету и ставь «Нравится».",
        reply_markup=keyboard, parse_mode="Markdown")


@router.message(Command("verify"))
async def cmd_verify(message: Message):
    await start_verify(message)


async def start_verify(message: Message):
    uid = message.from_user.id
    if not ADMIN_ID:
        await message.answer("Подтверждение анкеты пока недоступно.")
        return
    async with pool.acquire() as c:
        u = await c.fetchrow("SELECT age, verified FROM users WHERE telegram_id=$1", uid)
        pending = await c.fetchval("SELECT 1 FROM verifications WHERE user_id=$1 AND status='pending'", uid)
    if not u or u["age"] is None:
        await message.answer("Сначала создай анкету в приложении, потом возвращайся сюда.")
        return
    if pending:
        await message.answer("Твой кружок уже на проверке. Дождись ответа модератора.")
        return
    if u["verified"] == 1:
        await message.answer("Твоя анкета уже подтверждена ✅")
        return
    gesture = pick_gesture()
    awaiting[uid] = gesture
    await send_example(message, gesture)
    await message.answer(
        f"Запиши кружок (круглое видео) до 30 секунд и покажи в нём этот жест:\n\n"
        f"{gesture[0]} {gesture[1]}\n\n"
        "Лицо и рука должны быть хорошо видны. "
        "Кружок увидит только модератор, в анкету он не попадёт.")


async def send_example(message, gesture):
    """Кружок-пример именно с этим жестом: как настоящий кружок, а если файл не квадратный, то как видео."""
    path = gesture_path(gesture)
    if not os.path.exists(path):
        return
    name = os.path.basename(path)
    try:
        await message.answer("Так выглядит проверка 👇")
    except Exception:
        return
    try:
        fid = EXAMPLE_NOTES.get(name)
        if fid:
            await message.answer_video_note(fid)
        else:
            sent = await message.answer_video_note(FSInputFile(path))
            EXAMPLE_NOTES[name] = sent.video_note.file_id
        return
    except Exception:
        EXAMPLE_NOTES.pop(name, None)
    try:
        await message.answer_video(FSInputFile(path), caption="Пример того, как это выглядит")
    except Exception:
        pass


@router.message(F.video_note)
async def got_circle(message: Message):
    uid = message.from_user.id
    gesture = awaiting.pop(uid, None)
    if not gesture or not ADMIN_ID:
        await message.answer("Чтобы пройти подтверждение, нажми «Подтвердить» в профиле приложения.")
        return
    async with pool.acquire() as c:
        u = await c.fetchrow("SELECT name, age, username, gender FROM users WHERE telegram_id=$1", uid)
        await c.execute(
            "INSERT INTO verifications (user_id, status) VALUES ($1,'pending') "
            "ON CONFLICT (user_id) DO UPDATE SET status='pending', comment=NULL, created=now()", uid)
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Одобрить", callback_data=f"ver:ok:{uid}"),
        InlineKeyboardButton(text="❌ Отклонить", callback_data=f"ver:no:{uid}")]])
    await send_profile_to_admin(uid)   # фото анкеты с описанием, возрастом и статистикой в подписи
    await bot.send_video_note(ADMIN_ID, message.video_note.file_id)   # кружок сразу под анкетой
    who = {"m": "парень", "f": "девушка"}.get(u["gender"] or "", "пол не указан")
    await bot.send_message(ADMIN_ID, f"Подтверждение анкеты\n{u['name']}, {u['age']}, {who}, @{u['username'] or '-'} (id {uid})\n"
                                     f"Нужный жест: {gesture[0]} {gesture[1]}", reply_markup=kb)
    await message.answer("Кружок отправлен на проверку. Когда проверим, напишем сюда.")


@router.message(F.photo | F.video)
async def need_circle(message: Message):
    if message.from_user.id in awaiting:
        await message.answer("Нужен именно кружок: круглое видео, а не фото и не обычное видео.")


async def finish_verify(uid, ok, comment=None):
    async with pool.acquire() as c:
        if ok:
            gave = await c.fetchval(
                "UPDATE users SET verified=1, vibes=vibes+$2, earned=earned+$2 "
                "WHERE telegram_id=$1 AND verified=0 RETURNING 1", uid, VERIFY_BONUS)
            if gave:
                await log_vibes(c, uid, VERIFY_BONUS, "verify")
        await c.execute("UPDATE verifications SET status=$2, comment=$3 WHERE user_id=$1",
                        uid, "approved" if ok else "rejected", comment)
    if ok:
        text = f"✅ Анкета подтверждена! У тебя значок и +{VERIFY_BONUS} вайбов."
    else:
        text = "❌ Не получилось подтвердить анкету."
        if comment:
            text += f"\nПричина: {comment}"
        text += "\nЗапиши новый кружок: /verify"
    try:
        await bot.send_message(uid, text)
    except Exception:
        pass


@router.callback_query(F.data.startswith("ver:"))
async def on_verify(cb: CallbackQuery):
    if cb.from_user.id != ADMIN_ID:
        await cb.answer()
        return
    _, verdict, raw = cb.data.split(":")
    uid = int(raw)
    if verdict == "ok":
        await finish_verify(uid, True)
        mark = "\n\n✅ Одобрено"
    elif verdict == "no":
        reject_wait[ADMIN_ID] = uid
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="Без комментария", callback_data=f"ver:nc:{uid}")]])
        await bot.send_message(ADMIN_ID, "Напиши причину отказа одним сообщением, её увидит пользователь. "
                                         "Или нажми «Без комментария».", reply_markup=kb)
        await cb.answer()
        return
    else:
        reject_wait.pop(ADMIN_ID, None)
        await finish_verify(uid, False)
        mark = "\n\n❌ Отклонено без комментария"
    try:
        await cb.message.edit_text((cb.message.text or "") + mark, reply_markup=None)
    except Exception:
        pass
    await cb.answer("Готово")


@router.callback_query(F.data.startswith("ban:"))
async def on_ban(cb: CallbackQuery):
    if cb.from_user.id != ADMIN_ID:
        await cb.answer()
        return
    uid = int(cb.data.split(":")[1])
    BANNED.add(uid)
    async with pool.acquire() as c:
        await c.execute("UPDATE users SET banned=1 WHERE telegram_id=$1", uid)
    try:
        await cb.message.edit_text((cb.message.text or "") + "\n\n🚫 Аккаунт заблокирован", reply_markup=None)
    except Exception:
        pass
    await cb.answer("Заблокирован")


async def set_ban(uid, on):
    async with pool.acquire() as c:
        if on:
            await c.execute("INSERT INTO users (telegram_id, banned) VALUES ($1, 1) "
                            "ON CONFLICT (telegram_id) DO UPDATE SET banned=1", uid)
        else:
            await c.execute("UPDATE users SET banned=0 WHERE telegram_id=$1", uid)
    if on:
        BANNED.add(uid)
    else:
        BANNED.discard(uid)


def parse_id(command):
    try:
        return int((command.args or "").split()[0])
    except (ValueError, IndexError):
        return None


@router.message(Command("ban"))
async def cmd_ban(message: Message, command: CommandObject):
    if message.from_user.id != ADMIN_ID:
        return
    uid = parse_id(command)
    if not uid:
        await message.answer("Напиши так: /ban 123456789")
    elif uid == ADMIN_ID:
        await message.answer("Себя заблокировать нельзя.")
    else:
        await set_ban(uid, True)
        await message.answer(f"🚫 Аккаунт {uid} заблокирован.")


@router.message(Command("unban"))
async def cmd_unban(message: Message, command: CommandObject):
    if message.from_user.id != ADMIN_ID:
        return
    uid = parse_id(command)
    if not uid:
        await message.answer("Напиши так: /unban 123456789")
    else:
        await set_ban(uid, False)
        await message.answer(f"✅ Аккаунт {uid} разблокирован.")


@router.callback_query(F.data.startswith("dis:"))
async def on_dismiss(cb: CallbackQuery):
    if cb.from_user.id != ADMIN_ID:
        await cb.answer()
        return
    try:
        await cb.message.edit_text((cb.message.text or "") + "\n\n✅ Оставлено, аккаунт не заблокирован",
                                   reply_markup=None)
    except Exception:
        pass
    await cb.answer("Готово")


@router.message(F.text)
async def admin_text(message: Message):
    if message.from_user.id != ADMIN_ID or ADMIN_ID not in reject_wait:
        return
    uid = reject_wait.pop(ADMIN_ID)
    await finish_verify(uid, False, message.text.strip()[:300])
    await message.answer("Отказ отправлен пользователю с твоим комментарием.")


# ---------- ВЕБ-СЕРВЕР ----------
async def handle(request):
    return web.Response(text="KIVO Bot is running!")


async def app_page(request):
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "index.html")
    try:
        with open(path, "rb") as f:
            data = f.read()
    except FileNotFoundError:
        return web.Response(text="index.html не найден рядом с main.py", status=404)
    return web.Response(body=data, content_type="text/html", charset="utf-8",
                        headers={"Cache-Control": "no-cache",
                                 "X-Content-Type-Options": "nosniff",
                                 "Referrer-Policy": "no-referrer",
                                 "Content-Security-Policy": (
                                     "default-src 'self'; "
                                     "script-src 'self' 'unsafe-inline' https://telegram.org; "
                                     "style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
                                     "font-src https://fonts.gstatic.com; "
                                     "img-src 'self' data: blob:; media-src 'self'; connect-src 'self'; "
                                     "object-src 'none'; base-uri 'none'")})


async def web_server():
    app = web.Application(middlewares=[auth], client_max_size=700_000)
    app.router.add_get("/", handle)
    app.router.add_get("/app", app_page)
    app.router.add_get("/api/me", api_me_get)
    app.router.add_post("/api/me", api_me_post)
    app.router.add_get("/api/feed", api_feed)
    app.router.add_post("/api/swipe", api_swipe)
    app.router.add_get("/api/matches", api_matches)
    app.router.add_get("/api/profile", api_profile)
    app.router.add_get("/api/messages", api_messages_get)
    app.router.add_post("/api/messages", api_messages_post)
    app.router.add_post("/api/report", api_report)
    app.router.add_post("/api/photo", api_photo_post)
    app.router.add_delete("/api/photo", api_photo_delete)
    app.router.add_post("/api/rewind", api_rewind)
    app.router.add_get("/api/vibes/history", api_vibes_history)
    app.router.add_post("/api/swipes/buy", api_swipes_buy)
    app.router.add_post("/api/channel", api_channel)
    app.router.add_get("/api/username", api_username)
    app.router.add_get("/api/admin/personas", admin_only(api_admin_personas))
    app.router.add_post("/api/admin/persona", admin_only(api_admin_persona_new))
    app.router.add_post("/api/admin/persona/delete", admin_only(api_admin_persona_delete))
    app.router.add_post("/api/admin/switch", admin_only(api_admin_switch))
    app.router.add_get("/api/admin/search", admin_only(api_admin_search))
    app.router.add_get("/api/admin/user", admin_only(api_admin_user))
    app.router.add_get("/api/admin/chat", admin_only(api_admin_chat))
    app.router.add_post("/api/admin/ban", admin_only(api_admin_ban))
    app.router.add_post("/api/admin/verify", admin_only(api_admin_verify))
    app.router.add_post("/api/admin/vibes", admin_only(api_admin_vibes))
    app.router.add_get("/p/{uid}/{tok}", photo_get)
    app.router.add_get("/verify.mp4", example_video)
    app.router.add_get("/verify/{n}.mp4", example_video)
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", int(os.getenv("PORT", 10000)))
    await site.start()


def ru_plural(n, one, few, many):
    n = abs(int(n))
    if n % 10 == 1 and n % 100 != 11:
        return one
    if 2 <= n % 10 <= 4 and not 12 <= n % 100 <= 14:
        return few
    return many


async def send_streak_reminders():
    """Когда до конца дня осталось <= REMIND_HOURS часов, а серия ещё не продлена сегодня, шлём напоминание.
    Один раз в день на человека; отметка ставится до отправки, поэтому дублей не будет."""
    async with pool.acquire() as c:
        left = await c.fetchval(
            "SELECT extract(epoch from (date_trunc('day', now() AT TIME ZONE 'Europe/Moscow') + interval '1 day') "
            "- (now() AT TIME ZONE 'Europe/Moscow'))")
        if not REMIND_MIN_LEFT <= left <= REMIND_HOURS * 3600:
            return
        rows = await c.fetch(
            f"""UPDATE users u SET streak_remind_day={TODAY}
                WHERE u.owner IS NULL AND u.age IS NOT NULL AND COALESCE(u.banned,0)=0
                  AND COALESCE(u.remind_off,0)=0 AND u.streak>={REMIND_MIN_STREAK}
                  AND u.last_streak_day={TODAY}-1
                  AND u.streak_remind_day IS DISTINCT FROM {TODAY}
                RETURNING u.telegram_id, u.streak,
                  COALESCE((SELECT d.likes FROM daily d WHERE d.user_id=u.telegram_id AND d.day={TODAY}),0) AS likes,
                  COALESCE((SELECT d.passes FROM daily d WHERE d.user_id=u.telegram_id AND d.day={TODAY}),0) AS passes""")
        for r in rows:
            try:
                sw = await swipe_info(c, r["telegram_id"])
            except Exception:
                sw = None
            need_swipes = max(0, STREAK_SWIPES - (r["likes"] + r["passes"]))
            need_likes = max(0, STREAK_LIKES - r["likes"])
            n = r["streak"]
            reward = STREAK_BONUS[min(n + 1, 7) - 1]
            hours = max(1, round(left / 3600))
            todo = f"{need_swipes} {ru_plural(need_swipes, 'свайп', 'свайпа', 'свайпов')}"
            if need_likes:
                todo += f", из них минимум {need_likes} {ru_plural(need_likes, 'лайк', 'лайка', 'лайков')}"
            text = (f"🔥 Серия {n} {ru_plural(n, 'день', 'дня', 'дней')} в KIVO скоро сгорит: "
                    f"до конца дня около {hours} ч.\n\n"
                    f"Сделай ещё {todo}, и серия продолжится, а за сегодняшний день получишь +{reward} вайбов.")
            if sw and sw["left"] <= 0 and sw["reset_in"]:
                text += f"\n\nСвайпы сейчас закончились, они обновятся через {fmt_wait(sw['reset_in'])}."
            kb = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="⚡️ Открыть KIVO", web_app=WebAppInfo(url=WEBAPP_URL))],
                [InlineKeyboardButton(text="🔕 Не напоминать", callback_data="remind:off")]])
            try:
                await bot.send_message(r["telegram_id"], text, reply_markup=kb)
            except Exception:
                pass   # человек заблокировал бота или недоступен
            await asyncio.sleep(0.05)   # не упираемся в лимиты Telegram


async def reminder_loop():
    await asyncio.sleep(60)
    while True:
        try:
            await send_streak_reminders()
        except Exception:
            logging.exception("streak reminders failed")
        await asyncio.sleep(600)


@router.callback_query(F.data == "remind:off")
async def remind_off(cb: CallbackQuery):
    async with pool.acquire() as c:
        await c.execute("UPDATE users SET remind_off=1 WHERE telegram_id=$1", cb.from_user.id)
    await cb.answer("Напоминания выключены. Включить обратно: /remind", show_alert=True)
    try:
        await cb.message.edit_reply_markup(reply_markup=InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="⚡️ Открыть KIVO", web_app=WebAppInfo(url=WEBAPP_URL))]]))
    except Exception:
        pass


@router.message(Command("remind"))
async def cmd_remind(message: Message):
    """Включает или выключает напоминания о серии."""
    async with pool.acquire() as c:
        off = await c.fetchval(
            "UPDATE users SET remind_off = CASE WHEN COALESCE(remind_off,0)=1 THEN 0 ELSE 1 END "
            "WHERE telegram_id=$1 AND age IS NOT NULL RETURNING remind_off", message.from_user.id)
    if off is None:
        await message.answer("Сначала создай анкету в приложении.")
    elif off:
        await message.answer("🔕 Напоминания о серии выключены. Чтобы включить, снова нажми /remind.")
    else:
        await message.answer("🔔 Напоминания о серии включены: напишу, если серия будет под угрозой.")


async def main():
    global BOT_USERNAME
    await init_db()
    BOT_USERNAME = (await bot.get_me()).username
    dp = Dispatcher()
    dp.include_router(router)
    await bot.delete_webhook(drop_pending_updates=True)
    await asyncio.gather(web_server(), dp.start_polling(bot), reminder_loop())


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO)
    asyncio.run(main())
