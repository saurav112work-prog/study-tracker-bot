"""
Telegram Study Tracker Bot

Python 3.10+
Install:
    pip install "python-telegram-bot[job-queue]>=20.7,<22"

Run:
    export BOT_TOKEN="123456:your-token"
    python main.py

All persistent application data is stored in study_tracker.sqlite3.
"""

from __future__ import annotations

import html
import asyncio
import logging
import os
import re
import sqlite3
import traceback
import math
from io import BytesIO
from functools import wraps
from typing import Awaitable, Callable
from collections import Counter, defaultdict, deque
from contextlib import closing
from datetime import date, datetime, timedelta, timezone, time as dt_time
from pathlib import Path
from typing import Any, Iterable, Optional
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

from PIL import Image, ImageDraw, ImageFont

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import BadRequest, TelegramError
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    ChatMemberHandler,
    filters,
)


BOT_TOKEN = os.getenv("BOT_TOKEN", "PUT_BOT_TOKEN_HERE")
DB_PATH = "/data/study_tracker.sqlite3"
DEFAULT_TIMEZONE = "Asia/Kolkata"
DEFAULT_DAILY_GOAL = 60
MAX_CALLBACK_TEXT = 55
TIMEZONE_CHOICES = [
    ("🇮🇳 Asia/Kolkata (IST)", "Asia/Kolkata"),
    ("🇬🇧 Europe/London", "Europe/London"),
    ("🇺🇸 America/New_York", "America/New_York"),
    ("🇺🇸 America/Los_Angeles", "America/Los_Angeles"),
    ("🇦🇪 Asia/Dubai", "Asia/Dubai"),
    ("🇸🇬 Asia/Singapore", "Asia/Singapore"),
    ("🇯🇵 Asia/Tokyo", "Asia/Tokyo"),
    ("🇦🇺 Australia/Sydney", "Australia/Sydney"),
    ("🇪🇺 Europe/Berlin", "Europe/Berlin"),
]

logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    level=os.getenv("LOG_LEVEL", "INFO").upper(),
)
LOGGER = logging.getLogger("study_tracker")

# Owner-only administration. Configure your numeric Telegram user ID(s) in
# Railway as OWNER_IDS, e.g. OWNER_IDS=123456789. Usernames are intentionally
# not used because Telegram usernames can change.
def _parse_owner_ids(value: str) -> set[int]:
    ids: set[int] = set()
    for part in (value or "").split(","):
        part = part.strip()
        if not part:
            continue
        try:
            value_int = int(part)
            if value_int > 0:
                ids.add(value_int)
        except ValueError:
            LOGGER.warning("Ignoring invalid OWNER_IDS value: %r", part)
    return ids

OWNER_IDS = _parse_owner_ids(os.getenv("OWNER_IDS", "") or os.getenv("OWNER_ID", ""))
BOT_STARTED_AT = utc_now() if "utc_now" in globals() else datetime.now(timezone.utc)
OWNER_ERROR_LOG = deque(maxlen=80)

class OwnerErrorBufferHandler(logging.Handler):
    """Keep a small in-memory error tail for the owner dashboard.

    This does not replace Railway/stdout logging; it only makes recent errors
    visible from Telegram while the current process is running.
    """
    def emit(self, record: logging.LogRecord) -> None:
        try:
            if record.levelno >= logging.ERROR:
                OWNER_ERROR_LOG.append({
                    "time": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC"),
                    "level": record.levelname,
                    "message": self.format(record),
                })
        except Exception:
            pass

OWNER_LOG_HANDLER = OwnerErrorBufferHandler()
OWNER_LOG_HANDLER.setLevel(logging.ERROR)
OWNER_LOG_HANDLER.setFormatter(logging.Formatter("%(levelname)s | %(name)s | %(message)s"))
LOGGER.addHandler(OWNER_LOG_HANDLER)


def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def iso_now() -> str:
    return utc_now().isoformat(timespec="seconds")


def parse_iso(value: Optional[str]) -> Optional[datetime]:
    if not value:
        return None
    try:
        parsed = datetime.fromisoformat(value)
        return parsed if parsed.tzinfo else parsed.replace(tzinfo=timezone.utc)
    except (ValueError, TypeError):
        return None


def safe_html(value: Any) -> str:
    return html.escape(str(value), quote=False)


SMALL_CAPS = str.maketrans({
    **dict(zip("abcdefghijklmnopqrstuvwxyz", "ᴀʙᴄᴅᴇғɢʜɪᴊᴋʟᴍɴᴏᴘǫʀsᴛᴜᴠᴡxʏᴢ")),
    **dict(zip("ABCDEFGHIJKLMNOPQRSTUVWXYZ", "ᴀʙᴄᴅᴇғɢʜɪᴊᴋʟᴍɴᴏᴘǫʀsᴛᴜᴠᴡxʏᴢ")),
})

def small_caps(value: Any) -> str:
    return safe_html(str(value).translate(SMALL_CAPS))


def minutes_text(seconds: int | float) -> str:
    total = max(0, int(seconds))
    hours, minutes = divmod(total // 60, 60)
    if hours and minutes:
        return f"{hours}h {minutes}m"
    if hours:
        return f"{hours}h"
    return f"{minutes}m"


def compact_duration(seconds: int | float) -> str:
    """Human-friendly duration: 30m, 1h, 1h 30m."""
    total = max(0, int(seconds))
    hours, remainder = divmod(total, 3600)
    minutes = remainder // 60
    if hours and minutes:
        return f"{hours}h {minutes}m"
    if hours:
        return f"{hours}h"
    return f"{minutes}m"


def elapsed_text(seconds: int | float) -> str:
    """Elapsed timer display: 12m 30s, 1h 02m 30s."""
    total = max(0, int(seconds))
    hours, remainder = divmod(total, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f"{hours}h {minutes:02d}m {secs:02d}s"
    return f"{minutes}m {secs:02d}s"


def duration_text(seconds: int | float) -> str:
    return elapsed_text(seconds)


def timezone_abbreviation(value: datetime, zone: ZoneInfo) -> str:
    try:
        local = value.astimezone(zone)
        return local.tzname() or zone.key
    except Exception:
        return zone.key


def format_local_datetime_with_zone(value: datetime, zone: ZoneInfo) -> str:
    local = value.astimezone(zone)
    return f"{local.day} {local.strftime('%b %Y')}, {local.strftime('%I:%M %p').lstrip('0')} ({timezone_abbreviation(local, zone)})"


def parse_duration_input(value: str, *, max_minutes: int) -> Optional[int]:
    """Parse easy duration input such as 30m, 1h, 1h 30m, 90 minutes."""
    raw = value.strip().lower().replace("–", "-").replace("—", "-")
    if not raw:
        return None
    if raw.isdigit():
        minutes = int(raw)
        return minutes * 60 if 1 <= minutes <= max_minutes else None
    normalized = re.sub(r"\s+", "", raw)
    normalized = normalized.replace("minutes", "m").replace("minute", "m").replace("mins", "m").replace("min", "m")
    normalized = normalized.replace("hours", "h").replace("hour", "h").replace("hrs", "h").replace("hr", "h")
    match = re.fullmatch(r"(?:(\d+)h)?(?:(\d+)m)?", normalized)
    if not match or (match.group(1) is None and match.group(2) is None):
        return None
    hours = int(match.group(1) or 0)
    minutes = int(match.group(2) or 0)
    # "90m" / "90 minutes" is intentionally valid; only mixed forms
    # such as "1h 60m" reject minutes >= 60.
    if match.group(1) is not None and minutes >= 60:
        return None
    total_minutes = hours * 60 + minutes
    if not 1 <= total_minutes <= max_minutes:
        return None
    return total_minutes * 60


def mention_html(user: Any) -> str:
    name = getattr(user, "first_name", None) or getattr(user, "username", None) or "Student"
    user_id = getattr(user, "id", None)
    return (
        f'<a href="tg://user?id={int(user_id)}">{safe_html(name)}</a>'
        if user_id
        else safe_html(name)
    )


def row_mention_html(row: sqlite3.Row | dict[str, Any]) -> str:
    user_id = int(row["user_id"])
    name = row["name"] if isinstance(row, dict) and "name" in row else row["first_name"] or row["username"] or "Student"
    return f'<a href="tg://user?id={user_id}">{safe_html(name)}</a>'


def timezone_label(zone: ZoneInfo) -> str:
    now = datetime.now(timezone.utc).astimezone(zone)
    if zone.key == DEFAULT_TIMEZONE:
        return "Asia/Kolkata (IST)"
    abbreviation = now.tzname() or zone.key
    return f"{zone.key} ({abbreviation})"


def local_datetime_text(user_id: int, value: Optional[str], *, include_zone: bool = True) -> str:
    parsed = parse_iso(value)
    if not parsed:
        return "—"
    zone = DB.timezone(user_id)
    result = parsed.astimezone(zone).strftime("%A, %-d %B %Y · %I:%M %p")
    return f"{result} · {timezone_label(zone)}" if include_zone else result


def short_date(value: Optional[str]) -> str:
    if not value:
        return "—"
    try:
        return datetime.fromisoformat(value).strftime("%d %b %Y")
    except ValueError:
        return value[:10]


def valid_date(value: str) -> bool:
    try:
        date.fromisoformat(value)
        return True
    except ValueError:
        return False


def parse_user_time(value: str) -> Optional[dt_time]:
    """Parse strict 24-hour or common 12-hour/AM-PM time input."""
    value = value.strip().upper().replace(".", "")
    for fmt in ("%H:%M", "%H%M", "%I:%M %p", "%I %p", "%I%p"):
        try:
            return datetime.strptime(value, fmt).time()
        except ValueError:
            continue
    return None


def valid_time(value: str) -> bool:
    return parse_user_time(value) is not None


def canonical_time(value: str) -> Optional[str]:
    parsed = parse_user_time(value)
    return parsed.strftime("%H:%M") if parsed else None


def xp_threshold_for_level(level: int) -> int:
    """Total XP required to enter a level; gentle 8% growth per level."""
    level = max(1, int(level))
    total = 0.0
    for n in range(1, level):
        total += 100.0 * (1.08 ** (n - 1))
    return int(round(total))


def level_for_xp(xp: int) -> int:
    xp = max(0, int(xp))
    level = 1
    while level < 1000 and xp >= xp_threshold_for_level(level + 1):
        level += 1
    return level


def xp_to_next_level(xp: int) -> int:
    level = level_for_xp(xp)
    return max(0, xp_threshold_for_level(level + 1) - int(xp))


def calculate_session_xp(seconds: int, target_seconds: int = 0, completed_target: bool = False, completed_tasks: int = 0) -> int:
    """Study XP: exactly 1 XP for every 2 fully studied minutes.

    XP is based only on recorded study time. Targets, timer presets, streaks,
    and plan completion do not secretly add study XP.
    """
    minutes = max(0, int(seconds)) // 60
    return minutes // 2


def xp_for_seconds(seconds: int) -> int:
    return calculate_session_xp(seconds)


def force_bold(text: str) -> str:
    if not text:
        return text
    # Screen builders may use a few explicit HTML tags (mentions/links).
    # Strip only redundant bold tags before applying the global bold wrapper.
    cleaned = re.sub(r"</?b>", "", str(text), flags=re.IGNORECASE)
    return f"<b>{cleaned}</b>"

def progress_bar(value: int, target: int, width: int = 12) -> str:
    if target <= 0:
        return "░" * width
    filled = min(width, max(0, round(width * value / target)))
    return "█" * filled + "░" * (width - filled)


def chunked(items: list[Any], size: int) -> Iterable[list[Any]]:
    for index in range(0, len(items), size):
        yield items[index : index + size]


def is_owner(user_id: Optional[int]) -> bool:
    return bool(user_id and int(user_id) in OWNER_IDS)

def owner_guard(update: Update) -> bool:
    return is_owner(user_id_from_update(update))

def owner_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("🩺 Health", callback_data="owner:health"), InlineKeyboardButton("📊 Analytics", callback_data="owner:analytics")],
        [InlineKeyboardButton("📈 Trends", callback_data="owner:trends"), InlineKeyboardButton("👥 Users", callback_data="owner:users")],
        [InlineKeyboardButton("🔎 User Lookup", callback_data="owner:user_lookup"), InlineKeyboardButton("🔴 Live Sessions", callback_data="owner:live")],
        [InlineKeyboardButton("📋 Error Logs", callback_data="owner:errors"), InlineKeyboardButton("💾 Backup", callback_data="owner:backup")],
        [InlineKeyboardButton("📢 Broadcast", callback_data="owner:broadcast"), InlineKeyboardButton("📨 Message User", callback_data="owner:message_user")],
        [InlineKeyboardButton("📣 Targeted Message", callback_data="owner:targeted"), InlineKeyboardButton("👥 Group Control", callback_data="owner:groups")],
        [InlineKeyboardButton("🧪 Notification Test", callback_data="owner:notif_test"), InlineKeyboardButton("🩺 Diagnostics", callback_data="owner:diagnostics")],
        [InlineKeyboardButton("🧹 Cleanup", callback_data="owner:cleanup"), InlineKeyboardButton("🎁 Rewards", callback_data="owner:reward")],
        [InlineKeyboardButton("👤 User Control", callback_data="owner:control"), InlineKeyboardButton("🔧 Maintenance", callback_data="owner:maintenance")],
        [InlineKeyboardButton("🧾 Audit Log", callback_data="owner:audit")],
        [InlineKeyboardButton("🔄 Refresh", callback_data="owner:home")],
    ])

def owner_back_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⬅️ Owner Dashboard", callback_data="owner:home")]])

def owner_format_uptime() -> str:
    seconds=max(0,int((utc_now()-BOT_STARTED_AT).total_seconds()))
    return elapsed_text(seconds)

def owner_db_health() -> tuple[bool, str, int]:
    try:
        path=Path(DB.path)
        size=path.stat().st_size if path.exists() else 0
        row=DB.fetchone("PRAGMA integrity_check")
        result=str(row[0]) if row else "unknown"
        return result.lower()=="ok", result, size
    except Exception as exc:
        return False, str(exc), 0

async def owner_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update):
        if update.effective_message:
            await update.effective_message.reply_text("🔒 Owner access only.")
        return
    if not update.effective_chat or update.effective_chat.type != "private":
        if update.effective_message:
            await update.effective_message.reply_text("🔐 Please use /owner in my private chat.")
        return
    ok, result, size=owner_db_health()
    users=int(DB.fetchone("SELECT COUNT(*) c FROM users")["c"] or 0)
    active=int(DB.fetchone("SELECT COUNT(*) c FROM study_sessions WHERE status IN ('active','paused')")["c"] or 0)
    groups=int(DB.fetchone("SELECT COUNT(DISTINCT chat_id) c FROM chat_members WHERE chat_id < 0")["c"] or 0)
    text=(
        "🔐 <b>Owner Dashboard</b>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"🤖 Bot: 🟢 Online\n"
        f"⏱️ Uptime: {owner_format_uptime()}\n"
        f"👥 Users: {users:,}\n"
        f"👨‍👩‍👧 Groups: {groups:,}\n"
        f"⏱️ Active sessions: {active:,}\n"
        f"💾 Database: {'🟢 Healthy' if ok else '🔴 Problem'}\n"
        f"📦 DB size: {size:,} bytes\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        "Select an owner tool below."
    )
    await send_or_edit(update, context, text, owner_keyboard())

async def owner_health_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    ok, result, size=owner_db_health()
    try:
        table_counts=[]
        for table in ("users","study_sessions","study_plans","tasks","subjects","chat_members"):
            n=int(DB.fetchone(f"SELECT COUNT(*) c FROM {table}")["c"] or 0)
            table_counts.append(f"• {table}: {n:,}")
        health="🟢 OK" if ok else "🔴 FAILED"
        text=(f"🩺 <b>Bot Health</b>\n━━━━━━━━━━━━━━━━━━━━\n"
              f"{health}\n🔧 SQLite integrity: <code>{safe_html(result)}</code>\n"
              f"💾 DB size: {size:,} bytes\n⏱️ Uptime: {owner_format_uptime()}\n\n"
              "📦 Records\n"+"\n".join(table_counts)+"\n\n"
              f"🟢 JobQueue: {'available' if context.application and context.application.job_queue else 'unavailable'}")
    except Exception as exc:
        text=f"🩺 <b>Bot Health</b>\n\n🔴 Health check error: <code>{safe_html(exc)}</code>"
    await send_or_edit(update, context, text, owner_back_keyboard())

async def owner_analytics_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, period: str = "7d") -> None:
    """Detailed owner analytics using completed/stopped study sessions."""
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private":
        return
    period = period if period in {"today", "7d", "30d", "all"} else "7d"
    now = utc_now()
    cutoff = None
    label = "All Time"
    if period == "today":
        label = "Today"
        owner_id = user_id_from_update(update)
        owner_zone = DB.timezone(owner_id) if owner_id else ZoneInfo(DEFAULT_TIMEZONE)
        local_now = now.astimezone(owner_zone)
        cutoff = local_now.replace(hour=0, minute=0, second=0, microsecond=0).astimezone(timezone.utc)
    elif period == "7d":
        label = "Last 7 Days"
        cutoff = now - timedelta(days=7)
    elif period == "30d":
        label = "Last 30 Days"
        cutoff = now - timedelta(days=30)

    rows = DB.fetchall("""SELECT id, user_id, elapsed_seconds, xp_awarded, ended_at, created_at
                         FROM study_sessions
                         WHERE status IN ('completed','stopped')""")
    sessions = []
    for r in rows:
        ts = parse_iso(r["ended_at"] or r["created_at"])
        if cutoff and (not ts or ts < cutoff):
            continue
        sessions.append(r)
    total_users = int(DB.fetchone("SELECT COUNT(*) c FROM users")["c"] or 0)
    active_users = len({int(r["user_id"]) for r in sessions})
    total_seconds = sum(int(r["elapsed_seconds"] or 0) for r in sessions)
    total_xp = sum(int(r["xp_awarded"] or 0) for r in sessions)
    session_count = len(sessions)
    avg_seconds = int(total_seconds / session_count) if session_count else 0
    subject_rows = DB.fetchall("""SELECT s.subject_id, sub.name, SUM(s.elapsed_seconds) seconds
                                FROM study_sessions s JOIN subjects sub ON sub.id=s.subject_id
                                WHERE s.status IN ('completed','stopped')
                                GROUP BY s.subject_id, sub.name ORDER BY seconds DESC LIMIT 5""")
    # For filtered periods, calculate subject totals from the filtered session set.
    if cutoff:
        filtered_subjects = defaultdict(int)
        for r in sessions:
            sidrow = DB.fetchone("SELECT subject_id FROM study_sessions WHERE id=?", (int(r["id"]),)) if "id" in r.keys() else None
            if sidrow:
                filtered_subjects[int(sidrow["subject_id"])] += int(r["elapsed_seconds"] or 0)
        if filtered_subjects:
            ids = sorted(filtered_subjects, key=filtered_subjects.get, reverse=True)[:5]
            subject_rows = []
            for sid in ids:
                sr = DB.fetchone("SELECT name FROM subjects WHERE id=?", (sid,))
                subject_rows.append({"name": sr["name"] if sr else f"Subject {sid}", "seconds": filtered_subjects[sid]})

    recent = sorted(sessions, key=lambda r: parse_iso(r["ended_at"] or r["created_at"]) or datetime.min.replace(tzinfo=timezone.utc), reverse=True)[:5]
    recent_lines = []
    for r in recent:
        u = DB.user(int(r["user_id"]))
        name = safe_html((u["first_name"] or u["username"] or str(r["user_id"]))[:22]) if u else str(r["user_id"])
        recent_lines.append(f"• {name} · {minutes_text(int(r['elapsed_seconds'] or 0))} · +{int(r['xp_awarded'] or 0)} XP")
    subject_lines = [f"• {safe_html(r['name'])} — {minutes_text(int(r['seconds'] or 0))}" for r in subject_rows]
    text = (
        f"📈 <b>Detailed Analytics — {label}</b>\n━━━━━━━━━━━━━━━━━━━━\n"
        f"👥 Total users: {total_users:,}\n"
        f"🔥 Active users: {active_users:,}\n"
        f"📚 Sessions: {session_count:,}\n"
        f"⏱️ Study time: {minutes_text(total_seconds)}\n"
        f"⏳ Avg session: {minutes_text(avg_seconds)}\n"
        f"⭐ XP generated: {total_xp:,}\n\n"
        "📚 Top subjects\n" + ("\n".join(subject_lines) if subject_lines else "• No recorded study yet.") + "\n\n"
        "🕒 Recent sessions\n" + ("\n".join(recent_lines) if recent_lines else "• No sessions in this period.")
    )
    if len(text) > 3900:
        text = text[:3860] + "…"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("Today", callback_data="owner:analytics:today"), InlineKeyboardButton("7 Days", callback_data="owner:analytics:7d")],
        [InlineKeyboardButton("30 Days", callback_data="owner:analytics:30d"), InlineKeyboardButton("All Time", callback_data="owner:analytics:all")],
        [InlineKeyboardButton("📈 Usage Trends", callback_data="owner:trends"), InlineKeyboardButton("⬅️ Owner Dashboard", callback_data="owner:home")],
    ])
    await send_or_edit(update, context, text, kb)

async def owner_trends_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Compact 14-day study/user trend view for the owner."""
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private":
        return
    now = utc_now()
    rows = DB.fetchall("""SELECT user_id, elapsed_seconds, ended_at, created_at
                         FROM study_sessions WHERE status IN ('completed','stopped')""")
    days = []
    for offset in range(13, -1, -1):
        day = (now - timedelta(days=offset)).date()
        seconds = 0
        users = set()
        count = 0
        for r in rows:
            ts = parse_iso(r["ended_at"] or r["created_at"])
            if ts and ts.astimezone(timezone.utc).date() == day:
                seconds += int(r["elapsed_seconds"] or 0)
                users.add(int(r["user_id"]))
                count += 1
        days.append((day, seconds, len(users), count))
    max_seconds = max((x[1] for x in days), default=0)
    lines = []
    for day, seconds, users, count in days:
        width = 10 if not max_seconds else max(0, min(10, round(10 * seconds / max_seconds)))
        bar = "█" * width + "░" * (10 - width)
        lines.append(f"<code>{day.strftime('%d %b')}</code> {bar} {minutes_text(seconds)} · {users}u · {count}s")
    text = "📈 <b>Usage Trends — 14 Days</b>\n━━━━━━━━━━━━━━━━━━━━\n" + "\n".join(lines)
    text += "\n\n<i>u = active users · s = sessions</i>"
    await send_or_edit(update, context, text, owner_back_keyboard())

async def owner_user_lookup_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Ask the owner for a Telegram ID, @username, or name fragment."""
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private":
        return
    await send_prompt(
        update,
        context,
        {"kind": "owner_user_lookup"},
        "🔎 <b>User Lookup</b>\n\nEnter a Telegram user ID, @username, or part of the user's name.",
        owner_back_keyboard(),
    )


def owner_user_display(row: sqlite3.Row) -> str:
    name = safe_html((row["first_name"] or row["username"] or str(row["user_id"]))[:40])
    username = f"@{safe_html(row['username'])}" if row["username"] else "No username"
    return f"<b>{name}</b> · {username} · <code>{int(row['user_id'])}</code>"


async def owner_user_detail_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private":
        return
    user = DB.user(user_id)
    if not user:
        await send_or_edit(update, context, "🔎 <b>User Lookup</b>\n\nUser not found.", owner_back_keyboard())
        return
    completed = int(DB.fetchone("SELECT COUNT(*) c FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped')", (user_id,))["c"] or 0)
    total_seconds = int(DB.fetchone("SELECT COALESCE(SUM(elapsed_seconds),0) s FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped')", (user_id,))["s"] or 0)
    subjects = DB.fetchall("SELECT name FROM subjects WHERE user_id=? ORDER BY is_default DESC,name COLLATE NOCASE", (user_id,))
    active = DB.active_session(user_id)
    last = DB.fetchone("SELECT ended_at FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped') ORDER BY ended_at DESC LIMIT 1", (user_id,))
    created = safe_html(str(user["created_at"] or "—"))
    last_text = safe_html(str(last["ended_at"] or "—")) if last else "—"
    active_text = "None"
    if active:
        active_elapsed = DB.session_seconds(active)
        active_text = f"🟢 {safe_html(active['subject_name'])} · {elapsed_text(active_elapsed)} · {safe_html(active['status'])}"
    subject_text = ", ".join(safe_html(str(r["name"])) for r in subjects) or "None"
    text=(
        "👤 <b>User Details</b>\n━━━━━━━━━━━━━━━━━━━━\n"
        f"{owner_user_display(user)}\n\n"
        f"⭐ XP: {int(user['xp']):,}\n"
        f"🏅 Level: {int(user['level'])}\n"
        f"🔥 Streak: {int(user['current_streak'])} days (best {int(user['best_streak'])})\n"
        f"⏱️ Study time: {minutes_text(total_seconds)}\n"
        f"📚 Sessions: {completed:,}\n"
        f"🌍 Timezone: {safe_html(user['timezone'])}\n"
        f"🗓️ Joined: <code>{created}</code>\n"
        f"🕒 Last study: <code>{last_text}</code>\n\n"
        f"🔴 Current session: {active_text}\n"
        f"📚 Subjects: {subject_text}"
    )
    kb=InlineKeyboardMarkup([[InlineKeyboardButton("📋 Activity", callback_data=f"owner:activity:{user_id}"), InlineKeyboardButton("📨 Message", callback_data=f"owner:message:{user_id}")],[InlineKeyboardButton("🎁 Reward XP", callback_data=f"owner:reward_user:{user_id}"), InlineKeyboardButton("👤 Control", callback_data=f"owner:control_user:{user_id}")],
        [InlineKeyboardButton("🗑️ Reset All Data", callback_data=f"owner:reset_user:{user_id}")],[InlineKeyboardButton("📥 Export", callback_data=f"owner:export:{user_id}"), InlineKeyboardButton("🔎 New Lookup", callback_data="owner:user_lookup")],[InlineKeyboardButton("⬅️ User List", callback_data="owner:users")],[InlineKeyboardButton("🏠 Owner Dashboard", callback_data="owner:home")]])
    await send_or_edit(update, context, text, kb)


async def owner_user_activity_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private":
        return
    user = DB.user(user_id)
    if not user:
        await send_or_edit(update, context, "📋 <b>User Activity</b>\n\nUser not found.", owner_back_keyboard())
        return
    zone = DB.timezone(user_id)
    sessions = DB.fetchall("""SELECT s.*, sub.name subject_name FROM study_sessions s
                             LEFT JOIN subjects sub ON sub.id=s.subject_id
                             WHERE s.user_id=? ORDER BY COALESCE(s.ended_at,s.started_at,s.created_at) DESC LIMIT 8""", (user_id,))
    plans = DB.fetchall("""SELECT plan_date, plan_time, task, planned_minutes, completed FROM study_plans
                         WHERE user_id=? ORDER BY plan_date DESC, plan_time DESC LIMIT 5""", (user_id,))
    achievements = DB.fetchall("""SELECT a.name, ua.earned_at FROM user_achievements ua
                                JOIN achievements a ON a.id=ua.achievement_id
                                WHERE ua.user_id=? ORDER BY ua.earned_at DESC LIMIT 5""", (user_id,))
    name = safe_html((user["first_name"] or user["username"] or str(user_id))[:30])
    lines = [f"📋 <b>User Activity — {name}</b>", "━━━━━━━━━━━━━━━━━━━━", "📚 Recent sessions"]
    if sessions:
        for r in sessions:
            started = parse_iso(r["started_at"])
            ended = parse_iso(r["ended_at"])
            when = ended or started
            when_text = when.astimezone(zone).strftime("%d %b %I:%M %p").lstrip("0") if when else "—"
            status = "🟢" if r["status"] == "active" else ("⏸️" if r["status"] == "paused" else "✅")
            lines.append(f"{status} {when_text} · {safe_html(r['subject_name'] or 'Unknown')} · {minutes_text(int(r['elapsed_seconds'] or 0))}")
    else:
        lines.append("• None")
    lines.append("\n📅 Recent plans")
    if plans:
        for r in plans:
            mark = "✅" if int(r["completed"] or 0) else "⬜"
            lines.append(f"{mark} {safe_html(r['plan_date'])} {safe_html(r['plan_time'])} · {safe_html(r['task'])[:45]}")
    else:
        lines.append("• None")
    lines.append("\n🏆 Recent achievements")
    if achievements:
        for r in achievements:
            earned = parse_iso(r["earned_at"])
            when = earned.astimezone(zone).strftime("%d %b %Y") if earned else "—"
            lines.append(f"🏅 {safe_html(r['name'])} · {when}")
    else:
        lines.append("• None")
    text = "\n".join(lines)
    if len(text) > 3900:
        text = text[:3860] + "…"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("👤 User Details", callback_data=f"owner:user:{user_id}"), InlineKeyboardButton("🔎 New Lookup", callback_data="owner:user_lookup")],
        [InlineKeyboardButton("⬅️ User List", callback_data="owner:users"), InlineKeyboardButton("🏠 Owner Dashboard", callback_data="owner:home")],
    ])
    await send_or_edit(update, context, text, kb)


async def owner_users_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    rows=DB.fetchall("""SELECT u.user_id,u.username,u.first_name,u.timezone,u.xp,u.level,u.current_streak,
        (SELECT MAX(ended_at) FROM study_sessions s WHERE s.user_id=u.user_id) last_study
        FROM users u ORDER BY u.updated_at DESC LIMIT 15""")
    lines=[]
    for r in rows:
        name=safe_html((r['first_name'] or r['username'] or str(r['user_id']))[:28])
        handle=f"@{safe_html(r['username'])}" if r['username'] else f"ID {int(r['user_id'])}"
        lines.append(f"• <b>{name}</b> — {handle}\n  ⭐ {int(r['xp']):,} XP · Lv {int(r['level'])} · 🔥 {int(r['current_streak'])}")
    text="👥 <b>Recent Users</b>\n━━━━━━━━━━━━━━━━━━━━\n"+(("\n".join(lines)) if lines else "No users yet.")
    await send_or_edit(update, context, text, owner_back_keyboard())

async def owner_live_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    rows=DB.fetchall("""SELECT s.id,s.user_id,s.status,s.started_at,s.elapsed_seconds,s.target_seconds,
        u.first_name,u.username,sub.name subject_name FROM study_sessions s
        JOIN users u ON u.user_id=s.user_id JOIN subjects sub ON sub.id=s.subject_id
        WHERE s.status IN ('active','paused') ORDER BY s.started_at DESC""")
    lines=[]
    now=utc_now()
    for r in rows:
        elapsed=int(r['elapsed_seconds'] or 0)
        if r['status']=='active' and r['started_at']:
            st=parse_iso(r['started_at'])
            if st: elapsed += max(0,int((now-st).total_seconds()))
        name=safe_html((r['first_name'] or r['username'] or str(r['user_id']))[:20])
        status='🟢' if r['status']=='active' else '⏸️'
        lines.append(f"{status} <b>{name}</b> · {safe_html(r['subject_name'])} · {elapsed_text(elapsed)}")
    text="🔴 <b>Live Sessions</b>\n━━━━━━━━━━━━━━━━━━━━\n"+(("\n".join(lines)) if lines else "No active or paused sessions.")
    await send_or_edit(update, context, text, owner_back_keyboard())

async def owner_errors_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not OWNER_ERROR_LOG:
        text="📋 <b>Recent Error Logs</b>\n━━━━━━━━━━━━━━━━━━━━\n🟢 No errors captured since this process started."
    else:
        lines=[]
        for item in list(OWNER_ERROR_LOG)[-12:]:
            msg=safe_html(item['message'])
            if len(msg)>700: msg=msg[:700]+"…"
            lines.append(f"<code>{safe_html(item['time'])}</code>\n<code>{msg}</code>")
        text="📋 <b>Recent Error Logs</b>\n━━━━━━━━━━━━━━━━━━━━\n"+"\n\n".join(lines)
        if len(text) > 3800:
            text = text[:3780] + "…"
    await send_or_edit(update, context, text, owner_back_keyboard())

async def owner_backup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update): return
    if not update.effective_chat or update.effective_chat.type != "private": return
    try:
        backup_dir=Path(DB.path).parent / "owner_backups"
        backup_dir.mkdir(parents=True,exist_ok=True)
        stamp=utc_now().strftime("%Y%m%d_%H%M%S")
        target=backup_dir / f"study_tracker_backup_{stamp}.sqlite3"
        source=DB.connect()
        dest=sqlite3.connect(str(target))
        try:
            source.backup(dest)
        finally:
            dest.close(); source.close()
        size=target.stat().st_size
        with target.open("rb") as fh:
            await context.bot.send_document(chat_id=int(update.effective_chat.id),document=fh,filename=target.name,caption=f"💾 SQLite backup created successfully\n📦 Size: {size:,} bytes")
        # Keep only the newest 5 owner backups to avoid filling /data.
        backups=sorted(backup_dir.glob("study_tracker_backup_*.sqlite3"),key=lambda x:x.stat().st_mtime,reverse=True)
        for old in backups[5:]:
            try: old.unlink()
            except OSError: pass
    except Exception as exc:
        LOGGER.exception("Owner database backup failed")
        await update.effective_message.reply_text(f"🔴 Backup failed: <code>{safe_html(exc)}</code>",parse_mode=ParseMode.HTML)

class Database:
    """Small synchronous SQLite repository. Every query is parameterized."""

    def __init__(self, path: str):
        raw_path = os.path.expanduser(path).strip()
        # Accept a common Railway copy/paste mistake gracefully:
        # STUDY_TRACKER_DB=STUDY_TRACKER_DB=/data/study_tracker.sqlite3
        if raw_path.startswith("STUDY_TRACKER_DB="):
            raw_path = raw_path.split("=", 1)[1].strip()
        self.path = raw_path
        if self.path != ":memory:":
            database_parent = Path(self.path).parent
            try:
                database_parent.mkdir(parents=True, exist_ok=True)
            except OSError as exc:
                raise RuntimeError(
                    f"Cannot create SQLite directory '{database_parent}'. "
                    "Check the Railway Volume mount path and STUDY_TRACKER_DB variable."
                ) from exc
        LOGGER.info("Using PERSISTENT SQLite database at %s", self.path)
        self.initialize()
        try:
            db_file = Path(self.path)
            LOGGER.info("SQLite database ready: exists=%s size=%d bytes", db_file.exists(), db_file.stat().st_size if db_file.exists() else 0)
        except OSError:
            LOGGER.exception("Could not stat SQLite database at startup")

    def connect(self) -> sqlite3.Connection:
        # Railway Volume persistence: keep the SQLite database as a single
        # durable file on /data. DELETE journaling avoids relying on a separate
        # -wal sidecar during redeploys, while FULL synchronous mode makes each
        # committed write durable before the transaction returns.
        connection = sqlite3.connect(self.path, timeout=30)
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute("PRAGMA busy_timeout = 30000")
        connection.execute("PRAGMA journal_mode = DELETE")
        connection.execute("PRAGMA synchronous = FULL")
        return connection

    def initialize(self) -> None:
        with closing(self.connect()) as db:
            db.executescript(
                """
                CREATE TABLE IF NOT EXISTS users (
                    user_id INTEGER PRIMARY KEY,
                    username TEXT,
                    first_name TEXT NOT NULL DEFAULT '',
                    timezone TEXT NOT NULL DEFAULT 'Asia/Kolkata',
                    xp INTEGER NOT NULL DEFAULT 0,
                    level INTEGER NOT NULL DEFAULT 1,
                    current_streak INTEGER NOT NULL DEFAULT 0,
                    best_streak INTEGER NOT NULL DEFAULT 0,
                    streak_freezes INTEGER NOT NULL DEFAULT 1,
                    last_streak_warning_date TEXT,
                    last_study_local_date TEXT,
                    created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS subjects (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    name TEXT NOT NULL,
                    is_default INTEGER NOT NULL DEFAULT 0,
                    created_at TEXT NOT NULL,
                    UNIQUE(user_id, name COLLATE NOCASE),
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS study_sessions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    chat_id INTEGER,
                    subject_id INTEGER NOT NULL,
                    status TEXT NOT NULL CHECK(status IN ('active','paused','completed','stopped')),
                    started_at TEXT,
                    original_started_at TEXT,
                    paused_at TEXT,
                    ended_at TEXT,
                    elapsed_seconds INTEGER NOT NULL DEFAULT 0,
                    target_seconds INTEGER NOT NULL DEFAULT 0,
                    xp_awarded INTEGER NOT NULL DEFAULT 0,
                    notification_sent INTEGER NOT NULL DEFAULT 0,
                    created_at TEXT NOT NULL,
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE,
                    FOREIGN KEY(subject_id) REFERENCES subjects(id) ON DELETE CASCADE
                );
                CREATE INDEX IF NOT EXISTS idx_sessions_user_status
                    ON study_sessions(user_id, status);
                CREATE INDEX IF NOT EXISTS idx_sessions_user_ended
                    ON study_sessions(user_id, ended_at);
                CREATE TABLE IF NOT EXISTS study_session_segments (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    session_id INTEGER NOT NULL,
                    started_at TEXT NOT NULL,
                    ended_at TEXT,
                    elapsed_seconds INTEGER NOT NULL DEFAULT 0,
                    FOREIGN KEY(session_id) REFERENCES study_sessions(id) ON DELETE CASCADE
                );
                CREATE INDEX IF NOT EXISTS idx_session_segments_session ON study_session_segments(session_id, started_at);
                CREATE TABLE IF NOT EXISTS goals (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    title TEXT NOT NULL,
                    goal_type TEXT NOT NULL,
                    period TEXT NOT NULL,
                    subject_id INTEGER,
                    target_minutes INTEGER NOT NULL,
                    start_date TEXT NOT NULL,
                    end_date TEXT,
                    active INTEGER NOT NULL DEFAULT 1,
                    created_at TEXT NOT NULL,
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE,
                    FOREIGN KEY(subject_id) REFERENCES subjects(id) ON DELETE SET NULL
                );
                CREATE TABLE IF NOT EXISTS tasks (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    title TEXT NOT NULL,
                    subject_id INTEGER,
                    due_date TEXT,
                    priority TEXT NOT NULL DEFAULT 'medium',
                    recurrence TEXT NOT NULL DEFAULT 'none',
                    completed INTEGER NOT NULL DEFAULT 0,
                    created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL,
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE,
                    FOREIGN KEY(subject_id) REFERENCES subjects(id) ON DELETE SET NULL
                );
                CREATE TABLE IF NOT EXISTS study_plans (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    chat_id INTEGER,
                    plan_date TEXT NOT NULL,
                    plan_time TEXT NOT NULL,
                    subject_id INTEGER,
                    task TEXT NOT NULL,
                    planned_minutes INTEGER NOT NULL,
                    created_at TEXT NOT NULL,
                    updated_at TEXT NOT NULL DEFAULT '',
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE,
                    FOREIGN KEY(subject_id) REFERENCES subjects(id) ON DELETE SET NULL
                );
                CREATE TABLE IF NOT EXISTS achievements (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    code TEXT UNIQUE NOT NULL,
                    name TEXT NOT NULL,
                    description TEXT NOT NULL,
                    icon TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS user_achievements (
                    user_id INTEGER NOT NULL,
                    achievement_id INTEGER NOT NULL,
                    earned_at TEXT NOT NULL,
                    PRIMARY KEY(user_id, achievement_id),
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE,
                    FOREIGN KEY(achievement_id) REFERENCES achievements(id) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS settings (
                    user_id INTEGER PRIMARY KEY,
                    daily_goal_minutes INTEGER NOT NULL DEFAULT 60,
                    notifications_enabled INTEGER NOT NULL DEFAULT 1,
                    notify_daily INTEGER NOT NULL DEFAULT 1,
                    notify_study INTEGER NOT NULL DEFAULT 1,
                    notify_streak INTEGER NOT NULL DEFAULT 1,
                    notify_achievement INTEGER NOT NULL DEFAULT 1,
                    notify_task INTEGER NOT NULL DEFAULT 1,
                    notify_plan INTEGER NOT NULL DEFAULT 1,
                    notify_recap INTEGER NOT NULL DEFAULT 1,
                    daily_goal_notified_date TEXT,
                    privacy TEXT NOT NULL DEFAULT 'private',
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS chat_members (
                    chat_id INTEGER NOT NULL,
                    user_id INTEGER NOT NULL,
                    first_seen TEXT NOT NULL,
                    last_seen TEXT NOT NULL,
                    PRIMARY KEY(chat_id, user_id),
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS menu_sessions (
                    chat_id INTEGER NOT NULL,
                    message_id INTEGER NOT NULL,
                    owner_user_id INTEGER NOT NULL,
                    is_welcome INTEGER NOT NULL DEFAULT 0,
                    active INTEGER NOT NULL DEFAULT 1,
                    created_at TEXT NOT NULL,
                    last_activity_at TEXT NOT NULL,
                    expires_at TEXT,
                    PRIMARY KEY(chat_id, message_id),
                    FOREIGN KEY(owner_user_id) REFERENCES users(user_id) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS notification_events (
                    user_id INTEGER NOT NULL,
                    event_type TEXT NOT NULL,
                    event_key TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    PRIMARY KEY(user_id, event_type, event_key),
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE
                );
                CREATE TABLE IF NOT EXISTS goal_notifications (
                    user_id INTEGER NOT NULL,
                    goal_id INTEGER NOT NULL,
                    period_key TEXT NOT NULL,
                    notified_at TEXT NOT NULL,
                    PRIMARY KEY(user_id, goal_id, period_key),
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE,
                    FOREIGN KEY(goal_id) REFERENCES goals(id) ON DELETE CASCADE
                );
                """
            )
            achievements = [
                ("first_session", "First Session", "Complete your first study session", "🎉"),
                ("seven_day", "7-Day Streak", "Reach a 7-day streak", "🔥"),
                ("ten_hours", "10 Hours", "Complete 10 hours of study", "⏱️"),
                ("twenty_five_hours", "25 Hours", "Complete 25 hours of study", "📚"),
                ("fifty_hours", "50 Hours", "Complete 50 hours of study", "🌟"),
                ("hundred_hours", "100 Hours", "Complete 100 hours of study", "💯"),
                ("five_hundred_hours", "500 Hours", "Complete 500 hours of study", "🏅"),
                ("thousand_hours", "1000 Hours", "Complete 1000 hours of study", "👑"),
                ("hundred_sessions", "100 Sessions", "Complete 100 study sessions", "🎯"),
                ("thirty_day", "30-Day Streak", "Reach a 30-day streak", "🚀"),
                ("subject_master", "Subject Master", "Study one subject for 10 hours", "🧠"),
                ("comeback", "Comeback", "Return to study after a 7+ day break", "🔄"),
                ("five_hundred_xp", "500 XP", "Earn 500 XP", "⭐"),
                ("seven_day_500xp", "Streak Legend", "Reach a 7-day streak and 500 XP", "🏆"),
                ("fifteen_sessions", "15 Sessions", "Complete 15 study sessions", "🎓"),
            ]
            db.executemany(
                "INSERT OR IGNORE INTO achievements(code,name,description,icon) VALUES(?,?,?,?)",
                achievements,
            )
            # Phase 4A: genuinely new achievements. These do not duplicate the
            # existing first-session, hour-total, session-count, streak, XP,
            # subject-master or comeback achievements above.
            expanded_achievements = [
                ("early_bird_5", "Early Bird", "Complete 5 study sessions before 7:00 AM local time", "🌅"),
                ("night_owl_5", "Night Owl", "Complete 5 study sessions at or after 10:00 PM local time", "🌙"),
                ("deep_focus_90", "Deep Focus", "Complete a 90-minute study session without pausing", "🧘"),
                ("marathon_3h", "Marathoner", "Complete a single 3-hour study session", "🏃"),
                ("three_sessions_day", "Triple Threat", "Complete 3 study sessions on the same local day", "3️⃣"),
                ("subject_explorer_5", "Subject Explorer", "Study 5 different subjects", "🗺️"),
                ("weekend_4", "Weekend Warrior", "Study on 4 different weekend days", "☀️"),
                ("goal_crusher_7", "Goal Crusher", "Reach your daily study goal on 7 different local days", "🎯"),
                ("plan_finisher_10", "Plan Finisher", "Complete 10 study plans", "✅"),
                ("active_days_14", "Two-Week Rhythm", "Study on 14 different local calendar days", "📆"),
                ("subject_switcher_3", "Subject Switcher", "Study 3 different subjects in one local day", "🔄"),
                ("five_day_variety", "Variety Week", "Study at least 2 subjects on each of 5 different local days", "🌈"),
            ]
            db.executemany(
                "INSERT OR IGNORE INTO achievements(code,name,description,icon) VALUES(?,?,?,?)",
                expanded_achievements,
            )
            # A small migration keeps databases created by an older copy usable.
            session_columns = {
                row["name"] for row in db.execute("PRAGMA table_info(study_sessions)").fetchall()
            }
            if "notification_sent" not in session_columns:
                db.execute(
                    "ALTER TABLE study_sessions ADD COLUMN notification_sent INTEGER NOT NULL DEFAULT 0"
                )
            if "chat_id" not in session_columns:
                db.execute(
                    "ALTER TABLE study_sessions ADD COLUMN chat_id INTEGER"
                )
            if "message_id" not in session_columns:
                db.execute("ALTER TABLE study_sessions ADD COLUMN message_id INTEGER")
            if "original_started_at" not in session_columns:
                db.execute("ALTER TABLE study_sessions ADD COLUMN original_started_at TEXT")
            db.execute("UPDATE study_sessions SET original_started_at=COALESCE(original_started_at,created_at,started_at)")
            db.execute("""CREATE TABLE IF NOT EXISTS study_session_segments (
                id INTEGER PRIMARY KEY AUTOINCREMENT, session_id INTEGER NOT NULL,
                started_at TEXT NOT NULL, ended_at TEXT, elapsed_seconds INTEGER NOT NULL DEFAULT 0,
                FOREIGN KEY(session_id) REFERENCES study_sessions(id) ON DELETE CASCADE
            )""")
            db.execute("CREATE INDEX IF NOT EXISTS idx_session_segments_session ON study_session_segments(session_id, started_at)")
            task_columns = {row["name"] for row in db.execute("PRAGMA table_info(tasks)").fetchall()}
            if "recurrence" not in task_columns:
                db.execute("ALTER TABLE tasks ADD COLUMN recurrence TEXT NOT NULL DEFAULT 'none'")
            plan_columns = {row["name"] for row in db.execute("PRAGMA table_info(study_plans)").fetchall()}
            if "chat_id" not in plan_columns:
                db.execute("ALTER TABLE study_plans ADD COLUMN chat_id INTEGER")
            settings_columns = {
                row["name"] for row in db.execute("PRAGMA table_info(settings)").fetchall()
            }
            new_settings_columns = {
                "notify_goal": "INTEGER NOT NULL DEFAULT 1",
                "notify_daily": "INTEGER NOT NULL DEFAULT 1",
                "notify_study": "INTEGER NOT NULL DEFAULT 1",
                "notify_streak": "INTEGER NOT NULL DEFAULT 1",
                "notify_achievement": "INTEGER NOT NULL DEFAULT 1",
                "notify_task": "INTEGER NOT NULL DEFAULT 1",
                "notify_plan": "INTEGER NOT NULL DEFAULT 1",
                "notify_recap": "INTEGER NOT NULL DEFAULT 1",
                "daily_goal_notified_date": "TEXT",
            }
            for column, definition in new_settings_columns.items():
                if column not in settings_columns:
                    db.execute(f"ALTER TABLE settings ADD COLUMN {column} {definition}")
            user_columns = {row["name"] for row in db.execute("PRAGMA table_info(users)").fetchall()}
            new_user_columns = {
                "streak_freezes": "INTEGER NOT NULL DEFAULT 1",
                "last_streak_warning_date": "TEXT",
                "last_study_local_date": "TEXT",
                "dm_chat_id": "INTEGER",
            }
            for column, definition in new_user_columns.items():
                if column not in user_columns:
                    db.execute(f"ALTER TABLE users ADD COLUMN {column} {definition}")
            db.execute("""
                CREATE TABLE IF NOT EXISTS scheduled_alerts (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    user_id INTEGER NOT NULL,
                    chat_id INTEGER NOT NULL,
                    plan_id INTEGER,
                    alert_key TEXT NOT NULL UNIQUE,
                    alert_type TEXT NOT NULL,
                    scheduled_for TEXT NOT NULL,
                    sent_at TEXT,
                    created_at TEXT NOT NULL,
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE,
                    FOREIGN KEY(plan_id) REFERENCES study_plans(id) ON DELETE CASCADE
                )
            """)
            db.execute("""
                CREATE TABLE IF NOT EXISTS recap_events (
                    user_id INTEGER NOT NULL,
                    chat_id INTEGER NOT NULL,
                    period_type TEXT NOT NULL,
                    period_key TEXT NOT NULL,
                    sent_at TEXT NOT NULL,
                    PRIMARY KEY(user_id, period_type, period_key),
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE
                )
            """)
            db.execute("""
                CREATE TABLE IF NOT EXISTS streak_freeze_days (
                    user_id INTEGER NOT NULL,
                    protected_date TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    PRIMARY KEY(user_id, protected_date),
                    FOREIGN KEY(user_id) REFERENCES users(user_id) ON DELETE CASCADE
                )
            """)
            db.execute("""
                CREATE TABLE IF NOT EXISTS owner_audit_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    owner_id INTEGER NOT NULL,
                    action TEXT NOT NULL,
                    target_user_id INTEGER,
                    details TEXT,
                    created_at TEXT NOT NULL
                )
            """)
            db.execute("""
                CREATE TABLE IF NOT EXISTS bot_state (
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL DEFAULT '',
                    updated_at TEXT NOT NULL
                )
            """)
            db.execute("""
                CREATE TABLE IF NOT EXISTS bot_chats (
                    chat_id INTEGER PRIMARY KEY,
                    chat_type TEXT NOT NULL,
                    title TEXT NOT NULL DEFAULT '',
                    username TEXT,
                    first_seen TEXT NOT NULL,
                    last_seen TEXT NOT NULL,
                    active INTEGER NOT NULL DEFAULT 1,
                    owner_blocked INTEGER NOT NULL DEFAULT 0
                )
            """)
            db.execute("""
                INSERT OR IGNORE INTO bot_chats(chat_id,chat_type,title,first_seen,last_seen,active,owner_blocked)
                SELECT chat_id, CASE WHEN chat_id < 0 THEN 'group' ELSE 'unknown' END, '', MIN(first_seen), MAX(last_seen), 1, 0
                FROM chat_members WHERE chat_id < 0 GROUP BY chat_id
            """)
            user_columns = {row["name"] for row in db.execute("PRAGMA table_info(users)").fetchall()}
            if "owner_blocked" not in user_columns:
                db.execute("ALTER TABLE users ADD COLUMN owner_blocked INTEGER NOT NULL DEFAULT 0")
            db.execute("INSERT OR IGNORE INTO bot_state(key,value,updated_at) VALUES('maintenance_mode','0',?)", (iso_now(),))
            plan_columns={row["name"] for row in db.execute("PRAGMA table_info(study_plans)").fetchall()}
            for col,definition in {"priority":"TEXT NOT NULL DEFAULT 'medium'","reminder_minutes":"INTEGER NOT NULL DEFAULT -1","recurrence":"TEXT NOT NULL DEFAULT 'none'","recurrence_days":"TEXT NOT NULL DEFAULT ''","completed":"INTEGER NOT NULL DEFAULT 0","carried_over":"INTEGER NOT NULL DEFAULT 0","updated_at":"TEXT NOT NULL DEFAULT ''"}.items():
                if col not in plan_columns: db.execute(f"ALTER TABLE study_plans ADD COLUMN {col} {definition}")
            db.execute("UPDATE study_plans SET updated_at=COALESCE(NULLIF(updated_at,''),created_at)")
            db.execute("CREATE INDEX IF NOT EXISTS idx_plans_datetime ON study_plans(plan_date, plan_time)")
            alert_cols={row["name"] for row in db.execute("PRAGMA table_info(scheduled_alerts)").fetchall()}
            for col,definition in {"message_id":"INTEGER","dm_message_id":"INTEGER","expires_at":"TEXT"}.items():
                if col not in alert_cols: db.execute(f"ALTER TABLE scheduled_alerts ADD COLUMN {col} {definition}")
            db.execute("CREATE INDEX IF NOT EXISTS idx_alerts_pending ON scheduled_alerts(scheduled_for, sent_at)")
            menu_columns={row["name"] for row in db.execute("PRAGMA table_info(menu_sessions)").fetchall()}
            if "last_activity_at" not in menu_columns:
                db.execute("ALTER TABLE menu_sessions ADD COLUMN last_activity_at TEXT")
                db.execute("UPDATE menu_sessions SET last_activity_at=COALESCE(created_at,?) WHERE last_activity_at IS NULL", (iso_now(),))
            db.execute("CREATE INDEX IF NOT EXISTS idx_recap_events ON recap_events(period_type, period_key)")
            # XP migration: the canonical system is now 1 XP per 2 fully
            # studied minutes. Recalculate historical recorded-session XP so
            # existing users immediately follow the same rules without losing
            # any study history.
            db.execute("UPDATE study_sessions SET xp_awarded=CAST(MAX(0, elapsed_seconds) / 120 AS INTEGER) WHERE status IN ('completed','stopped')")
            for user_row in db.execute("SELECT user_id FROM users").fetchall():
                uid = int(user_row["user_id"])
                total_xp = int(db.execute("SELECT COALESCE(SUM(xp_awarded),0) FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped')", (uid,)).fetchone()[0] or 0)
                db.execute("UPDATE users SET xp=?, level=?, updated_at=? WHERE user_id=?", (total_xp, level_for_xp(total_xp), iso_now(), uid))
            # Older versions tracked ordinary user messages for cleanup. Do not
            # allow those legacy rows to be deleted by the new cleanup policy.
            db.execute("UPDATE menu_sessions SET active=0,is_welcome=0")
            db.commit()

    def execute(self, sql: str, params: tuple[Any, ...] = ()) -> int:
        with closing(self.connect()) as db:
            cursor = db.execute(sql, params)
            db.commit()
            return cursor.lastrowid or cursor.rowcount

    def fetchone(self, sql: str, params: tuple[Any, ...] = ()) -> Optional[sqlite3.Row]:
        with closing(self.connect()) as db:
            return db.execute(sql, params).fetchone()

    def fetchall(self, sql: str, params: tuple[Any, ...] = ()) -> list[sqlite3.Row]:
        with closing(self.connect()) as db:
            return db.execute(sql, params).fetchall()

    def transaction(self, statements: list[tuple[str, tuple[Any, ...]]]) -> None:
        with closing(self.connect()) as db:
            for sql, params in statements:
                db.execute(sql, params)
            db.commit()

    def ensure_user(self, telegram_user: Any) -> sqlite3.Row:
        now = iso_now()
        with closing(self.connect()) as db:
            db.execute(
                """
                INSERT INTO users(user_id,username,first_name,created_at,updated_at)
                VALUES(?,?,?,?,?)
                ON CONFLICT(user_id) DO UPDATE SET
                    username=excluded.username,
                    first_name=excluded.first_name,
                    updated_at=excluded.updated_at
                """,
                (
                    telegram_user.id,
                    telegram_user.username or "",
                    telegram_user.first_name or "",
                    now,
                    now,
                ),
            )
            db.execute(
                "INSERT OR IGNORE INTO settings(user_id) VALUES(?)", (telegram_user.id,)
            )
            defaults = [("Mathematics", "📐"), ("Physics", "⚛️"), ("Chemistry", "🧪"), ("Biology", "🧬")]
            for name, _icon in defaults:
                db.execute(
                    "INSERT OR IGNORE INTO subjects(user_id,name,is_default,created_at) VALUES(?,?,1,?)",
                    (telegram_user.id, name, now),
                )
            # Older databases may contain legacy default subjects. Preserve their
            # history but no longer treat them as system defaults.
            db.execute(
                "UPDATE subjects SET is_default=0 WHERE user_id=? AND name COLLATE NOCASE IN ('English','Other')",
                (telegram_user.id,),
            )
            db.commit()
            return db.execute("SELECT * FROM users WHERE user_id=?", (telegram_user.id,)).fetchone()

    def settings(self, user_id: int) -> sqlite3.Row:
        row = self.fetchone("SELECT * FROM settings WHERE user_id=?", (user_id,))
        if row:
            return row
        self.execute("INSERT OR IGNORE INTO settings(user_id) VALUES(?)", (user_id,))
        return self.fetchone("SELECT * FROM settings WHERE user_id=?", (user_id,))

    def register_chat_member(self, chat_id: int, user_id: int) -> None:
        now = iso_now()
        self.execute(
            """
            INSERT INTO chat_members(chat_id,user_id,first_seen,last_seen)
            VALUES(?,?,?,?)
            ON CONFLICT(chat_id,user_id) DO UPDATE SET last_seen=excluded.last_seen
            """,
            (chat_id, user_id, now, now),
        )

    def register_bot_chat(self, chat: Any) -> None:
        if not chat or getattr(chat, "type", None) not in {"group", "supergroup"}:
            return
        now = iso_now()
        self.execute("""
            INSERT INTO bot_chats(chat_id,chat_type,title,username,first_seen,last_seen,active,owner_blocked)
            VALUES(?,?,?,?,?,?,1,0)
            ON CONFLICT(chat_id) DO UPDATE SET
                chat_type=excluded.chat_type, title=excluded.title, username=excluded.username,
                last_seen=excluded.last_seen, active=1
        """, (int(chat.id), str(chat.type), str(chat.title or ""), getattr(chat, "username", None), now, now))

    def group_blocked(self, chat_id: int) -> bool:
        row=self.fetchone("SELECT owner_blocked FROM bot_chats WHERE chat_id=?", (int(chat_id),))
        return bool(row and int(row["owner_blocked"] or 0))

    def remember_menu(
        self,
        chat_id: int,
        message_id: int,
        owner_user_id: int,
        *,
        is_welcome: bool = False,
        expires_at: Optional[str] = None,
    ) -> None:
        self.execute(
            """
            INSERT INTO menu_sessions(chat_id,message_id,owner_user_id,is_welcome,active,created_at,last_activity_at,expires_at)
            VALUES(?,?,?,?,1,?,?,?)
            ON CONFLICT(chat_id,message_id) DO UPDATE SET
                owner_user_id=excluded.owner_user_id,
                is_welcome=excluded.is_welcome,
                active=1,
                last_activity_at=excluded.last_activity_at,
                expires_at=excluded.expires_at
            """,
            (
                chat_id,
                message_id,
                owner_user_id,
                1 if is_welcome else 0,
                iso_now(),
                iso_now(),
                expires_at,
            ),
        )

    def menu_owner(self, chat_id: int, message_id: int) -> Optional[int]:
        row = self.fetchone(
            """
            SELECT owner_user_id FROM menu_sessions
            WHERE chat_id=? AND message_id=? AND active=1
            """,
            (chat_id, message_id),
        )
        return int(row["owner_user_id"]) if row else None

    def touch_chat_activity(self, chat_id: int, message_id: int) -> None:
        self.execute("UPDATE menu_sessions SET last_activity_at=? WHERE chat_id=? AND message_id=? AND active=1", (iso_now(), chat_id, message_id))

    def deactivate_menu(self, chat_id: int, message_id: int) -> None:
        self.execute(
            "UPDATE menu_sessions SET active=0,is_welcome=0 WHERE chat_id=? AND message_id=?",
            (chat_id, message_id),
        )

    def claim_notification(self, user_id: int, event_type: str, event_key: str) -> bool:
        try:
            self.execute(
                """
                INSERT INTO notification_events(user_id,event_type,event_key,created_at)
                VALUES(?,?,?,?)
                """,
                (user_id, event_type, event_key, iso_now()),
            )
            return True
        except sqlite3.IntegrityError:
            return False

    def user(self, user_id: int) -> Optional[sqlite3.Row]:
        return self.fetchone("SELECT * FROM users WHERE user_id=?", (user_id,))

    def group_user_ids(self, chat_id: int) -> list[int]:
        return [
            int(row["user_id"])
            for row in self.fetchall(
                "SELECT user_id FROM chat_members WHERE chat_id=?",
                (chat_id,),
            )
        ]

    def leaderboard(self, period: str, user_ids: Optional[list[int]] = None) -> list[dict[str, Any]]:
        allowed = set(user_ids) if user_ids is not None else None
        today_cache: dict[int, date] = {}
        all_users = self.fetchall("SELECT * FROM users")
        totals: dict[int, dict[str, int]] = defaultdict(
            lambda: {"xp": 0, "seconds": 0, "sessions": 0}
        )
        for session in self.fetchall(
            """
            SELECT user_id, elapsed_seconds, xp_awarded, ended_at, created_at
            FROM study_sessions
            WHERE status IN ('completed','stopped')
            """
        ):
            uid = int(session["user_id"])
            if allowed is not None and uid not in allowed:
                continue
            if uid not in today_cache:
                today_cache[uid] = self.local_today(uid)
            session_day = self.local_date_for(uid, session["ended_at"] or session["created_at"])
            if not session_day:
                continue
            user_today = today_cache[uid]
            if period == "daily":
                start = end = user_today
            elif period == "weekly":
                start = user_today - timedelta(days=user_today.weekday())
                end = start + timedelta(days=6)
            else:
                start = user_today.replace(day=1)
                next_month = (start.replace(day=28) + timedelta(days=4)).replace(day=1)
                end = next_month - timedelta(days=1)
            if start <= session_day <= end:
                totals[uid]["xp"] += int(session["xp_awarded"] or 0)
                totals[uid]["seconds"] += int(session["elapsed_seconds"] or 0)
                totals[uid]["sessions"] += 1
        rows = []
        for user in all_users:
            uid = int(user["user_id"])
            if allowed is not None and uid not in allowed:
                continue
            values = totals[uid]
            if values["xp"] or values["sessions"]:
                rows.append({
                    "user_id": uid,
                    "name": user["first_name"] or user["username"] or f"User {uid}",
                    "username": user["username"] or "",
                    **values,
                })
        rows.sort(key=lambda row: (row["xp"], row["seconds"], row["sessions"]), reverse=True)
        for index, row in enumerate(rows, start=1):
            row["rank"] = index
        return rows

    def timezone(self, user_id: int) -> ZoneInfo:
        value = self.fetchone("SELECT timezone FROM users WHERE user_id=?", (user_id,))
        name = value["timezone"] if value else DEFAULT_TIMEZONE
        try:
            return ZoneInfo(name)
        except ZoneInfoNotFoundError:
            return ZoneInfo(DEFAULT_TIMEZONE)

    def local_today(self, user_id: int) -> date:
        return utc_now().astimezone(self.timezone(user_id)).date()

    def local_date_for(self, user_id: int, timestamp: Optional[str]) -> Optional[date]:
        parsed = parse_iso(timestamp)
        return parsed.astimezone(self.timezone(user_id)).date() if parsed else None

    def subjects(self, user_id: int) -> list[sqlite3.Row]:
        return self.fetchall(
            "SELECT * FROM subjects WHERE user_id=? ORDER BY is_default DESC, name COLLATE NOCASE",
            (user_id,),
        )

    def subject(self, user_id: int, subject_id: int) -> Optional[sqlite3.Row]:
        return self.fetchone(
            "SELECT * FROM subjects WHERE user_id=? AND id=?", (user_id, subject_id)
        )

    def active_session(self, user_id: int) -> Optional[sqlite3.Row]:
        return self.fetchone(
            """
            SELECT s.*, sub.name subject_name FROM study_sessions s
            JOIN subjects sub ON sub.id=s.subject_id
            WHERE s.user_id=? AND s.status IN ('active','paused')
            ORDER BY s.id DESC LIMIT 1
            """,
            (user_id,),
        )

    def session_seconds(self, session: sqlite3.Row) -> int:
        elapsed = int(session["elapsed_seconds"] or 0)
        if session["status"] == "active":
            started = parse_iso(session["started_at"])
            if started:
                elapsed += max(0, int((utc_now() - started).total_seconds()))
        return elapsed

    def completed_seconds(self, user_id: int) -> int:
        rows = self.fetchall(
            "SELECT elapsed_seconds FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped')",
            (user_id,),
        )
        return sum(int(row["elapsed_seconds"] or 0) for row in rows)

    def completed_sessions(self, user_id: int) -> list[sqlite3.Row]:
        return self.fetchall(
            """
            SELECT s.*, sub.name subject_name FROM study_sessions s
            JOIN subjects sub ON sub.id=s.subject_id
            WHERE s.user_id=? AND s.status='completed'
            ORDER BY COALESCE(s.ended_at,s.created_at) DESC
            """,
            (user_id,),
        )

    def recorded_sessions(self, user_id: int) -> list[sqlite3.Row]:
        return self.fetchall(
            """
            SELECT s.*, sub.name subject_name FROM study_sessions s
            JOIN subjects sub ON sub.id=s.subject_id
            WHERE s.user_id=? AND s.status IN ('completed','stopped')
            ORDER BY COALESCE(s.ended_at,s.created_at) DESC
            """,
            (user_id,),
        )

    def session_segments(self, session_id: int) -> list[sqlite3.Row]:
        return self.fetchall("SELECT * FROM study_session_segments WHERE session_id=? ORDER BY started_at,id", (session_id,))

    def session_original_start(self, session: sqlite3.Row) -> Optional[datetime]:
        return parse_iso(session["original_started_at"] or session["created_at"] or session["started_at"])

    def recover_active_sessions(self) -> None:
        # A process restart must never turn server downtime into study time.
        now = iso_now()
        with closing(self.connect()) as db:
            active_rows = db.execute("SELECT id,elapsed_seconds FROM study_sessions WHERE status='active'").fetchall()
            for row in active_rows:
                closed_seconds = int(db.execute("SELECT COALESCE(SUM(elapsed_seconds),0) FROM study_session_segments WHERE session_id=? AND ended_at IS NOT NULL", (row["id"],)).fetchone()[0] or 0)
                running_elapsed = max(0, int(row["elapsed_seconds"] or 0) - closed_seconds)
                db.execute("UPDATE study_session_segments SET ended_at=?,elapsed_seconds=? WHERE session_id=? AND ended_at IS NULL", (now, running_elapsed, row["id"]))
            db.execute("UPDATE study_sessions SET status='paused',started_at=NULL,paused_at=? WHERE status='active'", (now,))
            db.commit()

    def update_streak(self, user_id: int) -> tuple[int, int]:
        """Return the current/best streak without mutating progression state.

        Progression state is written only by complete_session_atomic(), which keeps
        session completion, XP, streaks, freezes and achievements in one transaction.
        """
        days: set[date] = set()
        for row in self.recorded_sessions(user_id):
            local_day = self.local_date_for(user_id, row["ended_at"] or row["created_at"])
            if local_day:
                days.add(local_day)
        for row in self.fetchall("SELECT protected_date FROM streak_freeze_days WHERE user_id=?", (user_id,)):
            try:
                days.add(date.fromisoformat(row["protected_date"]))
            except ValueError:
                pass
        if not days:
            user = self.user(user_id)
            return 0, int(user["best_streak"] or 0) if user else 0
        today = self.local_today(user_id)
        cursor = today if today in days else today - timedelta(days=1) if today - timedelta(days=1) in days else None
        current = 0
        if cursor:
            while cursor in days:
                current += 1
                cursor -= timedelta(days=1)
        best = 0
        run = 0
        previous = None
        for day in sorted(days):
            run = run + 1 if previous and day == previous + timedelta(days=1) else 1
            best = max(best, run)
            previous = day
        user = self.user(user_id)
        best = max(best, int(user["best_streak"] or 0) if user else 0)
        return current, best

    def goal_progress(self, user_id: int, goal: sqlite3.Row) -> int:
        today = self.local_today(user_id)
        if goal["period"] == "daily":
            start = end = today
        elif goal["period"] == "weekly":
            start = today - timedelta(days=today.weekday())
            end = start + timedelta(days=6)
        elif goal["period"] == "monthly":
            start = today.replace(day=1)
            next_month = (start.replace(day=28) + timedelta(days=4)).replace(day=1)
            end = next_month - timedelta(days=1)
        else:
            start = date.fromisoformat(goal["start_date"])
            end = date.fromisoformat(goal["end_date"] or today.isoformat())
        total = 0
        for row in self.completed_sessions(user_id):
            day = self.local_date_for(user_id, row["ended_at"] or row["created_at"])
            if day and start <= day <= end and (
                not goal["subject_id"] or row["subject_id"] == goal["subject_id"]
            ):
                total += int(row["elapsed_seconds"] or 0) // 60
        return total

    def check_achievements(self, user_id: int) -> list[sqlite3.Row]:
        # Kept for database compatibility; achievement mutation belongs exclusively to complete_session_atomic().
        return []

    def complete_session_atomic(self, session_id: int, user_id: int, elapsed: int, stopped: bool = False) -> dict[str, Any]:
        """Single BEGIN IMMEDIATE transaction: save session, XP, streak, achievements together."""
        elapsed=max(0,int(elapsed)); now=iso_now()
        with closing(self.connect()) as db:
            db.execute("BEGIN IMMEDIATE")
            session=db.execute("SELECT * FROM study_sessions WHERE id=? AND user_id=? AND status IN ('active','paused')",(session_id,user_id)).fetchone()
            if not session:
                db.rollback(); return {"ok":False}
            target=int(session["target_seconds"] or 0)
            completed=bool(target and elapsed>=target and not stopped)
            status="completed" if completed else "stopped"
            # Keep the real elapsed duration; completion is determined by reaching the target.
            # Completed tasks from today improve XP slightly; query timestamps in UTC then map to local.
            today=utc_now().astimezone(self.timezone(user_id)).date()
            task_count=0
            for t in db.execute("SELECT updated_at FROM study_plans WHERE user_id=? AND completed=1",(user_id,)).fetchall():
                parsed=parse_iso(t["updated_at"])
                if parsed and parsed.astimezone(self.timezone(user_id)).date()==today: task_count+=1
            xp=calculate_session_xp(elapsed,target,completed,task_count)
            if session["status"] == "active":
                closed_seconds = int(db.execute("SELECT COALESCE(SUM(elapsed_seconds),0) FROM study_session_segments WHERE session_id=? AND ended_at IS NOT NULL", (session_id,)).fetchone()[0] or 0)
                running_elapsed = max(0, elapsed - closed_seconds)
                open_segment = db.execute("SELECT id FROM study_session_segments WHERE session_id=? AND ended_at IS NULL ORDER BY id DESC LIMIT 1", (session_id,)).fetchone()
                if open_segment:
                    db.execute("UPDATE study_session_segments SET ended_at=?,elapsed_seconds=? WHERE id=?", (now, running_elapsed, int(open_segment["id"])))
            db.execute("UPDATE study_sessions SET status=?,ended_at=?,elapsed_seconds=?,xp_awarded=?,notification_sent=0 WHERE id=?",(status,now,elapsed,xp,session_id))
            user=db.execute("SELECT * FROM users WHERE user_id=?",(user_id,)).fetchone()
            old_xp=int(user["xp"] or 0); new_xp=old_xp+xp
            # All recorded study dates count for streak; partial saves therefore preserve the habit.
            rows=db.execute("SELECT ended_at,created_at FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped')",(user_id,)).fetchall()
            zone=self.timezone(user_id); days=set()
            for r in rows:
                parsed=parse_iso(r["ended_at"] or r["created_at"])
                if parsed: days.add(parsed.astimezone(zone).date())
            today=utc_now().astimezone(zone).date()
            old_last=user["last_study_local_date"]
            old_current=int(user["current_streak"] or 0)
            freezes=int(user["streak_freezes"] or 0)
            if old_last:
                try: gap=(today-date.fromisoformat(old_last)).days
                except ValueError: gap=0
                missed=max(0,gap-1)
                protect=min(missed,freezes)
                for days_back in range(1,protect+1):
                    db.execute("INSERT OR IGNORE INTO streak_freeze_days(user_id,protected_date,created_at) VALUES(?,?,?)",(user_id,(today-timedelta(days=days_back)).isoformat(),now))
                freezes-=protect
            for r in db.execute("SELECT protected_date FROM streak_freeze_days WHERE user_id=?",(user_id,)).fetchall():
                try: days.add(date.fromisoformat(r["protected_date"]))
                except ValueError: pass
            cursor=today if today in days else None; current=0
            while cursor and cursor in days:
                current+=1; cursor-=timedelta(days=1)
            best=int(user["best_streak"] or 0); run=0; prev=None
            for d in sorted(days):
                run=run+1 if prev and d==prev+timedelta(days=1) else 1; best=max(best,run); prev=d
            # One freeze is earned at each newly reached 7-day milestone, capped at 3.
            if current>old_current and current>=7 and current%7==0: freezes=min(3,freezes+1)
            comeback=bool(old_last and (today-date.fromisoformat(old_last)).days>=7) if old_last else False
            db.execute("UPDATE users SET xp=?,level=?,current_streak=?,best_streak=?,streak_freezes=?,last_study_local_date=?,updated_at=? WHERE user_id=?",(new_xp,level_for_xp(new_xp),current,best,freezes,today.isoformat(),now,user_id))
            recorded=db.execute("SELECT subject_id,elapsed_seconds FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped')",(user_id,)).fetchall()
            total_seconds=sum(int(r["elapsed_seconds"] or 0) for r in recorded)
            completed_count=db.execute("SELECT COUNT(*) FROM study_sessions WHERE user_id=? AND status='completed'",(user_id,)).fetchone()[0]
            subject_totals=Counter(int(r["subject_id"]) for r in recorded)
            subject_seconds=Counter()
            for r in recorded: subject_seconds[int(r["subject_id"])] += int(r["elapsed_seconds"] or 0)
            conditions={
                "first_session":completed_count>=1, "seven_day":current>=7, "ten_hours":total_seconds>=10*3600,
                "twenty_five_hours":total_seconds>=25*3600, "fifty_hours":total_seconds>=50*3600, "hundred_hours":total_seconds>=100*3600,
                "five_hundred_hours":total_seconds>=500*3600, "thousand_hours":total_seconds>=1000*3600, "hundred_sessions":completed_count>=100,
                "thirty_day":current>=30, "subject_master":max(subject_seconds.values(),default=0)>=10*3600, "comeback":comeback,
                "five_hundred_xp":new_xp>=500, "seven_day_500xp":current>=7 and new_xp>=500, "fifteen_sessions":completed_count>=15
            }
            # Phase 4A achievements use local calendar/time behavior and session
            # structure, so they are meaningfully different from the original set.
            local_rows = db.execute("SELECT id,subject_id,started_at,original_started_at,ended_at,elapsed_seconds FROM study_sessions WHERE user_id=? AND status='completed'", (user_id,)).fetchall()
            zone = self.timezone(user_id)
            early = 0; late = 0; three_day = Counter(); day_subjects = defaultdict(set); weekend_days = set(); active_days = set()
            for r in local_rows:
                started = parse_iso(r["original_started_at"] or r["started_at"])
                ended = parse_iso(r["ended_at"])
                local_start = started.astimezone(zone) if started else None
                local_end = ended.astimezone(zone) if ended else None
                if local_start:
                    if local_start.hour < 7: early += 1
                    if local_start.hour >= 22: late += 1
                if local_end:
                    d = local_end.date(); active_days.add(d); three_day[d] += 1; day_subjects[d].add(int(r["subject_id"]))
                    if d.weekday() >= 5: weekend_days.add(d)
            variety_days = sum(1 for vals in day_subjects.values() if len(vals) >= 2)
            subject_count = len({int(r["subject_id"]) for r in local_rows})
            deep_focus_90 = False
            for r in local_rows:
                if int(r["elapsed_seconds"] or 0) >= 90*60:
                    segs = db.execute("SELECT COUNT(*) c FROM study_session_segments WHERE session_id=?", (int(r["id"]),)).fetchone()["c"]
                    if int(segs or 0) == 1:
                        deep_focus_90 = True; break
            completed_plans = int(db.execute("SELECT COUNT(*) FROM study_plans WHERE user_id=? AND completed=1", (user_id,)).fetchone()[0] or 0)
            goal_row = db.execute("SELECT daily_goal_minutes FROM settings WHERE user_id=?", (user_id,)).fetchone()
            goal_minutes = int(goal_row[0] or 60) if goal_row else 60
            goal_days = 0
            for d, vals in day_subjects.items():
                day_minutes = sum(int(r["elapsed_seconds"] or 0) for r in local_rows if parse_iso(r["ended_at"]) and parse_iso(r["ended_at"]).astimezone(zone).date() == d) // 60
                if day_minutes >= goal_minutes:
                    goal_days += 1
            conditions.update({
                "early_bird_5": early >= 5, "night_owl_5": late >= 5,
                "deep_focus_90": deep_focus_90,
                "marathon_3h": any(int(r["elapsed_seconds"] or 0) >= 180*60 for r in local_rows),
                "three_sessions_day": max(three_day.values(), default=0) >= 3,
                "subject_explorer_5": subject_count >= 5, "weekend_4": len(weekend_days) >= 4,
                "goal_crusher_7": goal_days >= 7, "plan_finisher_10": completed_plans >= 10,
                "active_days_14": len(active_days) >= 14, "subject_switcher_3": max((len(v) for v in day_subjects.values()), default=0) >= 3,
                "five_day_variety": variety_days >= 5,
            })
            new_ach=[]
            # Partial stopped sessions do not unlock achievements; they still count XP/streak/study time.
            if not completed: conditions={k:False for k in conditions}
            for code,ready in conditions.items():
                if not ready: continue
                a=db.execute("SELECT * FROM achievements WHERE code=?",(code,)).fetchone()
                if a:
                    try:
                        db.execute("INSERT INTO user_achievements(user_id,achievement_id,earned_at) VALUES(?,?,?)",(user_id,a["id"],now));
                        new_ach.append(a)
                    except sqlite3.IntegrityError: pass
            db.commit()
            return {"ok":True,"status":status,"xp":xp,"current_streak":current,"best_streak":best,"new_achievements":new_ach,"total_seconds":total_seconds,"sessions_count":completed_count,"comeback":comeback,"streak_freezes":freezes,"ended_at":now,"completed":completed}

    def reset_statistics(self, user_id: int) -> None:
        with closing(self.connect()) as db:
            db.execute(
                "DELETE FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped')",
                (user_id,),
            )
            db.execute(
                "DELETE FROM user_achievements WHERE user_id=?", (user_id,)
            )
            db.execute("DELETE FROM streak_freeze_days WHERE user_id=?", (user_id,))
            db.execute("DELETE FROM notification_events WHERE user_id=?", (user_id,))
            db.execute("DELETE FROM recap_events WHERE user_id=?", (user_id,))
            reset_now = iso_now()
            active_rows = db.execute("SELECT id,elapsed_seconds,status FROM study_sessions WHERE user_id=? AND status IN ('active','paused')", (user_id,)).fetchall()
            for active_row in active_rows:
                if active_row["status"] == "active":
                    closed_seconds = int(db.execute("SELECT COALESCE(SUM(elapsed_seconds),0) FROM study_session_segments WHERE session_id=? AND ended_at IS NOT NULL", (active_row["id"],)).fetchone()[0] or 0)
                    seg_elapsed = max(0, int(active_row["elapsed_seconds"] or 0) - closed_seconds)
                    db.execute("UPDATE study_session_segments SET ended_at=?,elapsed_seconds=? WHERE session_id=? AND ended_at IS NULL", (reset_now, seg_elapsed, active_row["id"]))
            db.execute("UPDATE study_sessions SET status='stopped',ended_at=?,started_at=NULL,paused_at=NULL WHERE user_id=? AND status IN ('active','paused')", (reset_now,user_id))
            db.execute(
                "UPDATE users SET xp=0,level=1,current_streak=0,best_streak=0,streak_freezes=1,last_study_local_date=NULL,updated_at=? WHERE user_id=?",
                (iso_now(), user_id),
            )
            db.commit()


DB = Database(DB_PATH)


def nav_keyboard(back: str = "home") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [[
            InlineKeyboardButton("⬅️ Back", callback_data=back),
            InlineKeyboardButton("🏠 Home", callback_data="home"),
        ]]
    )


def home_keyboard() -> InlineKeyboardMarkup:
    buttons = [
        ("⏱️ Start Studying", "study"),
        ("📍 Today's Activity", "today"),
        ("📊 Dashboard", "dashboard"),
        ("📚 Subjects", "subjects"),
        ("📅 Study Plan", "plans"),
        ("📈 Statistics", "stats"),
        ("👤 Profile", "profile"),
        ("🏆 Leaderboard", "leaderboard"),
        ("⚙️ Settings", "settings"),
        ("❓ Help", "help"),
    ]
    rows=[]
    for pair in chunked(buttons,2):
        rows.append([InlineKeyboardButton(label,callback_data=data) for label,data in pair])
    return InlineKeyboardMarkup(rows)

def subject_keyboard(
    subjects: list[sqlite3.Row],
    prefix: str,
    back: str = "home",
    include_add: bool = False,
) -> InlineKeyboardMarkup:
    default_order={"Mathematics":0,"Physics":1,"Chemistry":2,"Biology":3}
    ordered=sorted(subjects,key=lambda row:(0,default_order[row["name"]]) if row["name"] in default_order else (1,str(row["name"]).lower()))
    rows = [
        [InlineKeyboardButton(f"📚 {row['name']}", callback_data=f"{prefix}:{row['id']}")]
        for row in ordered
    ]
    if include_add:
        rows.append([InlineKeyboardButton("➕ Add subject", callback_data="subject:add")])
    rows.append([
        InlineKeyboardButton("⬅️ Back", callback_data=back),
        InlineKeyboardButton("🏠 Home", callback_data="home"),
    ])
    return InlineKeyboardMarkup(rows)


def user_id_from_update(update: Update) -> Optional[int]:
    return update.effective_user.id if update.effective_user else None


def is_group_update(update: Update) -> bool:
    chat = update.effective_chat
    return bool(chat and chat.type in {"group", "supergroup"})


def is_group_chat_id(chat_id: Optional[int]) -> bool:
    # Telegram group/supergroup IDs are negative. This is only a defensive
    # guard for bot-generated background notifications; all interactive
    # updates are additionally checked by is_group_update().
    return bool(chat_id is not None and int(chat_id) < 0)


async def ensure(update: Update) -> Optional[int]:
    user=update.effective_user; chat=update.effective_chat
    if not user or not chat or chat.type not in {"private","group","supergroup"}: return None
    DB.ensure_user(user)
    if chat.type == "private":
        # A DM interaction authorizes the bot to send that user future DMs.
        DB.execute("UPDATE users SET dm_chat_id=?, updated_at=? WHERE user_id=?", (int(chat.id), iso_now(), int(user.id)))
    else:
        DB.register_chat_member(chat.id,user.id)
    return user.id


async def remember_message(message: Any, owner_user_id: int, *, is_welcome: bool = False) -> None:
    if message and getattr(message, "chat_id", None) and getattr(message, "message_id", None):
        DB.remember_menu(
            int(message.chat_id),
            int(message.message_id),
            owner_user_id,
            is_welcome=is_welcome,
        )


def cancel_prompt_job(context: ContextTypes.DEFAULT_TYPE, chat_id: int, user_id: int) -> None:
    if not context.application.job_queue:
        return
    name = f"prompt-timeout-{chat_id}-{user_id}"
    for job in context.application.job_queue.get_jobs_by_name(name):
        job.schedule_removal()


async def expire_prompt(context: ContextTypes.DEFAULT_TYPE) -> None:
    job = context.job
    if not job:
        return
    data = job.data or {}
    chat_id = data.get("chat_id")
    user_id = data.get("user_id")
    message_id = data.get("message_id")
    if chat_id is None or user_id is None:
        return
    awaiting = context.user_data.get("awaiting") if user_id is not None else None
    if message_id is not None and awaiting and int(awaiting.get("prompt_message_id", -1)) == int(message_id):
        context.user_data.pop("awaiting", None)
    if message_id is not None:
        try:
            await context.bot.delete_message(chat_id=int(chat_id), message_id=int(message_id))
        except TelegramError:
            pass
        DB.deactivate_menu(int(chat_id), int(message_id))
    # The per-user state is cleared by the command/callback that created a new
    # prompt. A timeout marker prevents an old prompt from accepting replies.
    DB.execute("UPDATE menu_sessions SET expires_at=? WHERE chat_id=? AND message_id=?", (iso_now(), int(chat_id), int(message_id or 0)))


async def send_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE, state: dict[str, Any], text: str, keyboard: Optional[InlineKeyboardMarkup] = None) -> None:
    """Render a prompt and make it expire after 30s of inactivity."""
    uid = user_id_from_update(update)
    chat = update.effective_chat
    if not uid or not chat:
        return
    context.user_data["awaiting"] = state
    cancel_prompt_job(context, int(chat.id), int(uid))
    await send_or_edit(update, context, text, keyboard)
    latest = DB.fetchone("SELECT message_id FROM menu_sessions WHERE chat_id=? AND owner_user_id=? AND active=1 ORDER BY message_id DESC LIMIT 1", (int(chat.id), int(uid)))
    if latest:
        message_id = int(latest["message_id"])
        state["prompt_message_id"] = message_id
        if chat.type in {"group", "supergroup"}:
            DB.execute("UPDATE menu_sessions SET expires_at=? WHERE chat_id=? AND message_id=?", ((utc_now()+timedelta(seconds=30)).isoformat(), int(chat.id), message_id))
            if context.application.job_queue:
                context.application.job_queue.run_once(
                    expire_prompt, 30,
                    data={"chat_id": int(chat.id), "user_id": int(uid), "message_id": message_id},
                    name=f"prompt-timeout-{chat.id}-{uid}",
                    user_id=int(uid),
                    chat_id=int(chat.id),
                )


def cancel_welcome_job(context: ContextTypes.DEFAULT_TYPE, chat_id: int, message_id: int) -> None:
    if not context.application.job_queue:
        return
    job_name = f"welcome-delete-{chat_id}-{message_id}"
    for job in context.application.job_queue.get_jobs_by_name(job_name):
        job.schedule_removal()
    DB.execute(
        "UPDATE menu_sessions SET is_welcome=0 WHERE chat_id=? AND message_id=?",
        (chat_id, message_id),
    )


async def delete_welcome_message(context: ContextTypes.DEFAULT_TYPE) -> None:
    job = context.job
    if not job:
        return
    data = job.data or {}
    chat_id = data.get("chat_id")
    message_id = data.get("message_id")
    if chat_id is None or message_id is None:
        return
    session = DB.fetchone(
        """
        SELECT owner_user_id,is_welcome,active FROM menu_sessions
        WHERE chat_id=? AND message_id=?
        """,
        (chat_id, message_id),
    )
    if not session or not session["active"] or not session["is_welcome"]:
        return
    try:
        await context.bot.delete_message(chat_id=chat_id, message_id=message_id)
    except TelegramError:
        LOGGER.info("Welcome message %s/%s was already deleted or unavailable", chat_id, message_id)
    finally:
        DB.deactivate_menu(chat_id, message_id)


async def add_group_button_for_dm(context: ContextTypes.DEFAULT_TYPE, keyboard: Optional[InlineKeyboardMarkup]) -> Optional[InlineKeyboardMarkup]:
    """Append the group-add button to every DM screen that has buttons."""
    if keyboard is None:
        return None
    try:
        me = await context.bot.get_me()
        if not me.username:
            return keyboard
        rows = [list(row) for row in keyboard.inline_keyboard]
        url = f"https://t.me/{me.username}?startgroup=study_tracker"
        if not any(getattr(btn, "url", None) == url for row in rows for btn in row):
            rows.append([InlineKeyboardButton("➕ Add to Group", url=url)])
        return InlineKeyboardMarkup(rows)
    except TelegramError:
        LOGGER.debug("Could not append DM group-add button", exc_info=True)
        return keyboard

async def send_or_edit(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str, keyboard: Optional[InlineKeyboardMarkup] = None, *, parse_mode: str = ParseMode.HTML) -> None:
    owner_id=user_id_from_update(update)
    rendered=force_bold(text)
    try:
        if update.callback_query and update.callback_query.message:
            source = update.callback_query.message
            # Profile cards (and any future image-based screen) are photo
            # messages, so Telegram cannot edit them into text. Remove the
            # old card before rendering the next screen.
            if not getattr(source, "text", None):
                try:
                    await context.bot.delete_message(chat_id=int(source.chat_id), message_id=int(source.message_id))
                except TelegramError:
                    LOGGER.debug("Could not delete previous non-text menu", exc_info=True)
                DB.deactivate_menu(int(source.chat_id), int(source.message_id))
            else:
                try:
                    await source.edit_text(rendered, reply_markup=keyboard, parse_mode=ParseMode.HTML)
                    await remember_message(source, owner_id or 0)
                    return
                except BadRequest as exc:
                    if "message is not modified" in str(exc).lower():
                        return
                    # If Telegram refuses to edit the message, replace it.
                    try:
                        await context.bot.delete_message(chat_id=int(source.chat_id), message_id=int(source.message_id))
                    except TelegramError:
                        LOGGER.debug("Could not delete uneditable menu", exc_info=True)
                    DB.deactivate_menu(int(source.chat_id), int(source.message_id))
        if update.effective_message:
            message=await update.effective_message.reply_text(rendered,reply_markup=keyboard,parse_mode=ParseMode.HTML)
            if owner_id: await remember_message(message,owner_id)
    except TelegramError:
        LOGGER.exception("Telegram API error while rendering screen")


# ---------------------------------------------------------------------------
# Dynamic profile card
# ---------------------------------------------------------------------------

_PROFILE_FONT_PATHS = (
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf",
)
_PROFILE_BOLD_FONT_PATHS = (
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation2/LiberationSans-Bold.ttf",
)


def _profile_font(size: int, *, bold: bool = False) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    paths = _PROFILE_BOLD_FONT_PATHS if bold else _PROFILE_FONT_PATHS
    for path in paths:
        try:
            return ImageFont.truetype(path, size=size)
        except OSError:
            continue
    return ImageFont.load_default()


def _fit_profile_font(text: str, max_width: int, size: int, *, bold: bool = False) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    current = max(18, size)
    while current >= 18:
        font = _profile_font(current, bold=bold)
        box = font.getbbox(text)
        if (box[2] - box[0]) <= max_width:
            return font
        current -= 2
    return _profile_font(18, bold=bold)


def _profile_draw_text(draw: ImageDraw.ImageDraw, xy: tuple[int, int], text: str, font: ImageFont.ImageFont, fill: tuple[int, int, int], *, anchor: str = "la") -> None:
    draw.text(xy, text, font=font, fill=fill, anchor=anchor)


def _profile_card_png(user: sqlite3.Row, *, total_seconds: int, tasks_done: int, current: int, best: int, earned: int, total_achievements: int, rank: int) -> BytesIO:
    """Build a fresh profile card from current database values.

    The image is intentionally generated in memory and is not persisted to
    /data. Every profile open therefore reflects the latest database state.
    """
    width, height = 1600, 980
    bg = (250, 251, 253)
    ink = (20, 24, 32)
    muted = (92, 99, 112)
    line = (224, 228, 235)
    card = (255, 255, 255)
    accent = (63, 137, 222)
    accent_soft = (221, 235, 251)
    avatar_bg = (220, 234, 250)

    image = Image.new("RGB", (width, height), bg)
    draw = ImageDraw.Draw(image)

    # Header / avatar.
    draw.ellipse((70, 50, 240, 220), fill=avatar_bg)
    first = (user["first_name"] or user["username"] or "S").strip()[:1].upper() or "S"
    avatar_font = _profile_font(82, bold=True)
    draw.text((155, 136), first, font=avatar_font, fill=(38, 78, 120), anchor="mm")

    display_name = (user["first_name"] or user["username"] or "Student").strip()
    name_font = _fit_profile_font(display_name, 760, 58, bold=True)
    draw.text((285, 85), display_name, font=name_font, fill=ink)

    created = parse_iso(user["created_at"])
    if created:
        member = created.astimezone(DB.timezone(int(user["user_id"]))).strftime("Joined %b %Y")
    else:
        member = "Joined —"
    draw.text((285, 160), member, font=_profile_font(31), fill=muted)

    level = int(user["level"] or 1)
    level_text = f"Level {level}"
    level_font = _profile_font(31, bold=True)
    level_w = level_font.getbbox(level_text)[2] - level_font.getbbox(level_text)[0]
    pill = (width - 285 - level_w - 58, 75, width - 70, 160)
    draw.rounded_rectangle(pill, radius=42, fill=accent_soft)
    draw.text(((pill[0] + pill[2]) // 2, (pill[1] + pill[3]) // 2), level_text, font=level_font, fill=(35, 75, 116), anchor="mm")

    # Four statistic cards.
    top = 270
    gap = 35
    card_w = (width - 140 - gap) // 2
    card_h = 205
    boxes = [
        (70, top, 70 + card_w, top + card_h, "Total time", minutes_text(total_seconds)),
        (70 + card_w + gap, top, width - 70, top + card_h, "Tasks done", str(tasks_done)),
        (70, top + card_h + 35, 70 + card_w, top + 2 * card_h + 35, "Current streak", f"{current} days"),
        (70 + card_w + gap, top + card_h + 35, width - 70, top + 2 * card_h + 35, "Longest streak", f"{best} days"),
    ]
    for x1, y1, x2, y2, label, value in boxes:
        draw.rounded_rectangle((x1, y1, x2, y2), radius=24, fill=card, outline=(239, 241, 245), width=2)
        draw.text((x1 + 34, y1 + 32), label, font=_profile_font(31), fill=muted)
        value_font = _fit_profile_font(value, x2 - x1 - 68, 52, bold=True)
        draw.text((x1 + 34, y1 + 101), value, font=value_font, fill=ink)

    # Achievement progress.
    section_y = 775
    draw.line((70, section_y - 30, width - 70, section_y - 30), fill=line, width=2)
    draw.text((70, section_y), "Achievements", font=_profile_font(34), fill=ink, anchor="lm")
    ach_text = f"{earned} / {total_achievements}"
    draw.text((width - 70, section_y), ach_text, font=_profile_font(34, bold=True), fill=ink, anchor="rm")
    bar_x1, bar_y1, bar_x2, bar_y2 = 70, section_y + 35, width - 70, section_y + 59
    draw.rounded_rectangle((bar_x1, bar_y1, bar_x2, bar_y2), radius=12, fill=(232, 235, 240))
    ratio = (earned / total_achievements) if total_achievements else 0
    fill_x2 = bar_x1 + int((bar_x2 - bar_x1) * min(1.0, max(0.0, ratio)))
    if fill_x2 > bar_x1:
        draw.rounded_rectangle((bar_x1, bar_y1, fill_x2, bar_y2), radius=12, fill=accent)

    # Rank.
    rank_y = 900
    draw.line((70, rank_y - 28, width - 70, rank_y - 28), fill=line, width=2)
    draw.text((70, rank_y + 10), "Leaderboard rank", font=_profile_font(34), fill=ink, anchor="lm")
    draw.text((width - 70, rank_y + 10), f"#{rank}", font=_profile_font(38, bold=True), fill=ink, anchor="rm")

    output = BytesIO()
    output.name = "profile.png"
    image.save(output, format="PNG", optimize=True)
    output.seek(0)
    return output


async def send_profile_card(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Send a fresh, temporary profile image based on live database values."""
    uid = await ensure(update)
    if not uid or not update.effective_message:
        return
    u = DB.user(uid)
    if not u:
        return
    current, best = DB.update_streak(uid)
    sessions = DB.recorded_sessions(uid)
    total = sum(int(r["elapsed_seconds"] or 0) for r in sessions)
    tasks_done = int(DB.fetchone("SELECT COUNT(*) c FROM study_plans WHERE user_id=? AND completed=1", (uid,))["c"])
    earned = int(DB.fetchone("SELECT COUNT(*) c FROM user_achievements WHERE user_id=?", (uid,))["c"])
    total_ach = int(DB.fetchone("SELECT COUNT(*) c FROM achievements")["c"])
    rank_row = DB.fetchone("SELECT COUNT(*)+1 r FROM users WHERE xp>?", (int(u["xp"] or 0),))
    rank = int(rank_row["r"]) if rank_row else 1

    photo = _profile_card_png(
        u, total_seconds=total, tasks_done=tasks_done, current=current, best=best,
        earned=earned, total_achievements=total_ach, rank=rank,
    )
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("⬅️ Back", callback_data="home"), InlineKeyboardButton("🏠 Home", callback_data="home")]
    ])

    # If Profile is opened from another menu, replace that menu instead of
    # stacking another message.
    if update.callback_query and update.callback_query.message:
        old = update.callback_query.message
        try:
            await context.bot.delete_message(chat_id=int(old.chat_id), message_id=int(old.message_id))
        except TelegramError:
            LOGGER.debug("Could not delete previous menu before profile card", exc_info=True)
        DB.deactivate_menu(int(old.chat_id), int(old.message_id))

    try:
        message = await context.bot.send_photo(
            chat_id=int(update.effective_chat.id),
            photo=photo,
            reply_markup=keyboard,
        )
        await remember_message(message, uid)
    except TelegramError:
        LOGGER.exception("Telegram API error while sending profile card")

async def reply_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str, keyboard: Optional[InlineKeyboardMarkup] = None, *, parse_mode: str = ParseMode.HTML) -> Any:
    if not update.effective_message: return None
    try:
        message=await update.effective_message.reply_text(force_bold(text),reply_markup=keyboard,parse_mode=ParseMode.HTML)
        owner_id=user_id_from_update(update)
        if owner_id: await remember_message(message,owner_id)
        return message
    except TelegramError:
        LOGGER.exception("Telegram API error while sending screen")
        return None

async def answer_callback(
    query: Any,
    text: Optional[str] = None,
    *,
    show_alert: bool = False,
) -> None:
    """Answer a Telegram callback query exactly once, without leaking errors."""
    if not query:
        return
    try:
        await query.answer(text=text, show_alert=show_alert)
    except TelegramError:
        LOGGER.debug("Callback answer failed", exc_info=True)


async def render_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid=await ensure(update)
    if not uid: return
    # The home screen is intentionally the exact group welcome experience.
    user=DB.user(uid)
    text=(f"🎓 Welcome to Study Tracker Bot {row_mention_html(user)}!\n\n"
          "Your smart study companion built to help you focus, stay consistent, and actually hit your goals.\n\n"
          "Track your sessions, crush your streaks, and watch your progress add up, one study block at a time.\n\n"
          "Let's get started 👇")
    keyboard=home_keyboard()
    if update.effective_chat and update.effective_chat.type == "private":
        keyboard=await add_group_button_for_dm(context,keyboard)
    await send_or_edit(update,context,text,keyboard)

async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data.pop("awaiting",None)
    user=update.effective_user; msg=update.effective_message; chat=update.effective_chat
    if not user or not msg or not chat or chat.type not in {"private","group","supergroup"}: return
    uid=await ensure(update)
    if not uid: return
    if DB.active_session(uid):
        await timer_screen(update, context)
        return
    await render_home(update, context)

async def help_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    text="""❓ Help

⏱️ Study — choose a subject and custom duration.
/pause, /resume, /stop — control the active session.

📅 Study Plan — add, view, edit, complete, filter and schedule study plans.
📊 Statistics — switch between Daily, Weekly, Monthly and All-Time.
📈 Dashboard — open Session History, Streak Details, Achievement Log and XP & Leveling.
🌍 Settings — change timezone, privacy, and notification preferences."""
    await send_or_edit(update,context,text,nav_keyboard('home'))

def achievement_progress(user_id: int) -> Optional[dict[str, Any]]:
    user = DB.user(user_id)
    if not user:
        return None
    recorded = DB.recorded_sessions(user_id)
    completed = DB.completed_sessions(user_id)
    total_seconds = sum(int(r["elapsed_seconds"] or 0) for r in recorded)
    current, best = DB.update_streak(user_id)
    xp = int(user["xp"] or 0)
    subject_totals = Counter()
    for row in recorded:
        subject_totals[int(row["subject_id"])] += int(row["elapsed_seconds"] or 0)
    earned_codes = {r["code"] for r in DB.fetchall("SELECT a.code FROM achievements a JOIN user_achievements ua ON ua.achievement_id=a.id WHERE ua.user_id=?", (user_id,))}
    candidates = []
    if "first_session" not in earned_codes: candidates.append((len(completed), 1, "First Session", "1 session"))
    if "seven_day" not in earned_codes: candidates.append((current, 7, "7-Day Streak", f"{max(0, 7-current)} days left"))
    if "ten_hours" not in earned_codes: candidates.append((total_seconds, 10*3600, "10 Hours", f"{max(0, 10*3600-total_seconds)//60} min left"))
    if "fifteen_sessions" not in earned_codes: candidates.append((len(completed), 15, "15 Sessions", f"{max(0, 15-len(completed))} sessions left"))
    if "five_hundred_xp" not in earned_codes: candidates.append((xp, 500, "500 XP", f"{max(0, 500-xp)} XP left"))
    if "seven_day_500xp" not in earned_codes: candidates.append((min(current/7, xp/500) * 500, 500, "7-Day Streak + 500 XP", "keep both milestones rising"))
    if "subject_master" not in earned_codes: candidates.append((max(subject_totals.values(), default=0), 10*3600, "Subject Master", f"{max(0, 10*3600-max(subject_totals.values(), default=0))//60} min left"))
    if "comeback" not in earned_codes: candidates.append((0 if not user["last_study_local_date"] else 1, 1, "Comeback", "return after a break"))
    if not candidates: return None
    # Prefer the closest meaningful progress.
    scored = []
    for current_value, target, name, remaining in candidates:
        ratio = min(1.0, float(current_value) / target) if target else 1.0
        scored.append((ratio, name, remaining))
    ratio, name, remaining = max(scored, key=lambda x: x[0])
    return {"text": f"{name} ({remaining})", "name": name, "ratio": ratio}


async def dashboard_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = await ensure(update)
    if not uid:
        return
    u = DB.user(uid)
    current, best = DB.update_streak(uid)
    sessions = DB.recorded_sessions(uid)
    total = sum(int(r["elapsed_seconds"] or 0) for r in sessions)
    completed = len(DB.completed_sessions(uid))
    earned = int(DB.fetchone("SELECT COUNT(*) c FROM user_achievements WHERE user_id=?", (uid,))["c"])
    total_ach = int(DB.fetchone("SELECT COUNT(*) c FROM achievements")["c"])
    next_badge = achievement_progress(uid)
    next_name = next_badge["name"] if next_badge else "All unlocked"
    active = DB.active_session(uid)
    totals = Counter()
    for r in sessions:
        totals[int(r["subject_id"])] += int(r["elapsed_seconds"] or 0)
    if active:
        totals[int(active["subject_id"])] += DB.session_seconds(active)
    subjects = DB.subjects(uid)
    icon_map = {"Mathematics":"➗", "Chemistry":"⚗️", "Physics":"🔬", "Biology":"🧬"}
    ordered = sorted(subjects, key=lambda r: ({"Mathematics":0,"Chemistry":1,"Physics":2,"Biology":3}.get(r["name"],99), str(r["name"]).lower()))
    lines = [
        "📊 Executive Dashboard",
        "",
        f"👤 {row_mention_html(u)}   ·   🧑‍🎓 Student",
        "━━━━━━━━━━━━━━━━━━━━",
        "🗃️ Overview:",
        "",
        f"⏱️ Total study time: {compact_duration(total)}",
        f"✅ Completed sessions: {completed}",
        f"⭐ Level {int(u['level'])} · {int(u['xp'])} XP",
        f"🔥 Current streak: {current} day{'s' if current != 1 else ''}",
        f"🏅 Best streak: {best} day{'s' if best != 1 else ''}",
        f"🛡️ Streak freeze: {int(u['streak_freezes'] or 0)} available",
        f"🏆 Achievements: {earned}/{total_ach} unlocked",
        f"➡️ Next: {safe_html(next_name)}",
        "━━━━━━━━━━━━━━━━━━━━",
        "📚 Subject Focus:",
        "",
    ]
    for sub in ordered:
        sec = totals.get(int(sub["id"]), 0)
        status = "🟢 Active" if active and int(active["subject_id"]) == int(sub["id"]) else "⏸ Standby"
        lines.append(f"{icon_map.get(sub['name'], '📘')} {safe_html(sub['name'])} — {compact_duration(sec)} · {status}")
    lines += [
        "━━━━━━━━━━━━━━━━━━━━",
        "ℹ️ Use the buttons below to explore Streaks, Achievements & XP",
    ]
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("📜 Session History", callback_data="history")],
        [InlineKeyboardButton("🔥 Streak Details", callback_data="streak"), InlineKeyboardButton("🏆 Achievement Log", callback_data="achievements")],
        [InlineKeyboardButton("⭐ XP & Leveling", callback_data="xpinfo")],
        [InlineKeyboardButton("⬅️ Back", callback_data="home"), InlineKeyboardButton("🏠 Home", callback_data="home")],
    ])
    await send_or_edit(update, context, "\n".join(lines), kb)


async def history_screen(
    update: Update, context: ContextTypes.DEFAULT_TYPE, offset: int = 0
) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    sessions = DB.recorded_sessions(user_id)
    page_size = 10
    offset = max(0, min(offset, max(0, len(sessions) - 1)))
    page = sessions[offset : offset + page_size]
    lines = [f"🕘 <b>Session history</b> · {offset + 1}–{min(offset + page_size, len(sessions))} of {len(sessions)}"]
    if not sessions:
        lines = ["🕘 <b>Session history</b>", "No study sessions saved yet."]
    for session in page:
        when = DB.local_date_for(user_id, session["ended_at"] or session["created_at"])
        lines.append(
            f"\n<b>{when.strftime('%d %b') if when else '—'}</b> · "
            f"{safe_html(session['subject_name'])} · {minutes_text(session['elapsed_seconds'])} · +{session['xp_awarded']} XP" + (" · ⏹ Saved early" if session["status"]=="stopped" else "")
        )
    controls: list[InlineKeyboardButton] = []
    if offset > 0:
        controls.append(InlineKeyboardButton("◀️ Newer", callback_data=f"history:{max(0, offset - page_size)}"))
    if offset + page_size < len(sessions):
        controls.append(InlineKeyboardButton("Older ▶️", callback_data=f"history:{offset + page_size}"))
    keyboard_rows = [controls] if controls else []
    keyboard_rows.append([
        InlineKeyboardButton("⬅️ Back", callback_data="dashboard"),
        InlineKeyboardButton("🏠 Home", callback_data="home"),
    ])
    await send_or_edit(update, context, "\n".join(lines), InlineKeyboardMarkup(keyboard_rows))


async def leaderboard_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await ensure(update)
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("📅 Daily", callback_data="leaderboard:period:daily"),
         InlineKeyboardButton("📆 Weekly", callback_data="leaderboard:period:weekly")],
        [InlineKeyboardButton("🗓️ Monthly", callback_data="leaderboard:period:monthly")],
        [InlineKeyboardButton("⬅️ Back", callback_data="home"), InlineKeyboardButton("🏠 Main Menu", callback_data="home")],
    ])
    await send_or_edit(
        update,
        context,
        "🏆 <b>Leaderboard</b>\n\nChoose a time period:",
        keyboard,
    )


async def leaderboard_scope_menu(update: Update, context: ContextTypes.DEFAULT_TYPE, period: str) -> None:
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("🌎 Global Leaderboard", callback_data=f"leaderboard:{period}:global:0")],
        [InlineKeyboardButton("⬅️ Back", callback_data="leaderboard"), InlineKeyboardButton("🏠 Main Menu", callback_data="home")],
    ])
    await send_or_edit(update, context, f"🏆 <b>{period.title()} Global Leaderboard</b>\n\nRanked across all bot users.", keyboard)


async def leaderboard_screen(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    period: str,
    scope: str,
    offset: int = 0,
) -> None:
    chat = update.effective_chat
    scope = "global"
    rows = DB.leaderboard(period, None)
    page_size = 10
    offset = max(0, min(offset, max(0, len(rows) - 1)))
    page = rows[offset : offset + page_size]
    period_title = {"daily": "Daily", "weekly": "Weekly", "monthly": "Monthly"}.get(period, "Weekly")
    scope_title = "Global"
    lines = [f"🏆 <b>{scope_title} Leaderboard · {period_title}</b>"]
    if not page:
        lines.append("\nNo completed study sessions in this period yet.")
    for row in page:
        lines.append(
            f"\n<b>#{row['rank']}</b> {row_mention_html(row)}\n"
            f"⭐ {row['xp']} XP · ⏱ {duration_text(row['seconds'])} · "
            f"📚 {row['sessions']} sessions"
        )
    controls: list[InlineKeyboardButton] = []
    if offset > 0:
        controls.append(InlineKeyboardButton("◀️ Newer", callback_data=f"leaderboard:{period}:global:{max(0, offset-page_size)}"))
    if offset + page_size < len(rows):
        controls.append(InlineKeyboardButton("Older ▶️", callback_data=f"leaderboard:{period}:global:{offset+page_size}"))
    keyboard_rows = [controls] if controls else []
    keyboard_rows.append([
        InlineKeyboardButton("📅 Periods", callback_data="leaderboard"),
        InlineKeyboardButton("⬅️ Back", callback_data="leaderboard"),
    ])
    keyboard_rows.append([InlineKeyboardButton("🏠 Main Menu", callback_data="home")])
    await send_or_edit(update, context, "\n".join(lines), InlineKeyboardMarkup(keyboard_rows))


async def achievements_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, offset: int = 0) -> None:
    """Show the complete achievement log with working pagination."""
    user_id = await ensure(update)
    if not user_id:
        return
    user = DB.user(user_id)
    rows = DB.fetchall(
        """
        SELECT a.code, a.name, a.description, a.icon, ua.earned_at
        FROM achievements a
        LEFT JOIN user_achievements ua
          ON ua.achievement_id=a.id AND ua.user_id=?
        ORDER BY a.id
        """,
        (user_id,),
    )
    page_size = 7
    offset = max(0, min(int(offset), max(0, len(rows) - 1)))
    page = rows[offset:offset + page_size]
    earned_count = sum(1 for row in rows if row["earned_at"])
    total = len(rows)

    lines = [
        "🏆 Achievement Log",
        f"👤 {row_mention_html(user)}",
        "━━━━━━━━━━━━━━━━━━━━━━━━",
        f"📊 Unlocked: {earned_count} / {total}",
        "",
    ]
    if not page:
        lines.append("No achievements are available yet.")
    else:
        for row in page:
            status = "✅" if row["earned_at"] else "🔒"
            lines.append(f"{status} {row['icon']} {safe_html(row['name'])}")
            lines.append(f"   {safe_html(row['description'])}")
            if row["earned_at"]:
                earned_at = parse_iso(row["earned_at"])
                if earned_at:
                    local = earned_at.astimezone(DB.timezone(user_id))
                    lines.append(f"   🕒 Unlocked: {local.day} {local.strftime('%b %Y, %I:%M %p').lstrip('0')}")
            lines.append("")

    controls = []
    if offset > 0:
        controls.append(InlineKeyboardButton("◀️ Previous", callback_data=f"achievements:{max(0, offset-page_size)}"))
    if offset + page_size < total:
        controls.append(InlineKeyboardButton("Next ▶️", callback_data=f"achievements:{offset+page_size}"))
    keyboard_rows = [controls] if controls else []
    keyboard_rows.append([InlineKeyboardButton("⬅️ Back", callback_data="dashboard"), InlineKeyboardButton("🏠 Home", callback_data="home")])
    await send_or_edit(update, context, "\n".join(lines).rstrip(), InlineKeyboardMarkup(keyboard_rows))


async def streak_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    user = DB.user(user_id)
    current, best = DB.update_streak(user_id)
    rows = DB.recorded_sessions(user_id)
    days = {
        DB.local_date_for(user_id, row["ended_at"] or row["created_at"])
        for row in rows
    }
    days.discard(None)
    last_day = max(days) if days else None
    milestones = [7, 14, 30, 50, 100]
    next_milestone = next((m for m in milestones if current < m), 100)
    progress_value = min(current, next_milestone)
    progress = min(100, max(0, round(progress_value / next_milestone * 100)))
    progress_text = f"{progress}% ({current}/{next_milestone})"
    bar = progress_bar(progress_value, next_milestone, 10)
    zone = DB.timezone(user_id)
    last_text = last_day.strftime("%-d %b %Y") if last_day else "—"
    text = (
        f"👤 {row_mention_html(user)} - Streak Details\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🔥 Current Streak : {current} Days\n"
        f"🏆 Best Streak    : {best} Days\n"
        f"📅 Total Active   : {len(days)} Days\n"
        f"🕒 Last Studied   : {last_text}\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🎯 Next Milestone : {next_milestone} Days\n"
        f"⏳ Progress: [{bar}] {progress_text}\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        "🎖️ Milestones: 7 · 14 · 30 · 50 · 100 days"
    )
    await send_or_edit(update, context, text, nav_keyboard("dashboard"))


async def profile_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await send_profile_card(update, context)

async def xp_info_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    user = DB.user(user_id)
    xp = int(user["xp"] or 0)
    level = int(user["level"] or 1)
    current_level_start = xp_threshold_for_level(level)
    next_level_threshold = xp_threshold_for_level(level + 1)
    span = max(1, next_level_threshold - current_level_start)
    earned_in_level = max(0, xp - current_level_start)
    pct = max(0, min(100, round(earned_in_level / span * 100)))
    remaining = max(0, next_level_threshold - xp)
    text = (
        "⭐ <b>XP & Level Status</b>\n"
        f"👤 {row_mention_html(user)}\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🏅 Level: {level}\n"
        f"⭐ Total XP: {xp:,} XP\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"📈 Level Progress: {pct}%\n"
        f"{progress_bar(earned_in_level, span, 20)}\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━\n"
        f"🎯 Next Tier: {remaining:,} XP to Level {level + 1}\n"
        "💡 Rate: +1 XP / 2 mins studied\n"
        "━━━━━━━━━━━━━━━━━━━━━━━━"
    )
    await send_or_edit(update, context, text, InlineKeyboardMarkup([[InlineKeyboardButton("📊 Dashboard", callback_data="dashboard")],[InlineKeyboardButton("⬅️ Back", callback_data="dashboard"),InlineKeyboardButton("🏠 Home", callback_data="home")]]))


async def stats_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, period: str = "week") -> None:
    uid = await ensure(update)
    if not uid:
        return
    period = {"daily":"day", "weekly":"week", "monthly":"month", "all-time":"all"}.get(period, period)
    today = DB.local_today(uid)
    sessions = DB.recorded_sessions(uid)
    def day_of(r):
        return DB.local_date_for(uid, r["ended_at"] or r["created_at"])
    daily = defaultdict(int)
    by_subject = defaultdict(int)
    for r in sessions:
        d = day_of(r)
        if d:
            daily[d] += int(r["elapsed_seconds"] or 0)
            by_subject[int(r["subject_id"])] += int(r["elapsed_seconds"] or 0)
    names = {int(s["id"]): s["name"] for s in DB.subjects(uid)}
    if period == "day":
        total = daily[today]
        yesterday = daily[today - timedelta(days=1)]
        covered = defaultdict(int)
        today_sessions = []
        for r in sessions:
            if day_of(r) == today:
                covered[int(r["subject_id"])] += int(r["elapsed_seconds"] or 0)
                today_sessions.append(r)
        longest = max((int(r["elapsed_seconds"] or 0) for r in today_sessions), default=0)
        comparison = total - yesterday
        lines = [
            "📅 Daily Statistics", "",
            f"⏱️ Total time studied today: {compact_duration(total)}", "",
            "📚 Subjects covered:",
        ]
        for sub in DB.subjects(uid):
            lines.append(f"• {safe_html(sub['name'])} — {compact_duration(covered[int(sub['id'])])}")
        current, _ = DB.update_streak(uid)
        sign = "+" if comparison >= 0 else "-"
        lines += [
            "", f"🔥 Current streak: {current} day{'s' if current != 1 else ''}",
            f"🕐 Longest session today: {compact_duration(longest)}",
            f"📈 Comparison vs yesterday: {sign}{compact_duration(abs(comparison))}",
        ]
        text = "\n".join(lines)
    elif period == "week":
        monday = today - timedelta(days=today.weekday())
        vals = [daily[monday + timedelta(days=i)] for i in range(7)]
        total = sum(vals)
        best = max(vals, default=0)
        best_index = vals.index(best) if vals else 0
        week_subj = defaultdict(int)
        for r in sessions:
            d = day_of(r)
            if d and monday <= d <= monday + timedelta(days=6):
                week_subj[int(r["subject_id"])] += int(r["elapsed_seconds"] or 0)
        top = max(week_subj.items(), key=lambda x: x[1], default=(None, 0))
        u = DB.user(uid)
        week_number = ((today.day - 1) // 7) + 1
        month_label = today.strftime("%b %Y")
        lines = [
            "📊 <b>Weekly Statistics</b>",
            f"👤 {row_mention_html(u)}",
            f"📅 Week {week_number} · {month_label}",
            "━━━━━━━━━━━━━━━━━━━━━━━━",
            "📈 <b>Daily Distribution:</b>",
        ]
        for i, value in enumerate(vals):
            day_name = (monday + timedelta(days=i)).strftime("%a")
            lines.append(f"{day_name} ── {compact_duration(value)}")
        lines += [
            "━━━━━━━━━━━━━━━━━━━━━━━━",
            "⏱️ <b>Summary Metrics:</b>",
            f"• Total time this week: {compact_duration(total)}",
            f"• Daily Average: {compact_duration(total // 7)}",
            f"• Best Day: {compact_duration(best)} ({(monday + timedelta(days=best_index)).strftime('%a')})",
            f"• Top Subject: {safe_html(names.get(top[0], '—'))}",
            "━━━━━━━━━━━━━━━━━━━━━━━━",
        ]
        text = "\n".join(lines)
    elif period == "month":
        start = today.replace(day=1)
        total = sum(v for d, v in daily.items() if start <= d <= today)
        active_days = [d for d, v in daily.items() if start <= d <= today and v > 0]
        top3 = sorted(((v, k) for k, v in by_subject.items()), reverse=True)[:3]
        weeks = []
        for i in range(4):
            a = start + timedelta(days=i * 7)
            b = start + timedelta(days=(i + 1) * 7)
            weeks.append(sum(v for d, v in daily.items() if a <= d < b))
        run = best_streak = 0
        cursor = start
        while cursor <= today:
            if daily[cursor] > 0:
                run += 1; best_streak = max(best_streak, run)
            else:
                run = 0
            cursor += timedelta(days=1)
        productive = max(active_days, key=lambda d: daily[d], default=None)
        lines = [
            "📆 Monthly Statistics", "",
            f"⏱️ Total time this month: {compact_duration(total)}",
            f"📈 Daily average: {compact_duration(total // max(1, (today-start).days + 1))}",
            f"🔥 Best streak this month: {best_streak} days",
            "📚 Top 3 subjects:",
        ]
        lines += [f"• {safe_html(names.get(k, 'Subject'))} — {compact_duration(v)}" for v, k in top3] or ["• No study data yet"]
        lines += [f"📉 Weekly breakdown: " + " | ".join(f"W{i+1}: {compact_duration(v)}" for i, v in enumerate(weeks)), f"🗓️ Most productive day: {productive.strftime('%A') if productive else '—'}", f"🔁 Consistency: {len(active_days)}/{max(1, (today-start).days + 1)} days studied"]
        text = "\n".join(lines)
    else:
        total = sum(daily.values())
        active_days = [d for d, v in daily.items() if v > 0]
        top = max(by_subject.items(), key=lambda x: x[1], default=(None, 0))
        u = DB.user(uid)
        rank = int(DB.fetchone("SELECT COUNT(*)+1 r FROM users WHERE xp>?", (int(u["xp"]),))["r"])
        earned = int(DB.fetchone("SELECT COUNT(*) c FROM user_achievements WHERE user_id=?", (uid,))["c"])
        total_ach = int(DB.fetchone("SELECT COUNT(*) c FROM achievements")["c"])
        member = parse_iso(u["created_at"]).astimezone(DB.timezone(uid)).strftime("%d %b %Y") if parse_iso(u["created_at"]) else "—"
        text = "\n".join([
            "🏆 All-Time Statistics", "",
            f"⏱️ Total lifetime study time: {compact_duration(total)}",
            f"📅 Days active / member since: {len(active_days)} / {member}",
            f"🔥 Longest streak ever: {int(u['best_streak'])} days",
            f"📚 Most studied subject overall: {safe_html(names.get(top[0], '—'))}",
            f"🏅 Achievements unlocked: {earned} / {total_ach}",
            f"🥇 Leaderboard rank: #{rank}",
        ])
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("📅 Daily", callback_data="stats:day"), InlineKeyboardButton("📊 Weekly", callback_data="stats:week")],
        [InlineKeyboardButton("📆 Monthly", callback_data="stats:month"), InlineKeyboardButton("🏆 All-Time", callback_data="stats:all")],
        [InlineKeyboardButton("⬅️ Back", callback_data="home"), InlineKeyboardButton("🏠 Home", callback_data="home")],
    ])
    await send_or_edit(update, context, text, kb)

def _day_bounds_utc(local_day: date, zone: ZoneInfo) -> tuple[datetime, datetime]:
    start_local = datetime.combine(local_day, dt_time.min, tzinfo=zone)
    end_local = start_local + timedelta(days=1)
    return start_local.astimezone(timezone.utc), end_local.astimezone(timezone.utc)


def _overlap_seconds(start: datetime, end: datetime, day: date, zone: ZoneInfo) -> int:
    day_start, day_end = _day_bounds_utc(day, zone)
    left = max(start.astimezone(timezone.utc), day_start)
    right = min(end.astimezone(timezone.utc), day_end)
    return max(0, int((right - left).total_seconds())) if right > left else 0


def _session_daily_seconds(uid: int, session: sqlite3.Row, day: date) -> int:
    zone = DB.timezone(uid)
    now = utc_now()
    segments = DB.session_segments(int(session["id"]))
    if segments:
        return sum(_overlap_seconds(parse_iso(seg["started_at"]), parse_iso(seg["ended_at"]) or now, day, zone) for seg in segments if parse_iso(seg["started_at"]))
    start = DB.session_original_start(session)
    if not start:
        return 0
    end = parse_iso(session["ended_at"]) or now
    return min(_overlap_seconds(start, end, day, zone), max(0, int(session["elapsed_seconds"] or 0)))


def _timeline_entries_for_day(uid: int, session: sqlite3.Row, day: date, active: bool = False) -> list[tuple[datetime, str]]:
    """Return only the real session time that falls inside the user's local day.

    Pauses/resumes are represented as separate timeline entries, and sessions
    crossing midnight are clipped to the current local day.
    """
    zone = DB.timezone(uid)
    now = utc_now()
    entries: list[tuple[datetime, str]] = []
    segments = DB.session_segments(int(session["id"]))
    if segments:
        for seg in segments:
            start = parse_iso(seg["started_at"])
            if not start:
                continue
            end = parse_iso(seg["ended_at"]) or now
            if _overlap_seconds(start, end, day, zone) <= 0:
                continue
            day_start, day_end = _day_bounds_utc(day, zone)
            left = max(start.astimezone(timezone.utc), day_start)
            right = min(end.astimezone(timezone.utc), day_end)
            ls = left.astimezone(zone); le = right.astimezone(zone)
            start_text = ls.strftime('%I:%M %p').lstrip('0')
            end_text = 'Now' if active and not seg["ended_at"] and right >= now.astimezone(timezone.utc) else le.strftime('%I:%M %p').lstrip('0')
            entries.append((ls, f"{start_text}–{end_text} — {safe_html(session['subject_name'])}"))
        return entries

    start = DB.session_original_start(session)
    if not start:
        return []
    end = parse_iso(session["ended_at"]) or now
    if _overlap_seconds(start, end, day, zone) <= 0:
        return []
    day_start, day_end = _day_bounds_utc(day, zone)
    left = max(start.astimezone(timezone.utc), day_start)
    right = min(end.astimezone(timezone.utc), day_end)
    ls = left.astimezone(zone); le = right.astimezone(zone)
    start_text = ls.strftime('%I:%M %p').lstrip('0')
    end_text = 'Now' if active else le.strftime('%I:%M %p').lstrip('0')
    return [(ls, f"{start_text}–{end_text} — {safe_html(session['subject_name'])}")]


async def today_activity_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = await ensure(update)
    if not uid:
        return
    today = DB.local_today(uid); user = DB.user(uid)
    recorded = DB.recorded_sessions(uid); active = DB.active_session(uid)
    total = sum(_session_daily_seconds(uid, r, today) for r in recorded)
    if active: total += _session_daily_seconds(uid, active, today)
    subject_totals: defaultdict[int, int] = defaultdict(int)
    for r in recorded:
        sec = _session_daily_seconds(uid, r, today)
        if sec: subject_totals[int(r["subject_id"])] += sec
    if active:
        sec = _session_daily_seconds(uid, active, today)
        if sec: subject_totals[int(active["subject_id"])] += sec
    timeline=[]
    for r in recorded:
        timeline.extend(_timeline_entries_for_day(uid, r, today))
    if active:
        timeline.extend(_timeline_entries_for_day(uid, active, today, active=True))
    timeline.sort(key=lambda x:x[0])
    done=int(DB.fetchone("SELECT COUNT(*) c FROM study_plans WHERE user_id=? AND plan_date=? AND completed=1",(uid,today.isoformat()))["c"])
    planned=int(DB.fetchone("SELECT COUNT(*) c FROM study_plans WHERE user_id=? AND plan_date=?",(uid,today.isoformat()))["c"])
    lines=[f"📍 Today's Activity - {row_mention_html(user)}",f"📅 {today.strftime('%a, %-d %b %Y')}","───────────────────",f"⏱️ Total studied: {minutes_text(total)} (Till Now)","───────────────────","📚 Subject breakdown"]
    for sec,sid in sorted([(v,k) for k,v in subject_totals.items() if v],reverse=True):
        sub=DB.subject(uid,sid)
        if sub: lines.append(f"• {safe_html(sub['name'])} - {minutes_text(sec)}")
    if len(lines)==6: lines.append("• No study sessions yet")
    lines += ["───────────────────","🕐 Timeline"]
    lines += [x[1] for x in timeline[-20:]] if timeline else ["No sessions yet today."]
    lines += ["───────────────────",f"✅ Plans done: {done}/{planned}"]
    if active: lines.insert(2,"🔴 LIVE — Studying "+safe_html(active["subject_name"]))
    kb=InlineKeyboardMarkup([[InlineKeyboardButton("⏱️ Start Studying",callback_data="study")],[InlineKeyboardButton("⬅️ Back",callback_data="home"),InlineKeyboardButton("🏠 Home",callback_data="home")]])
    await send_or_edit(update,context,"\n".join(lines),kb)


async def subjects_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    rows = DB.subjects(user_id)
    icons = {"Biology":"🧬", "Chemistry":"⚗️", "Mathematics":"➗", "Physics":"🔬"}
    lines=["📚 <b>Subjects</b>", "Select a subject to view its statistics or manage it."]
    for row in rows:
        count=DB.fetchone("SELECT COUNT(*) count FROM study_sessions WHERE user_id=? AND subject_id=? AND status IN ('completed','stopped')",(user_id,row["id"]))["count"]
        icon=icons.get(row["name"],"📘")
        lines.append(f"• {icon} {safe_html(row['name'])} · {count} sessions")
    await send_or_edit(update,context,"\n".join(lines),subject_keyboard(rows,"subject:view",include_add=True))


async def subject_view(update: Update, context: ContextTypes.DEFAULT_TYPE, subject_id: int) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    subject = DB.subject(user_id, subject_id)
    if not subject:
        await send_or_edit(update, context, "That subject no longer exists.", nav_keyboard("subjects"))
        return
    sessions = DB.fetchall(
        "SELECT * FROM study_sessions WHERE user_id=? AND subject_id=? AND status IN ('completed','stopped')",
        (user_id, subject_id),
    )
    total = sum(int(row["elapsed_seconds"] or 0) for row in sessions)
    text = (
        f"📚 <b>{safe_html(subject['name'])}</b>\n\n"
        f"Study time: <b>{minutes_text(total)}</b>\n"
        f"Sessions: <b>{len(sessions)}</b>\n"
        f"Average: <b>{minutes_text(total // len(sessions) if sessions else 0)}</b>"
    )
    rows = [
        [InlineKeyboardButton("✏️ Rename", callback_data=f"subject:rename:{subject_id}")],
        [InlineKeyboardButton("🗑 Delete", callback_data=f"subject:delete:{subject_id}")],
        [InlineKeyboardButton("⬅️ Back", callback_data="subjects"), InlineKeyboardButton("🏠 Home", callback_data="home")],
    ]
    await send_or_edit(update, context, text, InlineKeyboardMarkup(rows))


async def plans_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, day: Optional[str] = None) -> None:
    uid=await ensure(update)
    if not uid:return
    today=DB.local_today(uid); user=DB.user(uid)
    plans=DB.fetchall("SELECT p.*,s.name subject_name FROM study_plans p LEFT JOIN subjects s ON s.id=p.subject_id WHERE p.user_id=? AND p.plan_date=? ORDER BY p.plan_time,p.id",(uid,today.isoformat()))
    upcoming=DB.fetchall("SELECT p.*,s.name subject_name FROM study_plans p LEFT JOIN subjects s ON s.id=p.subject_id WHERE p.user_id=? AND p.plan_date>? ORDER BY p.plan_date,p.plan_time,p.id LIMIT 20",(uid,today.isoformat()))
    done=sum(int(p['completed'] or 0) for p in plans)
    lines=[f"📅 Study Plan • {today.strftime('%a, %-d %b %Y')} • 👤 {row_mention_html(user)}","",f"📊 Completion status: {done} of {len(plans)} tasks done today","","📍 Today's plan:"]
    if plans:
        for p in plans: lines.append(f"{'☑️' if p['completed'] else '⬜'} {safe_html(p['task'])} · {safe_html(p['subject_name'] or 'No subject')} · {compact_duration(int(p['planned_minutes'])*60)}")
    else: lines.append("• No plans scheduled for today.")
    lines += ["","🔜 Upcoming plans:"]
    if upcoming:
        for p in upcoming[:10]: lines.append(f"• {date.fromisoformat(p['plan_date']).strftime('%a, %-d %b')} - {safe_html(p['task'])} - {safe_html(p['subject_name'] or 'No subject')} - {compact_duration(int(p['planned_minutes'])*60)}")
    else: lines.append("• No upcoming plans.")
    buttons=[[InlineKeyboardButton("➕ Add task/plan",callback_data="plan:add")],[InlineKeyboardButton("📍 Today's Plan",callback_data="plans:today"),InlineKeyboardButton("🔜 Upcoming",callback_data="plans:upcoming")],[InlineKeyboardButton("📚 Filter by Subject",callback_data="plans:filter")],[InlineKeyboardButton("📊 Weekly / Monthly View",callback_data="plans:calendar")]]
    for p in plans[:10]: buttons.append([InlineKeyboardButton(("☑️ " if p['completed'] else "⬜ ")+str(p['task'])[:24],callback_data=f"plan:toggle:{p['id']}"),InlineKeyboardButton("✏️",callback_data=f"plan:rename:{p['id']}"),InlineKeyboardButton("🗑",callback_data=f"plan:delete:{p['id']}")])
    buttons.append([InlineKeyboardButton("⬅️ Back",callback_data="home"),InlineKeyboardButton("🏠 Home",callback_data="home")])
    await send_or_edit(update,context,"\n".join(lines),InlineKeyboardMarkup(buttons))

async def timezone_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = await ensure(update)
    if not uid:
        return
    rows = [[InlineKeyboardButton(label, callback_data=f"timezone:{zone}")] for label, zone in TIMEZONE_CHOICES]
    rows.append([InlineKeyboardButton("🌍 Enter IANA timezone", callback_data="timezone:custom")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="settings"), InlineKeyboardButton("🏠 Home", callback_data="home")])
    await send_or_edit(update, context, f"🌍 Timezone\n\nCurrent: {timezone_label(DB.timezone(uid))}\n\nChoose a timezone. Asia/Kolkata (IST) is the default.", InlineKeyboardMarkup(rows))


async def notifications_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = await ensure(update)
    if not uid:
        return
    st = DB.settings(uid)
    labels = {"notify_study":"⏱️ Study session events", "notify_streak":"🔥 Streak risk & milestones", "notify_achievement":"🏆 Achievement unlocks", "notify_plan":"📅 Study plan reminders", "notify_recap":"📊 Weekly/monthly recaps"}
    rows = [[InlineKeyboardButton(("🔔" if st["notifications_enabled"] else "🔕") + f" Notifications {'ON' if st['notifications_enabled'] else 'OFF'}", callback_data="notification:toggle_all")]]
    for col, label in labels.items():
        rows.append([InlineKeyboardButton(("✅ " if st[col] else "🔕 ") + label, callback_data=f"notification:toggle:{col}")])
    rows.append([InlineKeyboardButton("⬅️ Back", callback_data="settings"), InlineKeyboardButton("🏠 Home", callback_data="home")])
    await send_or_edit(update, context, "🔔 Notifications\n\nChoose which group notifications you want to receive.", InlineKeyboardMarkup(rows))


async def settings_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = await ensure(update)
    if not uid:
        return
    zone = DB.timezone(uid)
    st=DB.settings(uid)
    rows = [
        [InlineKeyboardButton(f"🌍 Timezone · {timezone_label(zone)}", callback_data="setting:timezone")],
        [InlineKeyboardButton("🔔 Notifications", callback_data="setting:notifications")],
        [InlineKeyboardButton("♻️ Reset Progress", callback_data="setting:reset")],
        [InlineKeyboardButton("⬅️ Back", callback_data="home"), InlineKeyboardButton("🏠 Home", callback_data="home")],
    ]
    text = "⚙️ Settings\n\nYour timezone defaults to Asia/Kolkata (IST) and can be changed to any valid IANA timezone."
    await send_or_edit(update, context, text, InlineKeyboardMarkup(rows))

async def timer_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = await ensure(update)
    if not uid:
        return
    active = DB.active_session(uid)
    if active:
        seconds = DB.session_seconds(active)
        target = max(1, int(active["target_seconds"] or 0))
        pct = min(100, round(seconds / target * 100))
        zone = DB.timezone(uid)
        started = DB.session_original_start(active) or utc_now()
        u = DB.user(uid)
        bar = progress_bar(seconds, target, 20)
        status = active["status"]
        control = InlineKeyboardButton("⏸ Pause", callback_data="timer:pause") if status == "active" else InlineKeyboardButton("▶️ Resume", callback_data="timer:resume")
        rows = [
            [InlineKeyboardButton("🔄 Refresh", callback_data="timer:refresh"), InlineKeyboardButton("⏹️ Stop Studying", callback_data="timer:stop")],
            [control],
            [InlineKeyboardButton("⬅️ Back", callback_data="home"), InlineKeyboardButton("🏠 Home", callback_data="home")],
        ]
        started_text = format_local_datetime_with_zone(started, zone)
        streak = int(u["current_streak"] or 0)
        streak_text = f"{streak} Day Active" if streak == 1 else f"{streak} Days Active"
        text = (
            "⏱️ Study Session - Live\n"
            "━━━━━━━━━━━━━━━━━\n"
            f"👤 Student : {row_mention_html(u)}\n"
            f"📚 Subject  : {safe_html(active['subject_name'])}\n"
            f"🕒 Started  : {safe_html(started_text)}\n"
            "━━━━━━━━━━━━━━━━━\n"
            "⏳ Time Matrix\n"
            f"├─ Elapsed  : {elapsed_text(seconds)}\n"
            f"├─ Target   : {compact_duration(target)}\n"
            f"└─ Progress :\n [{bar}] {pct}%\n"
            "━━━━━━━━━━━━━━━━━\n"
            "🌱 Session Metrics\n"
            f"├─ Streak   : {streak_text}\n"
            f"└─ Rewards  : +{xp_for_seconds(seconds)} XP (Rate: +1 / 2m)"
        )
        await send_or_edit(update, context, text, InlineKeyboardMarkup(rows))
        live_id = None
        if update.callback_query and update.callback_query.message:
            live_id = update.callback_query.message.message_id
        elif update.effective_message and getattr(update.effective_message, "message_id", None):
            latest = DB.fetchone("SELECT message_id FROM menu_sessions WHERE chat_id=? AND owner_user_id=? AND active=1 ORDER BY message_id DESC LIMIT 1", (update.effective_chat.id, uid))
            live_id = latest["message_id"] if latest else update.effective_message.message_id
        if live_id:
            DB.execute("UPDATE study_sessions SET message_id=? WHERE id=?", (int(live_id), active["id"]))
        return
    await send_or_edit(update, context, "⏱️ Start Studying\n\nChoose a subject:", subject_keyboard(DB.subjects(uid), "timer:subject", include_add=True))


async def start_timer_duration(update: Update, context: ContextTypes.DEFAULT_TYPE, subject_id: int) -> None:
    uid = await ensure(update)
    if not uid:
        return
    subject = DB.subject(uid, subject_id)
    if not subject:
        await send_or_edit(update, context, "Subject not found.", nav_keyboard("study"))
        return
    rows = [
        [InlineKeyboardButton("25m", callback_data=f"timer:preset:{subject_id}:25"), InlineKeyboardButton("30m", callback_data=f"timer:preset:{subject_id}:30"), InlineKeyboardButton("45m", callback_data=f"timer:preset:{subject_id}:45")],
        [InlineKeyboardButton("1h", callback_data=f"timer:preset:{subject_id}:60"), InlineKeyboardButton("1h 30m", callback_data=f"timer:preset:{subject_id}:90"), InlineKeyboardButton("2h", callback_data=f"timer:preset:{subject_id}:120")],
        [InlineKeyboardButton("✍️ Custom Duration", callback_data=f"timer:custom:{subject_id}")],
        [InlineKeyboardButton("⬅️ Back", callback_data="study"), InlineKeyboardButton("🏠 Home", callback_data="home")],
    ]
    await send_or_edit(update, context, f"📚 {safe_html(subject['name'])}\n\nChoose a duration or enter a custom duration.\n\nExamples: 30m · 1h · 1h 30m · 90 minutes", InlineKeyboardMarkup(rows))

async def start_timer(update: Update, context: ContextTypes.DEFAULT_TYPE, subject_id: int, target_seconds: int) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    if DB.active_session(user_id):
        await send_or_edit(update, context, "You already have an active session. Pause or stop it before starting another.", nav_keyboard("study"))
        return
    subject = DB.subject(user_id, subject_id)
    if not subject:
        await send_or_edit(update, context, "That subject no longer exists.", nav_keyboard("study"))
        return
    now = iso_now()
    DB.execute(
        """
        INSERT INTO study_sessions(user_id,chat_id,subject_id,status,started_at,original_started_at,target_seconds,created_at)
        VALUES(?,?,?, 'active', ?, ?, ?, ?)
        """,
        (user_id, update.effective_chat.id if update.effective_chat else None, subject_id, now, now, max(0, target_seconds), now),
    )
    session_id = DB.fetchone("SELECT id FROM study_sessions WHERE user_id=? AND status='active' ORDER BY id DESC LIMIT 1", (user_id,))["id"]
    DB.execute("INSERT INTO study_session_segments(session_id,started_at) VALUES(?,?)", (int(session_id), now))
    context.user_data.pop("awaiting", None)
    await timer_screen(update, context)


async def timer_notifications(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Auto-complete target timers from the unified atomic progression event."""
    try:
        sessions=DB.fetchall("SELECT s.*,sub.name subject_name FROM study_sessions s JOIN subjects sub ON sub.id=s.subject_id WHERE s.status='active' AND s.target_seconds>0")
        for session in sessions:
            elapsed=DB.session_seconds(session); target=int(session["target_seconds"] or 0)
            if elapsed<target: continue
            uid=int(session["user_id"]); result=DB.complete_session_atomic(int(session["id"]),uid,target,stopped=False)
            if not result.get("ok"): continue
            chat=int(session["chat_id"] or 0); user_row=DB.user(uid)
            done_text=(f"⏱️ Study Session Complete!\n\nWell done, {row_mention_html(user_row)}!\n\n📚 Subject: {safe_html(session['subject_name'])}\n⏱️ Duration: {duration_text(target)}\n📅 {local_datetime_text(uid,result['ended_at'],include_zone=True)}\n🔥 Streak: {result['current_streak']} days")
            if chat and session["message_id"]:
                try:
                    await context.bot.edit_message_text(chat_id=chat,message_id=int(session["message_id"]),text=force_bold(done_text),reply_markup=nav_keyboard("home"),parse_mode=ParseMode.HTML)
                    DB.remember_menu(chat,int(session["message_id"]),uid)
                except TelegramError: pass
            await notify_session_events(context,chat,uid,session,target,result["current_streak"],result["new_achievements"],completed=True,include_study=True)
    except Exception:
        LOGGER.exception("Timer notification job failed")


async def pause_timer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    session = DB.active_session(user_id)
    if not session or session["status"] != "active":
        await send_or_edit(update, context, "There is no running timer to pause.", nav_keyboard("study"))
        return
    elapsed = DB.session_seconds(session)
    now = iso_now()
    DB.execute("UPDATE study_sessions SET status='paused',paused_at=?,elapsed_seconds=? WHERE id=? AND status='active'", (now, elapsed, session["id"]))
    closed_seconds = sum(int(r["elapsed_seconds"] or 0) for r in DB.session_segments(int(session["id"])) if r["ended_at"])
    DB.execute("UPDATE study_session_segments SET ended_at=?,elapsed_seconds=? WHERE session_id=? AND ended_at IS NULL", (now, max(0, elapsed - closed_seconds), session["id"]))
    await timer_screen(update, context)


async def resume_timer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    session = DB.active_session(user_id)
    if not session or session["status"] != "paused":
        await send_or_edit(update, context, "There is no paused timer to resume.", nav_keyboard("study"))
        return
    now = iso_now()
    DB.execute("UPDATE study_sessions SET status='active',started_at=?,paused_at=NULL,notification_sent=0 WHERE id=? AND status='paused'", (now, session["id"]))
    DB.execute("INSERT INTO study_session_segments(session_id,started_at) VALUES(?,?)", (int(session["id"]), now))
    await timer_screen(update, context)


async def send_user_notification(context: ContextTypes.DEFAULT_TYPE, source_chat_id: Optional[int], user_id: int, text: str, setting_column: str, *, timed_group: bool=True) -> None:
    settings=DB.settings(user_id)
    if not settings['notifications_enabled'] or not settings[setting_column]: return
    destinations=[]
    if is_group_chat_id(source_chat_id): destinations.append((int(source_chat_id),True))
    u=DB.user(user_id); dm=int(u['dm_chat_id'] or 0) if u else 0
    if dm>0: destinations.append((dm,False))
    for chat_id,is_group in destinations:
        if is_group and DB.group_blocked(chat_id):
            continue
        try:
            sent=await context.bot.send_message(chat_id=chat_id,text=force_bold(text),parse_mode=ParseMode.HTML,disable_web_page_preview=True)
            if is_group and timed_group: DB.remember_menu(chat_id,int(sent.message_id),user_id)
        except TelegramError:
            if is_group: DB.execute("UPDATE bot_chats SET active=0 WHERE chat_id=?",(chat_id,))
            LOGGER.debug("Could not deliver notification",exc_info=True)


async def notify_session_events(context: ContextTypes.DEFAULT_TYPE, chat_id: Optional[int], user_id: int, session: sqlite3.Row, elapsed: int, streak: int, new_achievements: list[sqlite3.Row], *, completed: bool=True, include_study: bool=True) -> None:
    settings=DB.settings(user_id)
    if not settings['notifications_enabled']: return
    user=DB.user(user_id); mention=row_mention_html(user); messages=[]
    if include_study and settings['notify_study']:
        title='⏱️ Study Session Complete' if completed else '⏹️ Study Session Stopped'
        messages.append(('study',f"🔔 {mention}\n\n{title}\n\n📚 Subject: {safe_html(session['subject_name'])}\n⏱️ Duration: {duration_text(elapsed)}\n🔥 Streak: {streak} days\n⭐ XP earned: +{int(session['xp_awarded'] or 0)}",'notify_study'))
    if completed and settings['notify_achievement'] and new_achievements:
        messages.append(('achievement',f"🏆 {mention}\n\nAchievement Unlocked\n"+'\n'.join(f"{a['icon']} {safe_html(a['name'])}" for a in new_achievements),'notify_achievement'))
    if settings['notify_streak'] and streak in {7,14,30,50,100} and DB.claim_notification(user_id,'streak',str(streak)):
        messages.append(('streak',f"🔥 {mention}\n\n{streak}-Day Streak Reached\n\nYour {streak}-day study streak is active.",'notify_streak'))
    for kind,text,setting in messages:
        if kind!='streak' and not DB.claim_notification(user_id,kind,f"{session['id']}:{kind}"): continue
        await send_user_notification(context,chat_id,user_id,text,setting,timed_group=True)


async def finish_timer(update: Update, context: ContextTypes.DEFAULT_TYPE, stopped: bool = False) -> None:
    user_id = await ensure(update)
    if not user_id:
        return
    session = DB.active_session(user_id)
    if not session:
        await send_or_edit(update, context, "There is no active study session.", nav_keyboard("home"))
        return
    elapsed = DB.session_seconds(session)
    target = int(session["target_seconds"] or 0)
    actually_completed = bool(target and elapsed >= target and not stopped)
    result = DB.complete_session_atomic(int(session["id"]), user_id, elapsed, stopped=not actually_completed)
    if not result.get("ok"):
        await send_or_edit(update, context, "That timer was already saved. Your data is safe.", nav_keyboard("home"))
        return
    u = DB.user(user_id)
    if actually_completed:
        text = (
            "⏱️ Study Session Complete!\n\n"
            f"👤 {row_mention_html(u)}\n"
            f"📚 Subject: {safe_html(session['subject_name'])}\n"
            f"⏳ Duration: {elapsed_text(elapsed)}\n"
            f"📅 {local_datetime_text(user_id, result['ended_at'], include_zone=False)}\n"
            f"🔥 Streak: {result['current_streak']} day{'s' if result['current_streak'] != 1 else ''}\n"
            f"⭐ XP earned: +{result['xp']} XP"
        )
    else:
        text = (
            "⏹️ Study Session Stopped\n\n"
            f"👤 {row_mention_html(u)}\n"
            f"📚 Subject: {safe_html(session['subject_name'])}\n"
            f"⏳ Studied: {elapsed_text(elapsed)}\n"
            f"🎯 Target: {compact_duration(target)}\n"
            f"⭐ XP earned: +{result['xp']} XP\n"
            f"🔥 Streak: {result['current_streak']} day{'s' if result['current_streak'] != 1 else ''}"
        )
    live_id = session["message_id"] if "message_id" in session.keys() else None
    if live_id and is_group_chat_id(update.effective_chat.id if update.effective_chat else None):
        try:
            await context.bot.edit_message_text(
                chat_id=int(update.effective_chat.id), message_id=int(live_id),
                text=force_bold(text), reply_markup=nav_keyboard("home"), parse_mode=ParseMode.HTML,
            )
            DB.remember_menu(int(update.effective_chat.id), int(live_id), user_id)
            DB.touch_chat_activity(int(update.effective_chat.id), int(live_id))
        except TelegramError:
            await send_or_edit(update, context, text, nav_keyboard("home"))
    else:
        await send_or_edit(update, context, text, nav_keyboard("home"))
    await notify_session_events(
        context, update.effective_chat.id if update.effective_chat else None, user_id, session,
        elapsed, result["current_streak"], result["new_achievements"],
        completed=actually_completed, include_study=True,
    )

async def save_plan(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Persist a completed Study Plan form after the reminder choice."""
    uid = await ensure(update)
    if not uid:
        return
    a = context.user_data.get("awaiting") or {}
    if a.get("kind") != "plan":
        await answer_callback(update.callback_query, "This plan form expired. Tap Add task/plan again.", show_alert=True)
        return
    d = a.get("data") or {}
    required = ("plan_date", "plan_time", "task", "subject_id", "planned_minutes", "recurrence", "reminder_minutes")
    if any(k not in d for k in required):
        await answer_callback(update.callback_query, "The plan form is incomplete. Please start Add task/plan again.", show_alert=True)
        return
    try:
        DB.execute(
            "INSERT INTO study_plans(user_id,chat_id,plan_date,plan_time,subject_id,task,planned_minutes,created_at,priority,reminder_minutes,recurrence,recurrence_days,completed,carried_over,updated_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (uid, int(update.effective_chat.id), d["plan_date"], d["plan_time"], int(d["subject_id"]), d["task"], int(d["planned_minutes"]), iso_now(), "medium", int(d["reminder_minutes"]), d["recurrence"], "", 0, 0, iso_now()),
        )
    except sqlite3.IntegrityError:
        LOGGER.exception("Could not save study plan")
        await answer_callback(update.callback_query, "Could not save that plan. Your existing data is safe.", show_alert=True)
        return
    context.user_data.pop("awaiting", None)
    if update.callback_query and update.effective_chat:
        cancel_prompt_job(context, int(update.effective_chat.id), uid)
    await answer_callback(update.callback_query, "✅ Plan saved successfully!", show_alert=False)
    await plans_screen(update, context)


async def handle_awaiting(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    msg = update.effective_message
    a = context.user_data.get("awaiting")
    if not msg or not msg.text or not a or not update.effective_chat or update.effective_chat.type not in {"private", "group", "supergroup"}:
        return False
    uid = await ensure(update)
    if not uid:
        return False
    if update.effective_chat.type in {"group", "supergroup"}:
        replied = msg.reply_to_message
        if not replied or not replied.from_user or not replied.from_user.is_bot:
            return False
        if DB.menu_owner(msg.chat_id, replied.message_id) != uid:
            return False
        await remember_message(msg, uid)
    kind = a.get("kind")
    value = msg.text.strip()
    async def reject(text: str) -> bool:
        await msg.reply_text(force_bold(text), parse_mode=ParseMode.HTML)
        return True

    if kind == "owner_user_lookup":
        if not owner_guard(update) or update.effective_chat.type != "private":
            context.user_data.pop("awaiting", None)
            return True
        query = value.strip()
        if not query:
            return await reject("Enter a Telegram ID, @username, or name.")
        if query.startswith("@"):
            query = query[1:]
        rows = []
        if query.isdigit():
            row = DB.user(int(query))
            if row:
                rows = [row]
        if not rows:
            rows = DB.fetchall(
                "SELECT * FROM users WHERE username LIKE ? COLLATE NOCASE OR first_name LIKE ? COLLATE NOCASE ORDER BY updated_at DESC LIMIT 10",
                (f"%{query}%", f"%{query}%"),
            )
        context.user_data.pop("awaiting", None)
        if not rows:
            await send_or_edit(update, context, "🔎 <b>User Lookup</b>\n\nNo matching users found.", owner_back_keyboard())
            return True
        buttons = []
        for row in rows:
            label = (row["first_name"] or row["username"] or str(row["user_id"]))[:30]
            if row["username"]:
                label = f"{label} · @{row['username']}"
            buttons.append([InlineKeyboardButton(label, callback_data=f"owner:user:{int(row['user_id'])}")])
        buttons.append([InlineKeyboardButton("🔎 New Lookup", callback_data="owner:user_lookup")])
        buttons.append([InlineKeyboardButton("⬅️ Owner Dashboard", callback_data="owner:home")])
        await send_or_edit(update, context, f"🔎 <b>User Lookup Results</b>\n\nFound {len(rows)} matching user(s).", InlineKeyboardMarkup(buttons))
        return True

    if kind == "owner_group_lookup":
        query=value.strip()
        rows=[]
        if query.lstrip("-").isdigit():
            row=DB.fetchone("SELECT * FROM bot_chats WHERE chat_id=?", (int(query),))
            if row: rows=[row]
        if not rows:
            rows=DB.fetchall("SELECT * FROM bot_chats WHERE title LIKE ? COLLATE NOCASE OR CAST(chat_id AS TEXT) LIKE ? ORDER BY active DESC,last_seen DESC LIMIT 10", (f"%{query}%",f"%{query}%"))
        context.user_data.pop("awaiting",None)
        if not rows:
            await send_or_edit(update,context,"👥 <b>Group Lookup</b>\n\nNo matching groups found.",owner_back_keyboard()); return True
        buttons=[]
        for row in rows:
            title=(row["title"] or str(row["chat_id"]))[:32]
            buttons.append([InlineKeyboardButton(f"{title} · {int(row['chat_id'])}",callback_data=f"owner:group:{int(row['chat_id'])}")])
        buttons.append([InlineKeyboardButton("⬅️ Owner Dashboard",callback_data="owner:home")])
        await send_or_edit(update,context,"👥 <b>Group Lookup Results</b>",InlineKeyboardMarkup(buttons)); return True

    if kind in {"owner_message_lookup", "owner_reward_lookup", "owner_control_lookup"}:
        query=value.lstrip("@").strip()
        rows=[]
        if query.isdigit():
            row=DB.user(int(query))
            if row: rows=[row]
        if not rows:
            rows=DB.fetchall("SELECT * FROM users WHERE username LIKE ? COLLATE NOCASE OR first_name LIKE ? COLLATE NOCASE ORDER BY updated_at DESC LIMIT 10",(f"%{query}%",f"%{query}%"))
        context.user_data.pop("awaiting",None)
        if not rows: await send_or_edit(update,context,"No matching users found.",owner_back_keyboard()); return True
        buttons=[]
        action={"owner_message_lookup":"message","owner_reward_lookup":"reward_user","owner_control_lookup":"control_user"}[kind]
        for row in rows:
            label=(row["first_name"] or row["username"] or str(row["user_id"]))[:30]
            if row["username"]: label=f"{label} · @{row['username']}"
            buttons.append([InlineKeyboardButton(label,callback_data=f"owner:{action}:{int(row['user_id'])}")])
        buttons.append([InlineKeyboardButton("⬅️ Owner Dashboard",callback_data="owner:home")])
        await send_or_edit(update,context,"Select a user:",InlineKeyboardMarkup(buttons)); return True

    if kind in {"owner_message","owner_broadcast","owner_targeted_message"}:
        if not owner_guard(update) or update.effective_chat.type!="private": context.user_data.pop("awaiting",None); return True
        if not value: return await reject("Message cannot be empty.")
        if len(value)>3500: return await reject("Keep the message under 3500 characters.")
        if kind=="owner_message":
            target=int(a["target_user_id"]); context.user_data["owner_pending_message"]=value; context.user_data["owner_pending_target"]=target
            context.user_data.pop("awaiting",None)
            kb=InlineKeyboardMarkup([[InlineKeyboardButton("✅ Send",callback_data="owner:send_confirm"),InlineKeyboardButton("❌ Cancel",callback_data="owner:home")]])
            await send_or_edit(update,context,f"📨 <b>Message Preview</b>\n\nTo: <code>{target}</code>\n\n{safe_html(value)}",kb); return True
        audience=a.get("audience","users")
        context.user_data["owner_pending_message"]=value; context.user_data["owner_pending_audience"]=audience; context.user_data.pop("awaiting",None)
        cutoff=(utc_now()-timedelta(days=7)).isoformat()
        if audience=="active7": count=int(DB.fetchone("SELECT COUNT(*) c FROM users WHERE owner_blocked=0 AND dm_chat_id IS NOT NULL AND user_id IN (SELECT DISTINCT user_id FROM study_sessions WHERE COALESCE(ended_at,created_at)>=?)",(cutoff,))["c"] or 0)
        elif audience=="inactive7": count=int(DB.fetchone("SELECT COUNT(*) c FROM users WHERE owner_blocked=0 AND dm_chat_id IS NOT NULL AND user_id NOT IN (SELECT DISTINCT user_id FROM study_sessions WHERE COALESCE(ended_at,created_at)>=?)",(cutoff,))["c"] or 0)
        else: count=int(DB.fetchone("SELECT COUNT(*) c FROM users WHERE owner_blocked=0 AND dm_chat_id IS NOT NULL")["c"] or 0)
        label={"active7":"active in 7 days","inactive7":"inactive 7+ days","all":"all reachable users"}.get(audience,"selected users")
        if kind=="owner_broadcast":
            if audience=="groups":
                label="all active, unblocked groups"; count=int(DB.fetchone("SELECT COUNT(*) c FROM bot_chats WHERE active=1 AND owner_blocked=0")["c"] or 0)
            elif audience=="all":
                ucount=int(DB.fetchone("SELECT COUNT(*) c FROM users WHERE owner_blocked=0 AND dm_chat_id IS NOT NULL")["c"] or 0); gcount=int(DB.fetchone("SELECT COUNT(*) c FROM bot_chats WHERE active=1 AND owner_blocked=0")["c"] or 0)
                label=f"all reachable users + groups"; count=ucount+gcount
            else:
                label="all reachable users"; count=int(DB.fetchone("SELECT COUNT(*) c FROM users WHERE owner_blocked=0 AND dm_chat_id IS NOT NULL")["c"] or 0)
            cb="owner:broadcast_confirm"; title="Broadcast Preview"
        else:
            cb="owner:target_send_confirm"; title="Targeted Message Preview"
        await send_or_edit(update,context,f"📣 <b>{title}</b>\n\nAudience: {label}\nRecipients: {count:,}\n\n{safe_html(value)}",InlineKeyboardMarkup([[InlineKeyboardButton("✅ Send",callback_data=cb),InlineKeyboardButton("❌ Cancel",callback_data="owner:home")]])); return True

    if kind=="owner_group_message":
        if not owner_guard(update) or update.effective_chat.type!="private": context.user_data.pop("awaiting",None); return True
        if not value: return await reject("Message cannot be empty.")
        if len(value)>3500: return await reject("Keep the message under 3500 characters.")
        target=int(a["chat_id"]); context.user_data.pop("awaiting",None); context.user_data["owner_pending_group_message"]=(target,value)
        await send_or_edit(update,context,f"📨 <b>Group Message Preview</b>\n\nTo: <code>{target}</code>\n\n{safe_html(value)}",InlineKeyboardMarkup([[InlineKeyboardButton("✅ Send",callback_data="owner:group_send_confirm"),InlineKeyboardButton("❌ Cancel",callback_data="owner:home")]])); return True


    if kind=="owner_reward":
        try: amount=int(value)
        except ValueError: return await reject("Enter a whole XP amount from 1 to 100000.")
        if not 1<=amount<=100000: return await reject("XP must be between 1 and 100000.")
        target=int(a["target_user_id"]); user=DB.user(target)
        if not user: return await reject("User no longer exists.")
        context.user_data.pop("awaiting",None); context.user_data["owner_pending_reward"]=(target,amount)
        await send_or_edit(update,context,f"🎁 <b>Reward Preview</b>\n\nUser: {owner_user_display(user)}\nGrant: +{amount:,} XP",InlineKeyboardMarkup([[InlineKeyboardButton("✅ Grant XP",callback_data="owner:reward_confirm"),InlineKeyboardButton("❌ Cancel",callback_data="owner:home")]])); return True

    if kind=="timer_custom":
        seconds = parse_duration_input(value, max_minutes=720)
        if seconds is None:
            return await reject("Use a duration like 30m, 1h, 1h 30m, or 90 minutes. Range: 1–720 minutes.")
        await start_timer(update, context, int(a["subject_id"]), seconds)
        context.user_data.pop("awaiting", None)
        return True

    if kind in {"subject_add", "subject_rename"}:
        if not 1 <= len(value) <= 40:
            return await reject("Subject names must be 1–40 characters.")
        try:
            if kind == "subject_add":
                DB.execute("INSERT INTO subjects(user_id,name,is_default,created_at) VALUES(?,?,0,?)", (uid, value, iso_now()))
            else:
                DB.execute("UPDATE subjects SET name=? WHERE id=? AND user_id=?", (value, int(a["subject_id"]), uid))
        except sqlite3.IntegrityError:
            return await reject("A subject with that name already exists.")
        context.user_data.pop("awaiting", None)
        await subjects_screen(update, context)
        return True

    if kind == "timezone":
        try:
            ZoneInfo(value)
        except ZoneInfoNotFoundError:
            return await reject("Unknown timezone. Try Asia/Kolkata, Europe/London, or America/New_York.")
        DB.execute("UPDATE users SET timezone=?,updated_at=? WHERE user_id=?", (value, iso_now(), uid))
        context.user_data.pop("awaiting", None)
        await settings_screen(update, context)
        return True

    if kind == "plan_rename":
        pid = int(a["plan_id"])
        if not 1 <= len(value) <= 120:
            return await reject("Plan name must be 1–120 characters.")
        updated = DB.execute("UPDATE study_plans SET task=?,updated_at=? WHERE id=? AND user_id=?", (value, iso_now(), pid, uid))
        if not updated:
            await reject("That plan no longer exists.")
        context.user_data.pop("awaiting", None)
        await plans_screen(update, context)
        return True

    if kind == "plan":
        step = int(a.get("step", 0)); d = a.setdefault("data", {})
        if step == 0:
            lower=value.lower()
            if lower == "today": value=DB.local_today(uid).isoformat()
            elif lower == "tomorrow": value=(DB.local_today(uid)+timedelta(days=1)).isoformat()
            if not valid_date(value): return await reject("Use a date like 2026-09-10, today, or tomorrow.")
            day = date.fromisoformat(value)
            if day < DB.local_today(uid): return await reject("The plan date must be today or a future date.")
            d["plan_date"] = value; a["step"] = 1
            await send_prompt(update, context, a, "🕐 Enter the plan time (e.g. 18:30 or 6:30 PM), or type skip for no fixed time.", nav_keyboard("plans"))
            return True
        if step == 1:
            if value.lower() == "skip": d["plan_time"] = "00:00"; d["reminder_minutes"] = -1
            else:
                t = canonical_time(value)
                if not t: return await reject("Use a time like 18:30 or 6:30 PM.")
                if date.fromisoformat(d["plan_date"]) == DB.local_today(uid) and parse_user_time(t) <= utc_now().astimezone(DB.timezone(uid)).time().replace(second=0,microsecond=0):
                    return await reject("That time has already passed today.")
                d["plan_time"] = t
            a["step"] = 2
            await send_prompt(update, context, a, "📝 What should you study? Reply with the plan/task name.", nav_keyboard("plans"))
            return True
        if step == 2:
            if not 1 <= len(value) <= 120: return await reject("Use 1–120 characters.")
            d["task"] = value; a["step"] = 3
            await send_prompt(update, context, a, "📚 Choose a subject:", subject_keyboard(DB.subjects(uid), "plan:subject", "plans"))
            return True
        if step == 4:
            seconds = parse_duration_input(value, max_minutes=1440) if value.lower() != "skip" else 30 * 60
            if seconds is None: return await reject("Use 30m, 1h, 1h 30m, or another duration up to 24h.")
            d["planned_minutes"] = max(1, seconds // 60); a["step"] = 5
            await send_prompt(update, context, a, "🔁 Choose recurrence:", InlineKeyboardMarkup([[InlineKeyboardButton("🚫 No repeat",callback_data="plan:recurrence:none"),InlineKeyboardButton("📅 Daily",callback_data="plan:recurrence:daily"),InlineKeyboardButton("🗓️ Weekly",callback_data="plan:recurrence:weekly")]]))
            return True
    return False

async def text_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    # Random text is ignored everywhere. Only direct replies to an active bot prompt are parsed.
    await handle_awaiting(update, context)


async def study_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Open the Study Timer subject picker for the current group user."""
    await ensure(update)
    await timer_screen(update, context)


async def command_pause(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await pause_timer(update, context)


async def command_resume(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await resume_timer(update, context)


async def command_stop(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await finish_timer(update, context, stopped=True)


async def command_achievements(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await achievements_screen(update, context)




async def command_profile(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await profile_screen(update, context)


async def command_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await stats_screen(update, context, "week")


async def command_streak(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await streak_screen(update, context)


async def command_plans(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await plans_screen(update, context)


async def command_plan(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid = await ensure(update)
    if not uid:
        return
    await send_prompt(update, context, {"kind":"plan", "step":0, "data":{}}, "📅 Enter the plan date (e.g. 2026-09-10, today or future).", nav_keyboard("plans"))

async def command_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await settings_screen(update, context)






async def command_dashboard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await dashboard_screen(update, context)


async def command_subjects(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await subjects_screen(update, context)


async def command_history(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await history_screen(update, context)


async def command_leaderboard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await leaderboard_menu(update, context)


async def group_add_keyboard(context: ContextTypes.DEFAULT_TYPE) -> InlineKeyboardMarkup:
    """Return Telegram's native group-selection/add flow.

    Telegram bots cannot enumerate every group a human user belongs to. The
    official startgroup deep link therefore opens Telegram's own group picker,
    where the user chooses the group and confirms adding the bot.
    """
    try:
        me = await context.bot.get_me()
        if me.username:
            return InlineKeyboardMarkup([[InlineKeyboardButton("➕ Add me to a group", url=f"https://t.me/{me.username}?startgroup=study_tracker")]])
    except TelegramError:
        LOGGER.exception("Could not resolve bot username for group-add link")
    return InlineKeyboardMarkup([])



def owner_state(key: str, default: str = "") -> str:
    try:
        row = DB.fetchone("SELECT value FROM bot_state WHERE key=?", (key,))
        return str(row["value"]) if row else default
    except Exception:
        return default


def set_owner_state(key: str, value: str) -> None:
    DB.execute("INSERT INTO bot_state(key,value,updated_at) VALUES(?,?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value,updated_at=excluded.updated_at", (key, value, iso_now()))


def owner_audit(owner_id: int, action: str, target_user_id: Optional[int] = None, details: str = "") -> None:
    try:
        DB.execute("INSERT INTO owner_audit_log(owner_id,action,target_user_id,details,created_at) VALUES(?,?,?,?,?)", (owner_id, action, target_user_id, details[:1000], iso_now()))
    except Exception:
        LOGGER.exception("Could not write owner audit log")


def owner_maintenance_enabled() -> bool:
    return owner_state("maintenance_mode", "0") == "1"


async def owner_broadcast_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    kb=InlineKeyboardMarkup([
        [InlineKeyboardButton("👤 All Users", callback_data="owner:broadcast:users"), InlineKeyboardButton("👥 All Groups", callback_data="owner:broadcast:groups")],
        [InlineKeyboardButton("🌐 Users + Groups", callback_data="owner:broadcast:all")],
        [InlineKeyboardButton("👤 Specific User", callback_data="owner:broadcast:user"), InlineKeyboardButton("👥 Specific Group", callback_data="owner:broadcast:group")],
        [InlineKeyboardButton("⬅️ Owner Dashboard", callback_data="owner:home")],
    ])
    await send_or_edit(update, context, "📢 <b>Broadcast & Messaging</b>\n\nChoose who should receive the message.", kb)

async def owner_group_lookup_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    await send_prompt(update, context, {"kind":"owner_group_lookup"}, "👥 <b>Group Lookup</b>\n\nEnter the group chat ID or part of the group name.", owner_back_keyboard())

async def owner_group_control_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    rows=DB.fetchall("SELECT * FROM bot_chats ORDER BY active DESC, last_seen DESC LIMIT 30")
    buttons=[]
    for r in rows:
        title=(r["title"] or str(r["chat_id"]))[:34]
        status="🚫" if int(r["owner_blocked"] or 0) else ("🟢" if int(r["active"] or 0) else "⚪")
        buttons.append([InlineKeyboardButton(f"{status} {title}", callback_data=f"owner:group:{int(r['chat_id'])}")])
    buttons.append([InlineKeyboardButton("🔎 Find Group", callback_data="owner:broadcast:group")])
    buttons.append([InlineKeyboardButton("⬅️ Owner Dashboard", callback_data="owner:home")])
    await send_or_edit(update, context, "👥 <b>Group Control</b>\n\n🟢 Active · ⚪ Unconfirmed/possibly unavailable · 🚫 Blocked", InlineKeyboardMarkup(buttons))

async def owner_group_detail_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, chat_id: int) -> None:
    if not owner_guard(update): return
    row=DB.fetchone("SELECT * FROM bot_chats WHERE chat_id=?", (int(chat_id),))
    if not row:
        await send_or_edit(update,context,"👥 Group not found in the bot registry.",owner_back_keyboard()); return
    blocked=int(row["owner_blocked"] or 0)
    action="unblock_group" if blocked else "block_group"
    label="🔓 Unblock Group" if blocked else "🚫 Block Group"
    text=(f"👥 <b>Group Control</b>\n━━━━━━━━━━━━━━━━━━━━\n"
          f"Name: <b>{safe_html(row['title'] or 'Unknown group')}</b>\n"
          f"Chat ID: <code>{int(chat_id)}</code>\n"
          f"Status: {'🔴 Blocked' if blocked else '🟢 Active'}\n"
          f"Last seen: <code>{safe_html(str(row['last_seen']))}</code>\n\n"
          "Blocking stops normal bot processing in this group. Stored study data is preserved.")
    rows=[[InlineKeyboardButton(label,callback_data=f"owner:{action}:{int(chat_id)}")]]
    if not blocked:
        rows.append([InlineKeyboardButton("📨 Message Group",callback_data=f"owner:group_message:{int(chat_id)}")])
    rows.append([InlineKeyboardButton("⬅️ Group Control",callback_data="owner:groups")])
    kb=InlineKeyboardMarkup(rows)
    await send_or_edit(update,context,text,kb)


async def owner_message_user_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    await send_prompt(update, context, {"kind":"owner_message_lookup"}, "📨 Enter a Telegram user ID, @username, or name to message.", owner_back_keyboard())


async def owner_targeted_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    kb=InlineKeyboardMarkup([
        [InlineKeyboardButton("🔥 Active in 7 days", callback_data="owner:targeted:active7")],
        [InlineKeyboardButton("💤 Inactive 7+ days", callback_data="owner:targeted:inactive7")],
        [InlineKeyboardButton("👥 All reachable users", callback_data="owner:targeted:all")],
        [InlineKeyboardButton("⬅️ Owner Dashboard", callback_data="owner:home")],
    ])
    await send_or_edit(update, context, "📣 <b>Targeted Messaging</b>\n\nChoose the recipient group.", kb)


async def owner_notification_test(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    kb=InlineKeyboardMarkup([
        [InlineKeyboardButton("⏱️ Study", callback_data="owner:testnotif:study"), InlineKeyboardButton("📅 Plan", callback_data="owner:testnotif:plan")],
        [InlineKeyboardButton("🔥 Streak", callback_data="owner:testnotif:streak"), InlineKeyboardButton("🏆 Achievement", callback_data="owner:testnotif:achievement")],
        [InlineKeyboardButton("📊 Recap", callback_data="owner:testnotif:recap"), InlineKeyboardButton("🎯 Goal", callback_data="owner:testnotif:goal")],
        [InlineKeyboardButton("⬅️ Owner Dashboard", callback_data="owner:home")],
    ])
    await send_or_edit(update, context, "🧪 <b>Notification Tester</b>\n\nTests are sent only to your owner account.", kb)


async def owner_diagnostics_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    try:
        integrity = DB.fetchone("PRAGMA integrity_check")[0]
        fk = DB.fetchall("PRAGMA foreign_key_check")
        orphan_subjects = int(DB.fetchone("SELECT COUNT(*) c FROM study_sessions s LEFT JOIN subjects sub ON sub.id=s.subject_id WHERE sub.id IS NULL")["c"] or 0)
        orphan_users = int(DB.fetchone("SELECT COUNT(*) c FROM study_sessions s LEFT JOIN users u ON u.user_id=s.user_id WHERE u.user_id IS NULL")["c"] or 0)
        pending_alerts = int(DB.fetchone("SELECT COUNT(*) c FROM scheduled_alerts WHERE sent_at IS NULL")["c"] or 0)
        active_sessions = int(DB.fetchone("SELECT COUNT(*) c FROM study_sessions WHERE status IN ('active','paused')")["c"] or 0)
        text=("🩺 <b>Advanced Diagnostics</b>\n━━━━━━━━━━━━━━━━━━━━\n"
              f"SQLite integrity: {'🟢 OK' if str(integrity).lower()=='ok' else '🔴 '+safe_html(integrity)}\n"
              f"Foreign-key violations: {len(fk):,}\n"
              f"Orphan sessions → subject: {orphan_subjects:,}\n"
              f"Orphan sessions → user: {orphan_users:,}\n"
              f"Pending scheduled alerts: {pending_alerts:,}\n"
              f"Active/paused sessions: {active_sessions:,}\n"
              f"JobQueue: {'🟢 available' if context.application and context.application.job_queue else '🔴 unavailable'}\n"
              f"Maintenance mode: {'🟠 ON' if owner_maintenance_enabled() else '🟢 OFF'}")
        kb=InlineKeyboardMarkup([[InlineKeyboardButton("🧹 Cleanup Preview",callback_data="owner:cleanup")],[InlineKeyboardButton("⬅️ Owner Dashboard",callback_data="owner:home")]])
        await send_or_edit(update, context, text, kb)
    except Exception as exc:
        await send_or_edit(update, context, f"🩺 <b>Diagnostics</b>\n\n🔴 Error: <code>{safe_html(exc)}</code>", owner_back_keyboard())


async def owner_cleanup_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    cutoff=(utc_now()-timedelta(days=180)).isoformat()
    menu=int(DB.fetchone("SELECT COUNT(*) c FROM menu_sessions WHERE active=0 OR COALESCE(expires_at,'') < ?", (cutoff,))["c"] or 0)
    alerts=int(DB.fetchone("SELECT COUNT(*) c FROM scheduled_alerts WHERE sent_at IS NOT NULL AND sent_at < ?", (cutoff,))["c"] or 0)
    recap=int(DB.fetchone("SELECT COUNT(*) c FROM recap_events WHERE sent_at < ?", (cutoff,))["c"] or 0)
    goals=int(DB.fetchone("SELECT COUNT(*) c FROM goal_notifications WHERE notified_at < ?", (cutoff,))["c"] or 0)
    events=int(DB.fetchone("SELECT COUNT(*) c FROM notification_events WHERE created_at < ?", (cutoff,))["c"] or 0)
    total=menu+alerts+recap+goals+events
    text=("🧹 <b>Safe Database Cleanup</b>\n━━━━━━━━━━━━━━━━━━━━\n"
          "Only old/temporary records are considered; users, sessions, plans, tasks and achievements are never deleted.\n\n"
          f"Menu sessions: {menu:,}\nScheduled alerts: {alerts:,}\nRecap events: {recap:,}\nGoal notifications: {goals:,}\nNotification events: {events:,}\n\nTotal candidates: {total:,}")
    buttons=[]
    if total: buttons.append([InlineKeyboardButton("⚠️ Delete These Records",callback_data="owner:cleanup_confirm")])
    buttons.append([InlineKeyboardButton("⬅️ Diagnostics",callback_data="owner:diagnostics"),InlineKeyboardButton("🏠 Owner Dashboard",callback_data="owner:home")])
    await send_or_edit(update, context, text, InlineKeyboardMarkup(buttons))


async def owner_cleanup_execute(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update): return
    cutoff=(utc_now()-timedelta(days=180)).isoformat()
    counts={}
    for key,sql in {
        "menu_sessions":"DELETE FROM menu_sessions WHERE active=0 OR COALESCE(expires_at,'') < ?",
        "scheduled_alerts":"DELETE FROM scheduled_alerts WHERE sent_at IS NOT NULL AND sent_at < ?",
        "recap_events":"DELETE FROM recap_events WHERE sent_at < ?",
        "goal_notifications":"DELETE FROM goal_notifications WHERE notified_at < ?",
        "notification_events":"DELETE FROM notification_events WHERE created_at < ?",
    }.items():
        cur=DB.execute(sql,(cutoff,)); counts[key]=cur.rowcount if cur.rowcount is not None else 0
    owner_audit(user_id_from_update(update) or 0,"database_cleanup",details=str(counts))
    await owner_cleanup_screen(update, context)


async def owner_reward_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    await send_prompt(update, context, {"kind":"owner_reward_lookup"}, "🎁 Enter the Telegram user ID, @username, or name of the user to reward.", owner_back_keyboard())


async def owner_reset_user_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int) -> None:
    if not owner_guard(update): return
    user=DB.user(user_id)
    if not user:
        await send_or_edit(update,context,"User not found.",owner_back_keyboard()); return
    sessions=int(DB.fetchone("SELECT COUNT(*) c FROM study_sessions WHERE user_id=?",(user_id,))["c"] or 0)
    plans=int(DB.fetchone("SELECT COUNT(*) c FROM study_plans WHERE user_id=?",(user_id,))["c"] or 0)
    tasks=int(DB.fetchone("SELECT COUNT(*) c FROM tasks WHERE user_id=?",(user_id,))["c"] or 0)
    text=(f"⚠️ <b>Reset ALL User Data</b>\n━━━━━━━━━━━━━━━━━━━━\n{owner_user_display(user)}\n\n"
          "This permanently removes this user's study data, sessions, plans, tasks, goals, subjects, achievements, settings, notification history and group membership records.\n\n"
          f"📚 Sessions: {sessions:,}\n📅 Plans: {plans:,}\n📝 Tasks: {tasks:,}\n\n"
          "The Telegram user account record is kept so the bot can recognize them again. The action cannot be undone.")
    kb=InlineKeyboardMarkup([[InlineKeyboardButton("⚠️ YES, RESET EVERYTHING",callback_data=f"owner:reset_confirm:{user_id}")],[InlineKeyboardButton("❌ Cancel",callback_data=f"owner:user:{user_id}")]])
    await send_or_edit(update,context,text,kb)

async def owner_reset_user_execute(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int) -> None:
    """Safely reset one user's application data while preserving their account identity.

    The operation is deliberately defensive: a fresh SQLite safety backup is
    created first, all dependent rows are deleted in foreign-key-safe order,
    and the user's default settings/subjects are recreated in the SAME
    transaction. If any database step fails, SQLite rolls the transaction back
    and the user is not left half-reset.
    """
    if not owner_guard(update):
        return
    if not update.effective_chat or update.effective_chat.type != "private":
        return

    user = DB.user(user_id)
    if not user:
        await send_or_edit(update, context, "User not found.", owner_back_keyboard())
        return

    backup_dir = Path(DB.path).parent / "owner_backups"
    try:
        backup_dir.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        LOGGER.exception("Could not create reset safety-backup directory")
        await send_or_edit(
            update, context,
            f"❌ <b>Reset cancelled</b>\n\nCould not create the safety-backup directory.\n<code>{safe_html(exc)}</code>",
            owner_back_keyboard(),
        )
        return

    target = backup_dir / f"pre_user_reset_{user_id}_{utc_now().strftime('%Y%m%d_%H%M%S_%f')}.sqlite3"

    # Never perform a destructive reset unless the pre-reset backup succeeds.
    source = None
    dest = None
    try:
        source = DB.connect()
        dest = sqlite3.connect(str(target), timeout=30)
        dest.execute("PRAGMA foreign_keys=ON")
        source.backup(dest, pages=100, sleep=0.05)
        dest.commit()
    except Exception as exc:
        LOGGER.exception("Safety backup failed before user reset for user_id=%s", user_id)
        try:
            if target.exists():
                target.unlink()
        except OSError:
            LOGGER.debug("Could not remove incomplete safety backup", exc_info=True)
        await send_or_edit(
            update, context,
            f"❌ <b>Reset cancelled</b>\n\nThe safety backup could not be created, so <b>no user data was deleted</b>.\n\n<code>{safe_html(exc)}</code>",
            owner_back_keyboard(),
        )
        return
    finally:
        if dest is not None:
            try:
                dest.close()
            except Exception:
                pass
        if source is not None:
            try:
                source.close()
            except Exception:
                pass

    reset_now = iso_now()
    try:
        with closing(DB.connect()) as db:
            db.execute("BEGIN IMMEDIATE")

            # Delete dependent records using their ACTUAL schema columns.
            # Important: study_session_segments does NOT have user_id; it is
            # linked through session_id -> study_sessions.id. Deleting it with
            # WHERE user_id=? was the cause of the rollback seen in production.
            db.execute(
                """
                DELETE FROM study_session_segments
                WHERE session_id IN (
                    SELECT id FROM study_sessions WHERE user_id=?
                )
                """,
                (user_id,),
            )

            # study_sessions are now safe to delete because their segment rows
            # have already been removed explicitly.
            db.execute("DELETE FROM study_sessions WHERE user_id=?", (user_id,))

            # All remaining user-owned tables use user_id directly.
            for table in (
                "goal_notifications",
                "notification_events",
                "scheduled_alerts",
                "recap_events",
                "user_achievements",
                "tasks",
                "study_plans",
                "goals",
                "streak_freeze_days",
                "chat_members",
            ):
                db.execute(f"DELETE FROM {table} WHERE user_id=?", (user_id,))

            # menu_sessions uses owner_user_id rather than user_id.
            db.execute("DELETE FROM menu_sessions WHERE owner_user_id=?", (user_id,))

            # Subjects are parents of session/plan/task/goal references.
            db.execute("DELETE FROM subjects WHERE user_id=?", (user_id,))
            db.execute("DELETE FROM settings WHERE user_id=?", (user_id,))

            # Keep the Telegram identity record but reset all application state.
            # dm_chat_id is cleared intentionally so the account starts fresh.
            db.execute(
                """
                UPDATE users
                SET xp=0, level=1, current_streak=0, best_streak=0,
                    streak_freezes=1, last_streak_warning_date=NULL,
                    last_study_local_date=NULL, dm_chat_id=NULL,
                    updated_at=?
                WHERE user_id=?
                """,
                (reset_now, user_id),
            )

            # Recreate a clean default settings row and the four built-in subjects
            # before committing, so the entire reset is atomic.
            db.execute("INSERT INTO settings(user_id) VALUES(?)", (user_id,))
            for name in ("Mathematics", "Physics", "Chemistry", "Biology"):
                db.execute(
                    "INSERT INTO subjects(user_id,name,is_default,created_at) VALUES(?,?,1,?)",
                    (user_id, name, reset_now),
                )

            db.commit()
    except Exception as exc:
        LOGGER.exception("Owner full user reset failed for user_id=%s", user_id)
        await send_or_edit(
            update, context,
            "❌ <b>User reset failed</b>\n\nThe database transaction was rolled back, so the user's data was not intentionally partially reset.\n\n🛡️ The safety backup remains available.",
            owner_back_keyboard(),
        )
        return

    owner_audit(
        user_id_from_update(update) or 0,
        "reset_user_data",
        user_id,
        f"safety_backup={target.name}",
    )

    # Keep the reset safety archive bounded so Railway /data does not grow
    # indefinitely. Keep the five newest user-reset backups.
    safety_backups = sorted(
        backup_dir.glob("pre_user_reset_*.sqlite3"),
        key=lambda x: x.stat().st_mtime,
        reverse=True,
    )
    for old_backup in safety_backups[5:]:
        try:
            old_backup.unlink()
        except OSError:
            LOGGER.debug("Could not remove old reset backup %s", old_backup, exc_info=True)

    fresh_user = DB.user(user_id)
    await send_or_edit(
        update, context,
        f"✅ <b>User data reset complete</b>\n\n{owner_user_display(fresh_user)}\n\n"
        f"🗑️ All application data was reset.\n"
        f"📚 Study history, XP, streaks, achievements, plans, tasks, goals, settings, notifications and group membership were cleared.\n"
        f"🌱 Fresh default subjects/settings were restored.\n\n"
        f"🛡️ Safety backup: <code>{safe_html(target.name)}</code>",
        owner_back_keyboard(),
    )


async def owner_control_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    await send_prompt(update, context, {"kind":"owner_control_lookup"}, "👤 Enter the Telegram user ID, @username, or name to manage.", owner_back_keyboard())


async def owner_control_screen(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int) -> None:
    if not owner_guard(update): return
    user=DB.user(user_id)
    if not user:
        await send_or_edit(update,context,"User not found.",owner_back_keyboard()); return
    blocked=int(user["owner_blocked"] or 0)
    action="unblock" if blocked else "block"
    label="✅ Unblock User" if blocked else "🚫 Block User"
    text=(f"👤 <b>User Control</b>\n━━━━━━━━━━━━━━━━━━━━\n{owner_user_display(user)}\n\n"
          f"Status: {'🔴 Blocked' if blocked else '🟢 Active'}\n\n"
          "Blocking prevents the user from using the bot. Their stored data is not deleted.")
    kb=InlineKeyboardMarkup([[InlineKeyboardButton(label,callback_data=f"owner:{action}:{user_id}")],[InlineKeyboardButton("👤 User Details",callback_data=f"owner:user:{user_id}"),InlineKeyboardButton("⬅️ Owner Dashboard",callback_data="owner:home")]])
    await send_or_edit(update,context,text,kb)


async def owner_maintenance_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    enabled=owner_maintenance_enabled()
    text=("🔧 <b>Maintenance Mode</b>\n━━━━━━━━━━━━━━━━━━━━\n"
          f"Status: {'🟠 ON' if enabled else '🟢 OFF'}\n\n"
          "When ON, normal users receive a maintenance message. Owner access remains available.")
    kb=InlineKeyboardMarkup([[InlineKeyboardButton("🔴 Turn OFF",callback_data="owner:maintenance:off") if enabled else InlineKeyboardButton("🟠 Turn ON",callback_data="owner:maintenance:on")],[InlineKeyboardButton("⬅️ Owner Dashboard",callback_data="owner:home")]])
    await send_or_edit(update,context,text,kb)


async def owner_audit_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not owner_guard(update): return
    rows=DB.fetchall("SELECT owner_id,action,target_user_id,details,created_at FROM owner_audit_log ORDER BY id DESC LIMIT 15")
    lines=["🧾 <b>Owner Audit Log</b>","━━━━━━━━━━━━━━━━━━━━"]
    for r in rows:
        lines.append(f"<code>{safe_html(r['created_at'])}</code> · {safe_html(r['action'])}" + (f" · user {int(r['target_user_id'])}" if r['target_user_id'] else ""))
    if not rows: lines.append("No owner actions recorded yet.")
    await send_or_edit(update,context,"\n".join(lines),owner_back_keyboard())


async def owner_export_user_data(update: Update, context: ContextTypes.DEFAULT_TYPE, user_id: int) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    user=DB.user(user_id)
    if not user:
        await answer_callback(update.callback_query,"User not found.",show_alert=True); return
    rows=DB.fetchall("SELECT id,subject_id,status,started_at,ended_at,elapsed_seconds,xp_awarded,created_at FROM study_sessions WHERE user_id=? ORDER BY id DESC LIMIT 500",(user_id,))
    import json
    payload={"user":dict(user),"sessions":[dict(r) for r in rows],"exported_at":iso_now()}
    path=Path("/tmp")/f"user_{user_id}_export.json"
    path.write_text(json.dumps(payload,ensure_ascii=False,indent=2,default=str),encoding="utf-8")
    owner_audit(user_id_from_update(update) or 0,"user_export",user_id)
    with path.open("rb") as fh:
        await context.bot.send_document(chat_id=int(update.effective_chat.id),document=fh,filename=path.name,caption="📥 User data export (latest 500 sessions)")
    try: path.unlink()
    except OSError: pass


async def owner_send_test_notification(update: Update, context: ContextTypes.DEFAULT_TYPE, kind: str) -> None:
    if not owner_guard(update) or not update.effective_chat or update.effective_chat.type != "private": return
    samples={
        "study":"⏱️ <b>Test Study Notification</b>\nThis is a safe owner-only test.",
        "plan":"📅 <b>Test Plan Reminder</b>\nYour scheduled study plan reminder would appear like this.",
        "streak":"🔥 <b>Test Streak Warning</b>\nThis is a sample streak notification.",
        "achievement":"🏆 <b>Test Achievement</b>\nYou just unlocked a sample achievement.",
        "recap":"📊 <b>Test Recap</b>\nThis is a sample weekly/monthly recap notification.",
        "goal":"🎯 <b>Test Goal Notification</b>\nYour study goal notification would appear like this.",
    }
    await context.bot.send_message(chat_id=int(update.effective_chat.id),text=samples.get(kind,"🧪 Test notification"),parse_mode=ParseMode.HTML)
    owner_audit(user_id_from_update(update) or 0,f"notification_test:{kind}")

async def command_owner(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await owner_screen(update, context)

async def command_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await help_screen(update, context)


async def command_reset(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user_id=await ensure(update)
    if not user_id: return
    await send_or_edit(update,context,"⚠️ <b>Reset statistics?</b>\n\nThis removes recorded study sessions, XP, level, streaks, freezes, and earned achievements. Subjects and study plans are kept.\n\nThis cannot be undone.",InlineKeyboardMarkup([[InlineKeyboardButton("Yes, reset everything",callback_data="setting:confirm_reset")],[InlineKeyboardButton("Cancel",callback_data="settings")]]))


async def plans_calendar_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid=await ensure(update)
    if not uid:return
    kb=InlineKeyboardMarkup([[InlineKeyboardButton("📅 Weekly",callback_data="plans:view:weekly"),InlineKeyboardButton("📆 Monthly",callback_data="plans:view:monthly")],[InlineKeyboardButton("⬅️ Back",callback_data="plans"),InlineKeyboardButton("🏠 Home",callback_data="home")]])
    await send_or_edit(update,context,"📊 Study Plan Views\n\nChoose Weekly or Monthly.",kb)

async def plan_weekly_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid=await ensure(update); user=DB.user(uid); today=DB.local_today(uid); start=today-timedelta(days=today.weekday()); end=start+timedelta(days=6)
    rows=DB.fetchall("SELECT p.*,s.name subject_name FROM study_plans p LEFT JOIN subjects s ON s.id=p.subject_id WHERE p.user_id=? AND p.plan_date BETWEEN ? AND ? ORDER BY p.plan_date,p.id",(uid,start.isoformat(),end.isoformat()))
    by=defaultdict(list)
    for r in rows: by[r['plan_date']].append(r)
    done=sum(int(r['completed'] or 0) for r in rows)
    lines=[f"📅 Study Plan - Weekly - 👤 {row_mention_html(user)}",f"({start.strftime('%-d')} – {end.strftime('%-d %b %Y')})","────────────────────────",f"📊 Completion Status - {done} / {len(rows)} tasks","────────────────────────"]
    for i in range(7):
        d=start+timedelta(days=i); items=by.get(d.isoformat(),[]); marks=''.join('☑️' if int(x['completed'] or 0) else '☐' for x in items) or '—'; comp=sum(int(x['completed'] or 0) for x in items); marker=' ← today' if d==today else ''
        lines.append(f"{d.strftime('%a %-d')} - {marks} - {comp}/{len(items)} Plan(s){marker}")
    counts=Counter((r['subject_name'] or 'No subject') for r in rows); top,count=counts.most_common(1)[0] if counts else ('—',0); active=sum(1 for x in by.values() if x)
    lines += ["────────────────────────",f"📚 Top subject - {safe_html(top)} ({count} tasks)",f"🔥 Active days - {active} / 7","────────────────────────"]
    kb=InlineKeyboardMarkup([[InlineKeyboardButton("📅 Weekly",callback_data="plans:view:weekly"),InlineKeyboardButton("📆 Monthly",callback_data="plans:view:monthly")],[InlineKeyboardButton("⬅️ Back",callback_data="plans"),InlineKeyboardButton("🏠 Home",callback_data="home")]])
    await send_or_edit(update,context,"\n".join(lines),kb)

async def plan_monthly_screen(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    uid=await ensure(update); user=DB.user(uid); today=DB.local_today(uid); first=today.replace(day=1); nextm=(first.replace(day=28)+timedelta(days=4)).replace(day=1); last=nextm-timedelta(days=1)
    rows=DB.fetchall("SELECT p.*,s.name subject_name FROM study_plans p LEFT JOIN subjects s ON s.id=p.subject_id WHERE p.user_id=? AND p.plan_date BETWEEN ? AND ? ORDER BY p.plan_date,p.id",(uid,first.isoformat(),last.isoformat()))
    done=sum(int(r['completed'] or 0) for r in rows)
    # Four calendar blocks, matching the requested 1–7, 8–14, 15–21, 22–end layout.
    ranges=[(1,min(7,last.day)),(8,min(14,last.day)),(15,min(21,last.day)),(22,last.day)]
    lines=[f"📆 Study Plan - Monthly - 👤 {row_mention_html(user)}",f"({first.strftime('%B %Y')})","────────────────────────",f"📊 Completion Status - {done} / {len(rows)} tasks","────────────────────────"]
    best=None
    for wn,(a,b) in enumerate(ranges,1):
        if a>last.day: continue
        items=[r for r in rows if a<=date.fromisoformat(r['plan_date']).day<=b]
        wd=sum(int(r['completed'] or 0) for r in items); total=len(items); pct=round(wd*100/total) if total else None
        marker=' ← this week' if a<=today.day<=b else ''
        lines.append(f"Week {wn} ({a}–{b}) - {wd}/{total} Plan(s) - {str(pct)+'%' if pct is not None else '—'}{marker}")
        if pct is not None and (best is None or pct>best[0]): best=(pct,wn)
    counts=Counter((r['subject_name'] or 'No subject') for r in rows); top,count=counts.most_common(1)[0] if counts else ('—',0); active=len({r['plan_date'] for r in rows}); besttext=f"Week {best[1]} ({best[0]}%)" if best else '—'
    lines += ["────────────────────────",f"📚 Top subject - {safe_html(top)} ({count} tasks)",f"🔥 Best week - {besttext}",f"📈 Active days - {active} / {last.day}","────────────────────────"]
    kb=InlineKeyboardMarkup([[InlineKeyboardButton("📅 Weekly",callback_data="plans:view:weekly"),InlineKeyboardButton("📆 Monthly",callback_data="plans:view:monthly")],[InlineKeyboardButton("⬅️ Back",callback_data="plans"),InlineKeyboardButton("🏠 Home",callback_data="home")]])
    await send_or_edit(update,context,"\n".join(lines),kb)

async def cleanup_group_messages(context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        now=utc_now()
        rows=DB.fetchall('SELECT chat_id,message_id,owner_user_id,created_at,last_activity_at FROM menu_sessions WHERE active=1')
        for r in rows:
            chat=int(r['chat_id']); uid=int(r['owner_user_id'])
            if not is_group_chat_id(chat): continue
            active=DB.active_session(uid); keep_id=int(active['message_id']) if active and active['message_id'] else None
            if keep_id==int(r['message_id']): continue
            last=parse_iso(r['last_activity_at'] or r['created_at']) or now
            age=(now-last).total_seconds()
            if age < 30: continue
            try: await context.bot.delete_message(chat_id=chat,message_id=int(r['message_id']))
            except TelegramError: pass
            DB.deactivate_menu(chat,int(r['message_id']))
    except Exception: LOGGER.exception('Group message cleanup failed')

async def plan_completion_streak(user_id: int, plan: sqlite3.Row) -> None:
    """Count a completed plan as a consistency day without adding study minutes."""
    now = iso_now()
    zone = DB.timezone(user_id)
    today = utc_now().astimezone(zone).date()
    with closing(DB.connect()) as db:
        db.execute("BEGIN IMMEDIATE")
        user = db.execute("SELECT * FROM users WHERE user_id=?", (user_id,)).fetchone()
        if not user:
            db.rollback(); return
        # Recompute active days from recorded study sessions plus completed plan dates.
        days = set()
        for r in db.execute("SELECT ended_at,created_at FROM study_sessions WHERE user_id=? AND status IN ('completed','stopped')", (user_id,)).fetchall():
            parsed = parse_iso(r["ended_at"] or r["created_at"])
            if parsed: days.add(parsed.astimezone(zone).date())
        for r in db.execute("SELECT plan_date FROM study_plans WHERE user_id=? AND completed=1", (user_id,)).fetchall():
            try: days.add(date.fromisoformat(r["plan_date"]))
            except ValueError: pass
        current = 0; cursor = today if today in days else None
        while cursor and cursor in days:
            current += 1; cursor -= timedelta(days=1)
        best = int(user["best_streak"] or 0); run = 0; previous = None
        for d in sorted(days):
            run = run + 1 if previous and d == previous + timedelta(days=1) else 1
            best = max(best, run); previous = d
        db.execute("UPDATE users SET current_streak=?,best_streak=?,last_study_local_date=?,updated_at=? WHERE user_id=?", (current,best,today.isoformat(),now,user_id))
        db.commit()


async def callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query:
        return
    answer_text = None; alert = False
    try:
        chat = update.effective_chat; msg = query.message; user = update.effective_user
        if not chat or chat.type not in {"private", "group", "supergroup"}:
            await answer_callback(query, "This chat type is not supported.", show_alert=True); return
        if not user or not msg:
            return
        uid = await ensure(update)
        if not uid:
            return
        data = query.data or ""
        cancel_welcome_job(context, int(chat.id), int(msg.message_id))

        # Owner dashboard callbacks intentionally bypass normal menu ownership
        # checks because the dashboard is an owner-only system menu. Every
        # owner callback is still checked against OWNER_IDS.
        if data.startswith("owner:"):
            if not is_owner(uid):
                await answer_callback(query, "🔒 Owner access only.", show_alert=True)
                return
            if chat.type != "private":
                await answer_callback(query, "Please use the owner dashboard in private chat.", show_alert=True)
                return
            action=data.split(":",1)[1]
            if action in {"home",""}: await owner_screen(update, context)
            elif action=="health": await owner_health_screen(update, context)
            elif action=="analytics": await owner_analytics_screen(update, context)
            elif action.startswith("analytics:"): await owner_analytics_screen(update, context, action.split(":", 1)[1])
            elif action=="trends": await owner_trends_screen(update, context)
            elif action=="users": await owner_users_screen(update, context)
            elif action=="user_lookup": await owner_user_lookup_prompt(update, context)
            elif action.startswith("user:"):
                try:
                    await owner_user_detail_screen(update, context, int(action.split(":", 1)[1]))
                except (ValueError, TypeError):
                    await answer_callback(query, "Invalid user ID.", show_alert=True)
            elif action.startswith("activity:"):
                try:
                    await owner_user_activity_screen(update, context, int(action.split(":", 1)[1]))
                except (ValueError, TypeError):
                    await answer_callback(query, "Invalid user ID.", show_alert=True)
            elif action=="live": await owner_live_screen(update, context)
            elif action=="errors": await owner_errors_screen(update, context)
            elif action=="backup": await owner_backup(update, context)
            elif action=="broadcast": await owner_broadcast_prompt(update, context)
            elif action.startswith("broadcast:"):
                mode=action.split(":",2)[1]
                if mode=="user": await owner_message_user_prompt(update,context)
                elif mode=="group": await owner_group_lookup_prompt(update,context)
                else:
                    await send_prompt(update,context,{"kind":"owner_broadcast","audience":mode},"📢 Enter the message to broadcast.",owner_back_keyboard())
            elif action=="groups": await owner_group_control_screen(update,context)
            elif action.startswith("group:"): await owner_group_detail_screen(update,context,int(action.split(":",1)[1]))
            elif action.startswith("block_group:") or action.startswith("unblock_group:"):
                target=int(action.split(":",1)[1]); blocked=action.startswith("block_group:")
                DB.execute("UPDATE bot_chats SET owner_blocked=? WHERE chat_id=?",(1 if blocked else 0,target)); owner_audit(uid,"block_group" if blocked else "unblock_group",details=f"chat_id={target}")
                await owner_group_detail_screen(update,context,target)
            elif action.startswith("group_message:"):
                target=int(action.split(":",1)[1]); context.user_data["owner_group_message_target"]=target
                await send_prompt(update,context,{"kind":"owner_group_message","chat_id":target},f"📨 Enter the message for group <code>{target}</code>.",owner_back_keyboard())
            elif action.startswith("reset_user:"): await owner_reset_user_confirm(update,context,int(action.split(":",1)[1]))
            elif action.startswith("reset_confirm:"): await owner_reset_user_execute(update,context,int(action.split(":",1)[1]))
            elif action=="message_user": await owner_message_user_prompt(update, context)
            elif action=="targeted": await owner_targeted_menu(update, context)
            elif action.startswith("targeted:"):
                audience=action.split(":",1)[1]
                context.user_data["owner_target_audience"]=audience
                await send_prompt(update, context, {"kind":"owner_targeted_message","audience":audience}, "📣 Enter the message to send to this audience.", owner_back_keyboard())
            elif action=="notif_test": await owner_notification_test(update, context)
            elif action.startswith("testnotif:"): await owner_send_test_notification(update, context, action.split(":",1)[1])
            elif action=="diagnostics": await owner_diagnostics_screen(update, context)
            elif action=="cleanup": await owner_cleanup_screen(update, context)
            elif action=="cleanup_confirm": await owner_cleanup_execute(update, context)
            elif action=="reward": await owner_reward_prompt(update, context)
            elif action=="control": await owner_control_prompt(update, context)
            elif action.startswith("control_user:"): await owner_control_screen(update, context, int(action.split(":",1)[1]))
            elif action.startswith("block:") or action.startswith("unblock:"):
                target=int(action.split(":",1)[1]); blocked=action.startswith("block:")
                DB.execute("UPDATE users SET owner_blocked=?,updated_at=? WHERE user_id=?",(1 if blocked else 0,iso_now(),target))
                owner_audit(uid,"block_user" if blocked else "unblock_user",target)
                await owner_control_screen(update,context,target)
            elif action=="maintenance": await owner_maintenance_screen(update, context)
            elif action.startswith("maintenance:"):
                on=action.endswith(":on"); set_owner_state("maintenance_mode","1" if on else "0"); owner_audit(uid,"maintenance_on" if on else "maintenance_off")
                await owner_maintenance_screen(update,context)
            elif action=="audit": await owner_audit_screen(update,context)
            elif action.startswith("export:"): await owner_export_user_data(update,context,int(action.split(":",1)[1]))
            elif action.startswith("message:"):
                target=int(action.split(":",1)[1]); context.user_data["owner_message_target"]=target
                await send_prompt(update,context,{"kind":"owner_message","target_user_id":target},f"📨 Enter the message for user <code>{target}</code>.",owner_back_keyboard())
            elif action.startswith("reward_user:"):
                target=int(action.split(":",1)[1]); context.user_data["owner_reward_target"]=target
                await send_prompt(update,context,{"kind":"owner_reward","target_user_id":target},f"🎁 Enter XP to grant to user <code>{target}</code> (1–100000).",owner_back_keyboard())
            elif action=="send_confirm":
                target=int(context.user_data.get("owner_pending_target",0)); message=context.user_data.pop("owner_pending_message","")
                if not target or not message: await answer_callback(query,"Message expired.",show_alert=True)
                else:
                    u=DB.user(target); chat_id=int(u["dm_chat_id"] or 0) if u else 0
                    try:
                        if not chat_id: raise TelegramError("No private chat available")
                        await context.bot.send_message(chat_id=chat_id,text=message)
                        owner_audit(uid,"message_user",target)
                        await send_or_edit(update,context,"✅ Message sent successfully.",owner_back_keyboard())
                    except TelegramError as exc: await send_or_edit(update,context,f"❌ Could not send message: <code>{safe_html(exc)}</code>",owner_back_keyboard())
            elif action=="group_send_confirm":
                pending=context.user_data.pop("owner_pending_group_message",None)
                if not pending: await answer_callback(query,"Message expired.",show_alert=True)
                else:
                    target,message=pending
                    if DB.group_blocked(target):
                        await send_or_edit(update,context,"🚫 This group is blocked. Unblock it before sending bot messages to it.",owner_back_keyboard())
                        return
                    try:
                        await context.bot.send_message(chat_id=int(target),text=message)
                        DB.execute("UPDATE bot_chats SET active=1,last_seen=? WHERE chat_id=?",(iso_now(),target)); owner_audit(uid,"message_group",details=f"chat_id={target}")
                        await send_or_edit(update,context,"✅ Group message sent successfully.",owner_back_keyboard())
                    except TelegramError as exc:
                        DB.execute("UPDATE bot_chats SET active=0 WHERE chat_id=?",(target,))
                        await send_or_edit(update,context,f"❌ Could not send message: <code>{safe_html(exc)}</code>",owner_back_keyboard())
            elif action in {"broadcast_confirm","target_send_confirm"}:
                message=context.user_data.pop("owner_pending_message",""); audience=context.user_data.pop("owner_pending_audience","users")
                sent=failed=0
                if audience in {"users","all"}:
                    users=DB.fetchall("SELECT * FROM users WHERE owner_blocked=0 AND dm_chat_id IS NOT NULL")
                    for u in users:
                        try: await context.bot.send_message(chat_id=int(u["dm_chat_id"]),text=message); sent+=1
                        except TelegramError: failed+=1
                        await asyncio.sleep(0.05)
                if audience in {"groups","all"}:
                    groups=DB.fetchall("SELECT * FROM bot_chats WHERE active=1 AND owner_blocked=0")
                    for g in groups:
                        try:
                            await context.bot.send_message(chat_id=int(g["chat_id"]),text=message); sent+=1
                            DB.execute("UPDATE bot_chats SET active=1,last_seen=? WHERE chat_id=?",(iso_now(),int(g["chat_id"])))
                        except TelegramError:
                            failed+=1; DB.execute("UPDATE bot_chats SET active=0 WHERE chat_id=?",(int(g["chat_id"]),))
                        await asyncio.sleep(0.05)
                owner_audit(uid,"broadcast",details=f"audience={audience};sent={sent};failed={failed}")
                await send_or_edit(update,context,f"📣 <b>Broadcast Complete</b>\n\nAudience: {safe_html(audience)}\n✅ Sent: {sent:,}\n❌ Failed: {failed:,}",owner_back_keyboard())
            elif action=="reward_confirm":
                pending=context.user_data.pop("owner_pending_reward",None)
                if not pending: await answer_callback(query,"Reward expired.",show_alert=True)
                else:
                    target,amount=pending; user=DB.user(target)
                    if not user: await answer_callback(query,"User not found.",show_alert=True)
                    else:
                        new_xp=int(user["xp"] or 0)+int(amount); DB.execute("UPDATE users SET xp=?,level=?,updated_at=? WHERE user_id=?",(new_xp,level_for_xp(new_xp),iso_now(),target)); owner_audit(uid,"grant_xp",target,f"+{amount} XP")
                        await send_or_edit(update,context,f"🎁 <b>Reward Granted</b>\n\n{owner_user_display(user)}\n⭐ +{amount:,} XP\n🏅 New level: {level_for_xp(new_xp)}",owner_back_keyboard())
            else: await answer_callback(query, "Unknown owner action.", show_alert=True)
            await answer_callback(query)
            return

        owner = DB.menu_owner(int(chat.id), int(msg.message_id))
        if owner is None:
            await answer_callback(query, "This menu has expired. Send /start to open your own Study Tracker menu.", show_alert=True); return
        if owner != uid:
            await answer_callback(query, "This menu belongs to another user. Send /start to open your own menu.", show_alert=True); return
        DB.touch_chat_activity(int(chat.id), int(msg.message_id))

        active = DB.active_session(uid)
        allowed_live = data.startswith("timer:") or data == "study"
        if active and not allowed_live:
            await answer_callback(query, "⏱️ Finish the live study session or tap Stop Studying before using another bot feature.", show_alert=True)
            return

        if data == "home":
            context.user_data.pop("awaiting", None); cancel_prompt_job(context, int(chat.id), uid); await render_home(update, context)
        elif data == "study": await timer_screen(update, context)
        elif data == "today": await today_activity_screen(update, context)
        elif data == "dashboard": await dashboard_screen(update, context)
        elif data == "history": await history_screen(update, context)
        elif data.startswith("history:"): await history_screen(update, context, int(data.split(":")[1]))
        elif data == "subjects": await subjects_screen(update, context)
        elif data.startswith("subject:view:"): await subject_view(update, context, int(data.split(":")[2]))
        elif data == "subject:add": await send_prompt(update, context, {"kind":"subject_add"}, "📚 Enter the new subject name (1–40 characters).", nav_keyboard("subjects"))
        elif data.startswith("subject:rename:"):
            sid = int(data.split(":")[2]); await send_prompt(update, context, {"kind":"subject_rename","subject_id":sid}, "✏️ Reply with the new subject name.", nav_keyboard(f"subject:view:{sid}"))
        elif data.startswith("subject:delete:"):
            sid = int(data.split(":")[2]); sub = DB.subject(uid, sid)
            if not sub: await send_or_edit(update, context, "Subject not found.", nav_keyboard("subjects"))
            elif sub["is_default"]: await send_or_edit(update, context, "Default subjects cannot be deleted. Rename them instead.", nav_keyboard(f"subject:view:{sid}"))
            else: await send_or_edit(update, context, "Delete this custom subject?", InlineKeyboardMarkup([[InlineKeyboardButton("🗑 Delete", callback_data=f"subject:confirm_delete:{sid}"), InlineKeyboardButton("Cancel", callback_data=f"subject:view:{sid}")]]))
        elif data.startswith("subject:confirm_delete:"):
            sid = int(data.split(":")[2]); count = int(DB.fetchone("SELECT COUNT(*) c FROM study_sessions WHERE user_id=? AND subject_id=?", (uid, sid))["c"])
            if count: await send_or_edit(update, context, "This subject has study history and cannot be deleted safely. Rename it instead.", nav_keyboard(f"subject:view:{sid}"))
            else: DB.execute("DELETE FROM subjects WHERE id=? AND user_id=?", (sid, uid)); await subjects_screen(update, context)
        elif data.startswith("timer:subject:"): await start_timer_duration(update, context, int(data.split(":")[2]))
        elif data.startswith("timer:preset:"):
            _, _, sid, minutes = data.split(":"); await start_timer(update, context, int(sid), int(minutes) * 60)
        elif data.startswith("timer:custom:"):
            sid = int(data.split(":")[2]); await send_prompt(update, context, {"kind":"timer_custom","subject_id":sid}, "✍️ Custom Duration\n\nReply with 30m, 1h, 1h 30m, or 90 minutes.\nRange: 1 minute to 12 hours.", nav_keyboard("study"))
        elif data == "timer:refresh": await timer_screen(update, context)
        elif data == "timer:pause": await pause_timer(update, context)
        elif data == "timer:resume": await resume_timer(update, context)
        elif data == "timer:stop": await finish_timer(update, context, stopped=True)
        elif data == "plans": await plans_screen(update, context)
        elif data == "plan:add": await send_prompt(update, context, {"kind":"plan","step":0,"data":{}}, "📅 Enter the plan date (e.g. 2026-09-10, today or future).", nav_keyboard("plans"))
        elif data.startswith("plan:subject:"):
            a = context.user_data.get("awaiting")
            if not a or a.get("kind") != "plan": await answer_callback(query, "This plan form expired. Tap Add task/plan again.", show_alert=True); return
            a.setdefault("data", {})["subject_id"] = int(data.split(":")[2]); a["step"] = 4
            await send_prompt(update, context, a, "⏱️ Planned focus duration\n\nExamples: 30m · 1h · 1h 30m · 90 minutes\nMaximum: 24 hours.", nav_keyboard("plans"))

        elif data.startswith("plan:recurrence:"):
            a = context.user_data.get("awaiting")
            if not a or a.get("kind") != "plan": await answer_callback(query, "This plan form expired. Tap Add task/plan again.", show_alert=True); return
            a.setdefault("data", {})["recurrence"] = data.split(":")[2]; a["step"] = 6
            await send_prompt(update, context, a, "⏰ Optional reminder before the plan:", InlineKeyboardMarkup([[InlineKeyboardButton("🔕 None", callback_data="plan:reminder:-1")], [InlineKeyboardButton("5 min", callback_data="plan:reminder:5"), InlineKeyboardButton("10 min", callback_data="plan:reminder:10"), InlineKeyboardButton("30 min", callback_data="plan:reminder:30")]]))
        elif data.startswith("plan:reminder:"):
            a = context.user_data.get("awaiting")
            if not a or a.get("kind") != "plan": await answer_callback(query, "This plan form expired. Tap Add task/plan again.", show_alert=True); return
            if int(a.get("step", -1)) != 6:
                await answer_callback(query, "This reminder menu has expired. Start Add task/plan again.", show_alert=True); return
            a.setdefault("data", {})["reminder_minutes"] = int(data.split(":")[2])
            await save_plan(update, context)
        elif data.startswith("plan:toggle:"):
            pid = int(data.split(":")[2]); p = DB.fetchone("SELECT * FROM study_plans WHERE id=? AND user_id=?", (pid, uid))
            if not p: await answer_callback(query, "That plan no longer exists.", show_alert=True); return
            if p["plan_date"] != DB.local_today(uid).isoformat():
                await answer_callback(query, "Only today's plans can be marked or unmarked.", show_alert=True); return
            new_done = 0 if int(p["completed"] or 0) else 1
            DB.execute("UPDATE study_plans SET completed=?,updated_at=? WHERE id=? AND user_id=?", (new_done, iso_now(), pid, uid))
            if new_done:
                # Completing a plan updates consistency only. Study XP is earned
                # strictly from recorded study time at 1 XP per 2 minutes.
                await plan_completion_streak(uid, p)
                if p["recurrence"] in {"daily", "weekly"}:
                    step = timedelta(days=1 if p["recurrence"] == "daily" else 7)
                    next_day = date.fromisoformat(p["plan_date"]) + step
                    exists = DB.fetchone("SELECT id FROM study_plans WHERE user_id=? AND task=? AND plan_date=? AND recurrence=?", (uid, p["task"], next_day.isoformat(), p["recurrence"]))
                    if not exists:
                        DB.execute("INSERT INTO study_plans(user_id,chat_id,plan_date,plan_time,subject_id,task,planned_minutes,created_at,priority,reminder_minutes,recurrence,recurrence_days,completed,carried_over) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,0,0)", (uid,p["chat_id"],next_day.isoformat(),p["plan_time"],p["subject_id"],p["task"],p["planned_minutes"],iso_now(),p["priority"],p["reminder_minutes"],p["recurrence"],p["recurrence_days"]))
                if DB.claim_notification(uid,"plan_completed",f"{p['id']}:{p['plan_date']}"):
                    sub=DB.fetchone("SELECT name FROM subjects WHERE id=?",(p['subject_id'],))
                    await send_user_notification(context,int(p["chat_id"] or 0),uid,f"✅ {row_mention_html(DB.user(uid))}\n\nStudy Plan Completed\n\n📚 {safe_html(p['task'])}\n📘 Subject: {safe_html(sub['name'] if sub else 'No subject')}\n⏱ Planned duration: {compact_duration(int(p['planned_minutes'])*60)}\n🔥 Consistency streak updated.","notify_plan",timed_group=True)
            await plans_screen(update, context)
        elif data.startswith("plan:rename:"):
            pid = int(data.split(":")[2]); p = DB.fetchone("SELECT id FROM study_plans WHERE id=? AND user_id=?", (pid, uid))
            if not p: await answer_callback(query, "That plan no longer exists.", show_alert=True); return
            await send_prompt(update, context, {"kind":"plan_rename","plan_id":pid}, "✏️ Rename Plan\n\nReply with the new task/plan name.", nav_keyboard("plans"))
        elif data.startswith("plan:delete:"):
            pid = int(data.split(":")[2]); p = DB.fetchone("SELECT task FROM study_plans WHERE id=? AND user_id=?", (pid, uid))
            if not p: await answer_callback(query, "That plan no longer exists.", show_alert=True); return
            await send_or_edit(update, context, f"🗑 Delete '{safe_html(p['task'])}'?", InlineKeyboardMarkup([[InlineKeyboardButton("🗑 Yes, delete", callback_data=f"plan:delete_confirm:{pid}"), InlineKeyboardButton("Cancel", callback_data="plans")]]))
        elif data.startswith("plan:delete_confirm:"):
            pid = int(data.split(":")[2]); DB.execute("DELETE FROM study_plans WHERE id=? AND user_id=?", (pid, uid)); await plans_screen(update, context)
        elif data == "plans:today":
            if not DB.fetchone("SELECT id FROM study_plans WHERE user_id=? AND plan_date=? LIMIT 1", (uid, DB.local_today(uid).isoformat())):
                await answer_callback(query, "📅 No plan found. Please add a task/plan first.", show_alert=True); return
            await plans_screen(update, context, DB.local_today(uid).isoformat())
        elif data == "plans:upcoming":
            if not DB.fetchone("SELECT id FROM study_plans WHERE user_id=? AND plan_date>=? LIMIT 1", (uid, DB.local_today(uid).isoformat())):
                await answer_callback(query, "🔜 No upcoming plan found. Please add a task/plan first.", show_alert=True); return
            await plans_screen(update, context, DB.local_today(uid).isoformat())
        elif data == "plans:filter":
            if not DB.fetchone("SELECT id FROM study_plans WHERE user_id=? LIMIT 1", (uid,)):
                await answer_callback(query, "📚 No plans yet. Please add a task/plan first.", show_alert=True); return
            rows = [[InlineKeyboardButton(s["name"], callback_data=f"plans:filter:{s['id']}")] for s in DB.subjects(uid)]
            rows.append([InlineKeyboardButton("⬅️ Back", callback_data="plans")]); await send_or_edit(update, context, "📚 Filter plans by subject:", InlineKeyboardMarkup(rows))
        elif data.startswith("plans:filter:"):
            sid = int(data.split(":")[-1]); rows = DB.fetchall("SELECT p.*,s.name subject_name FROM study_plans p LEFT JOIN subjects s ON s.id=p.subject_id WHERE p.user_id=? AND p.subject_id=? ORDER BY p.plan_date,p.plan_time", (uid, sid))
            if not rows: await answer_callback(query, "No plans for this subject. Add a task/plan first.", show_alert=True); return
            text = "📚 Subject Plan Filter\n\n" + "\n".join(f"{'☑️' if p['completed'] else '⬜'} {p['plan_date']} · {safe_html(p['task'])} · {compact_duration(int(p['planned_minutes'])*60)}" for p in rows)
            await send_or_edit(update, context, text, nav_keyboard("plans"))
        elif data == "plans:calendar":
            if not DB.fetchone("SELECT id FROM study_plans WHERE user_id=? LIMIT 1", (uid,)):
                await answer_callback(query, "🗓️ No plans yet. Please add a task/plan first.", show_alert=True); return
            await plans_calendar_screen(update, context)
        elif data == "plans:view:weekly": await plan_weekly_screen(update,context)
        elif data == "plans:view:monthly": await plan_monthly_screen(update,context)
        elif data == "stats": await stats_screen(update, context, "week")
        elif data.startswith("stats:"): await stats_screen(update, context, data.split(":", 1)[1])
        elif data == "profile": await profile_screen(update, context)
        elif data == "streak": await streak_screen(update, context)
        elif data == "achievements": await achievements_screen(update, context)
        elif data.startswith("achievements:"):
            try:
                await achievements_screen(update, context, int(data.split(":", 1)[1]))
            except (ValueError, TypeError):
                await answer_callback(query, "Invalid achievement page.", show_alert=True)
        elif data == "xpinfo": await xp_info_screen(update, context)
        elif data == "leaderboard": await leaderboard_menu(update, context)
        elif data.startswith("leaderboard:period:"): await leaderboard_scope_menu(update, context, data.split(":", 2)[2])
        elif data.startswith("leaderboard:"):
            parts = data.split(":")
            if len(parts) == 4: await leaderboard_screen(update, context, parts[1], parts[2], int(parts[3]))
        elif data == "settings": await settings_screen(update, context)
        elif data == "setting:timezone": await timezone_screen(update, context)
        elif data == "setting:notifications": await notifications_screen(update, context)
        elif data == "setting:reset": await send_or_edit(update, context, "⚠️ Reset Progress?\n\nThis removes recorded study sessions, XP, levels, streaks, freezes and achievements. Subjects and study plans are kept. This cannot be undone.", InlineKeyboardMarkup([[InlineKeyboardButton("♻️ Yes, reset", callback_data="setting:confirm_reset"), InlineKeyboardButton("Cancel", callback_data="settings")]]))
        elif data == "setting:confirm_reset": DB.reset_statistics(uid); await send_or_edit(update, context, "Progress reset successfully. Your subjects and study plans were kept.", nav_keyboard("settings"))
        elif data.startswith("timezone:"):
            zone = data.split(":", 1)[1]
            try: ZoneInfo(zone)
            except ZoneInfoNotFoundError: await answer_callback(query, "Unknown timezone.", show_alert=True)
            else: DB.execute("UPDATE users SET timezone=?,updated_at=? WHERE user_id=?", (zone, iso_now(), uid)); context.user_data.pop("awaiting", None); await settings_screen(update, context)
        elif data.startswith("notification:toggle:"):
            col = data.split(":", 2)[2]
            if col in {"notify_study","notify_streak","notify_achievement","notify_plan","notify_recap"}: DB.execute(f"UPDATE settings SET {col}=CASE {col} WHEN 1 THEN 0 ELSE 1 END WHERE user_id=?", (uid,)); await notifications_screen(update, context)
        elif data == "notification:toggle_all":
            st = DB.settings(uid); DB.execute("UPDATE settings SET notifications_enabled=? WHERE user_id=?", (0 if st["notifications_enabled"] else 1, uid)); await notifications_screen(update, context)
        elif data == "help": await help_screen(update, context)
        else: await render_home(update, context)
    except Exception:
        LOGGER.exception("Callback failed")
        answer_text = "Something went wrong. Your saved data is safe."; alert = True
    finally:
        await answer_callback(query, answer_text, show_alert=alert)

async def persist_active_timers(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Persist active elapsed time frequently so a process crash loses only a few seconds."""
    try:
        sessions = DB.fetchall("SELECT id,user_id,started_at,elapsed_seconds,status FROM study_sessions WHERE status='active'")
        for session in sessions:
            started = parse_iso(session["started_at"])
            if not started:
                continue
            now = utc_now()
            elapsed = int(session["elapsed_seconds"] or 0) + max(0, int((now - started).total_seconds()))
            DB.execute("UPDATE study_sessions SET elapsed_seconds=?,started_at=? WHERE id=? AND status='active'", (elapsed, now.isoformat(timespec="seconds"), session["id"]))
    except Exception:
        LOGGER.exception("Active timer persistence job failed")


async def maintain_recurring_and_carryover(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Create future recurring occurrences; never carry incomplete plans into today."""
    try:
        now=utc_now()
        for u in DB.fetchall("SELECT user_id FROM users"):
            uid=int(u["user_id"]); today=now.astimezone(DB.timezone(uid)).date()
            completed_rows=DB.fetchall("SELECT * FROM study_plans WHERE user_id=? AND completed=1 AND recurrence!='none' AND plan_date>=?",(uid,(today-timedelta(days=7)).isoformat()))
            for p in completed_rows:
                recurrence=p["recurrence"]; step=timedelta(days=1 if recurrence=='daily' else 7); next_day=date.fromisoformat(p["plan_date"])+step
                if next_day<today: continue
                exists=DB.fetchone("SELECT id FROM study_plans WHERE user_id=? AND task=? AND plan_date=? AND recurrence=?",(uid,p["task"],next_day.isoformat(),recurrence))
                if not exists:
                    DB.execute("INSERT INTO study_plans(user_id,chat_id,plan_date,plan_time,subject_id,task,planned_minutes,created_at,priority,reminder_minutes,recurrence,recurrence_days,completed,carried_over,updated_at) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,0,0,?)",(uid,p["chat_id"],next_day.isoformat(),p["plan_time"],p["subject_id"],p["task"],p["planned_minutes"],iso_now(),p["priority"],p["reminder_minutes"],recurrence,p["recurrence_days"],iso_now()))
    except Exception:
        LOGGER.exception("Recurring plan maintenance failed")


async def scheduled_plan_alerts(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Deliver plan alerts to the plan's source chat and/or the user's DM.

    Group-created plans: group + user's DM (when the user has opened the bot in DM).
    DM-created plans: DM only. Every alert mentions the plan owner.
    """
    try:
        now=utc_now()
        rows=DB.fetchall("""
            SELECT p.*, s.name AS subject_name, u.dm_chat_id, u.username, u.first_name,
                   st.notifications_enabled, st.notify_plan
            FROM study_plans p
            LEFT JOIN subjects s ON s.id=p.subject_id
            JOIN users u ON u.user_id=p.user_id
            JOIN settings st ON st.user_id=p.user_id
            WHERE st.notifications_enabled=1 AND st.notify_plan=1
        """)
        for p in rows:
            uid=int(p['user_id'])
            local=now.astimezone(DB.timezone(uid)); today=local.date().isoformat()
            if p['plan_date'] != today or not p['plan_time'] or p['plan_time']=='00:00':
                continue
            t=parse_user_time(p['plan_time'])
            if not t: continue
            scheduled=datetime.combine(local.date(),t,tzinfo=DB.timezone(uid))
            reminder_value=int(p['reminder_minutes'] if p['reminder_minutes'] is not None else -1)
            if reminder_value < 0: continue
            trigger=scheduled-timedelta(minutes=reminder_value)
            delta=(local-trigger).total_seconds()
            if delta < -30 or delta > 150: continue
            key=f"{p['id']}:{p['plan_date']}:{p['plan_time']}:{reminder_value}"
            if not DB.claim_notification(uid,'plan',key): continue

            source_chat=int(p['chat_id'] or 0)
            destinations=[]
            if is_group_chat_id(source_chat):
                destinations.append((source_chat, 'group'))
                dm=int(p['dm_chat_id'] or 0)
                if dm > 0: destinations.append((dm, 'dm'))
            else:
                dm=int(p['dm_chat_id'] or source_chat)
                if dm > 0: destinations.append((dm, 'dm'))
            if not destinations:
                continue

            text=(f"🔔 {row_mention_html(p)}\n\n"
                  f"📅 <b>Study Plan Reminder</b>\n\n"
                  f"📚 {safe_html(p['task'])}\n"
                  f"📘 Subject: {safe_html(p['subject_name'] or 'No subject')}\n"
                  f"⏱ Planned focus: {int(p['planned_minutes'])} minutes\n"
                  f"🕐 Starts: {p['plan_time']}\n\n"
                  "🔥 Stay focused and make this block count.")
            sent_group=None; sent_dm=None
            for chat_id, kind in destinations:
                if kind == 'group' and DB.group_blocked(chat_id):
                    continue
                try:
                    sent=await context.bot.send_message(chat_id=chat_id,text=force_bold(text),parse_mode=ParseMode.HTML,disable_web_page_preview=True)
                    if kind=='group': sent_group=sent.message_id
                    else: sent_dm=sent.message_id
                except TelegramError:
                    LOGGER.info("Could not deliver plan reminder for user %s to %s", uid, kind)
            if sent_group is not None or sent_dm is not None:
                expires=(scheduled+timedelta(minutes=int(p['planned_minutes'] or 30))).astimezone(timezone.utc).isoformat()
                DB.execute("""INSERT OR REPLACE INTO scheduled_alerts
                    (user_id,chat_id,plan_id,alert_key,alert_type,scheduled_for,sent_at,created_at,message_id,dm_message_id,expires_at)
                    VALUES(?,?,?,?,?,?,?,?,?,?,?)""",
                    (uid,source_chat,p['id'],key,'plan',scheduled.astimezone(timezone.utc).isoformat(),iso_now(),iso_now(),sent_group,sent_dm,expires))

        # Keep each alert visible until its planned focus window ends.
        for a in DB.fetchall("SELECT * FROM scheduled_alerts WHERE alert_type='plan' AND expires_at IS NOT NULL"):
            exp=parse_iso(a['expires_at'])
            if not exp or now < exp: continue
            for chat_id, message_id in ((a['chat_id'],a['message_id']), (a['chat_id'],a['dm_message_id'])):
                # The first chat_id is the source group; for DM alerts the source is the DM.
                if message_id is None: continue
                target_chat=int(chat_id)
                if a['dm_message_id'] == message_id and not is_group_chat_id(target_chat):
                    target_chat=int(a['chat_id'])
                if a['dm_message_id'] == message_id:
                    # Recover the owner's actual DM chat id.
                    u=DB.fetchone("SELECT dm_chat_id FROM users WHERE user_id=?", (int(a['user_id']),))
                    target_chat=int(u['dm_chat_id']) if u and u['dm_chat_id'] else target_chat
                try: await context.bot.delete_message(chat_id=target_chat,message_id=int(message_id))
                except TelegramError: pass
            DB.execute("DELETE FROM scheduled_alerts WHERE id=?",(a['id'],))
    except Exception: LOGGER.exception('Scheduled plan alert job failed')

async def streak_risk_warnings(context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        now=utc_now()
        for u in DB.fetchall("SELECT u.* FROM users u JOIN settings s ON s.user_id=u.user_id WHERE s.notifications_enabled=1 AND s.notify_streak=1 AND u.current_streak>0"):
            uid=int(u['user_id']); local=now.astimezone(DB.timezone(uid))
            if local.hour<20 or u['last_study_local_date']==local.date().isoformat(): continue
            session=DB.fetchone("SELECT chat_id FROM study_sessions WHERE user_id=? AND chat_id IS NOT NULL ORDER BY id DESC LIMIT 1",(uid,))
            chat=session['chat_id'] if session else None
            if not DB.claim_notification(uid,'streak_warning',local.date().isoformat()): continue
            text=(f"⚠️ {row_mention_html(u)}\n\n🔥 Streak Risk Alert\n\nYou have a {int(u['current_streak'])}-day streak and have not studied today.\n🛡 Freeze available: {int(u['streak_freezes'] or 0)}\n\nStudy before your local day ends to protect your streak.")
            await send_user_notification(context,chat,uid,text,'notify_streak',timed_group=True)
    except Exception: LOGGER.exception('Streak warning job failed')

def _period_key_for_local(local_now: datetime, period: str) -> str:
    if period == "weekly":
        return (local_now.date() - timedelta(days=local_now.weekday())).isoformat()
    return local_now.date().replace(day=1).isoformat()


async def automated_recaps(context: ContextTypes.DEFAULT_TYPE) -> None:
    try:
        now=utc_now()
        for row in DB.fetchall('SELECT user_id FROM users'):
            uid=int(row['user_id']); local=now.astimezone(DB.timezone(uid)); st=DB.settings(uid)
            if not st['notifications_enabled'] or not st['notify_recap']: continue
            period='weekly' if local.weekday()==0 and local.hour==9 else 'monthly' if local.day==1 and local.hour==9 else None
            if not period: continue
            key=_period_key_for_local(local,period)
            if not DB.claim_notification(uid,'recap',f'{period}:{key}'): continue
            chatrow=DB.fetchone('SELECT chat_id FROM study_sessions WHERE user_id=? AND chat_id IS NOT NULL ORDER BY id DESC LIMIT 1',(uid,)); chat=chatrow['chat_id'] if chatrow else None
            if period=='weekly': start=local.date()-timedelta(days=7); end=local.date()
            else:
                end=local.date().replace(day=1)-timedelta(days=1); start=end.replace(day=1)
            items=[r for r in DB.recorded_sessions(uid) if (DB.local_date_for(uid,r['ended_at'] or r['created_at']) or date.min)>=start and (DB.local_date_for(uid,r['ended_at'] or r['created_at']) or date.max)<=end]
            secs=sum(int(r['elapsed_seconds'] or 0) for r in items); xp=sum(int(r['xp_awarded'] or 0) for r in items); u=DB.user(uid)
            text=(f"📊 {row_mention_html(u)}\n\n{period.title()} Study Recap\n\n⏱️ Study time: {minutes_text(secs)}\n✅ Completed sessions: {sum(1 for r in items if r['status']=='completed')}\n⭐ XP earned: +{xp}\n🏅 Level: {int(u['level'])}\n🔥 Streak: {int(u['current_streak'])} days")
            await send_user_notification(context,chat,uid,text,'notify_recap',timed_group=True)
    except Exception: LOGGER.exception('Automated recap job failed')

async def group_membership_update(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat=update.effective_chat
    if not chat or chat.type not in {"group","supergroup"}: return
    member=update.my_chat_member
    if not member: return
    DB.register_bot_chat(chat)
    new_status=str(member.new_chat_member.status)
    if new_status in {"left","kicked"}:
        DB.execute("UPDATE bot_chats SET active=0,last_seen=? WHERE chat_id=?",(iso_now(),int(chat.id)))
    elif new_status in {"member","administrator"}:
        DB.execute("UPDATE bot_chats SET active=1,last_seen=? WHERE chat_id=?",(iso_now(),int(chat.id)))


def protected_handler(handler: Callable[[Update, ContextTypes.DEFAULT_TYPE], Awaitable[Any]]):
    @wraps(handler)
    async def wrapped(update: Update, context: ContextTypes.DEFAULT_TYPE) -> Any:
        try:
            # IMPORTANT: menu_sessions.owner_user_id has a foreign key to users.
            # On a user's very first group message (especially /start), the old
            # order tried to insert the message into menu_sessions BEFORE the
            # user existed in users, which raised SQLITE_CONSTRAINT_FOREIGNKEY
            # and produced the generic Telegram error shown to the user.
            # Register the user first, then track the message. This also covers
            # callback queries from group members who have never used the bot.
            if isinstance(update, Update) and update.effective_chat and update.effective_chat.type == "private":
                user = update.effective_user
                if user:
                    DB.ensure_user(user)
                    DB.execute("UPDATE users SET dm_chat_id=?, updated_at=? WHERE user_id=?", (int(update.effective_chat.id), iso_now(), int(user.id)))
                    if not is_owner(int(user.id)):
                        db_user = DB.user(int(user.id))
                        if db_user and int(db_user["owner_blocked"] or 0):
                            if update.effective_message:
                                await update.effective_message.reply_text("🔒 Your bot access is currently restricted by the administrator.")
                            return None
                        if owner_maintenance_enabled():
                            if update.effective_message:
                                await update.effective_message.reply_text("🔧 The bot is temporarily in maintenance mode. Please try again later.")
                            return None
            if isinstance(update, Update) and is_group_update(update):
                user = update.effective_user
                chat = update.effective_chat
                if user and chat:
                    DB.ensure_user(user)
                    DB.register_bot_chat(chat)
                    if not is_owner(int(user.id)) and DB.group_blocked(int(chat.id)):
                        return None
                    db_user = DB.user(int(user.id))
                    if not is_owner(int(user.id)) and db_user and int(db_user["owner_blocked"] or 0):
                        if update.effective_message:
                            await update.effective_message.reply_text("🔒 Your bot access is currently restricted by the administrator.")
                        return None
                    if not is_owner(int(user.id)) and owner_maintenance_enabled():
                        if update.effective_message:
                            await update.effective_message.reply_text("🔧 The bot is temporarily in maintenance mode. Please try again later.")
                        return None
                    DB.register_chat_member(int(chat.id), int(user.id))
                    # While a user has a live timer, all unrelated bot commands
                    # are blocked so the live screen remains the single source
                    # of truth. Timer controls remain available.
                    active = DB.active_session(int(user.id))
                    # Callback and text handlers perform their own routing. In
                    # particular, timer:stop must reach the callback handler;
                    # ordinary random text must never trigger a bot message.
                    allowed = {"start_command", "study_command", "command_pause", "command_resume", "command_stop", "callback", "text_message"}
                    if active and handler.__name__ not in allowed:
                        if update.effective_message:
                            await update.effective_message.reply_text(
                                force_bold("⏱️ Your study session is still live. First complete the live study session or tap Stop Studying, then use the bot again."),
                                parse_mode=ParseMode.HTML,
                            )
                        return None
            return await handler(update, context)
        except Exception:
            LOGGER.exception('Unhandled exception in handler %s', handler.__name__)
            try:
                if isinstance(update, Update) and update.callback_query:
                    await answer_callback(
                        update.callback_query,
                        'Something went wrong. Please try again.',
                        show_alert=True,
                    )
                elif (
                    isinstance(update, Update)
                    and is_group_update(update)
                    and update.effective_message
                ):
                    await update.effective_message.reply_text(
                        force_bold(
                            'Something went wrong, but the bot is still running. Please try again.'
                        ),
                        parse_mode=ParseMode.HTML,
                    )
            except Exception:
                LOGGER.debug('Could not send protected-handler error response', exc_info=True)
        return None
    return wrapped

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    error = context.error
    if isinstance(error, TelegramError):
        LOGGER.error("Telegram error: %s", error)
    else:
        LOGGER.error("Unhandled application error: %s\n%s", error, traceback.format_exc())
    if isinstance(update, Update):
        try:
            if update.callback_query:
                await answer_callback(
                    update.callback_query,
                    "Something went wrong. Please try again.",
                    show_alert=True,
                )
            elif isinstance(update, Update) and update.effective_message:
                await update.effective_message.reply_text(
                    force_bold("Something went wrong, but the bot is still running. Please try that action again."),
                    parse_mode=ParseMode.HTML,
                )
        except TelegramError:
            LOGGER.debug("Could not send error response", exc_info=True)


def build_application() -> Application:
    global BOT_STARTED_AT
    BOT_STARTED_AT = utc_now()
    if not BOT_TOKEN or BOT_TOKEN == "PUT_BOT_TOKEN_HERE":
        raise RuntimeError("BOT_TOKEN is not configured. Set BOT_TOKEN in the environment before starting the bot.")
    application = ApplicationBuilder().token(BOT_TOKEN).build()
    chat_filter = filters.ChatType.PRIVATE | filters.ChatType.GROUPS
    application.add_handler(ChatMemberHandler(group_membership_update, ChatMemberHandler.MY_CHAT_MEMBER))
    application.add_handler(CommandHandler("start", protected_handler(start_command), filters=chat_filter))
    application.add_handler(CommandHandler("owner", protected_handler(command_owner), filters=chat_filter))
    commands = [
        ("help", command_help), ("study", study_command), ("pause", command_pause), ("resume", command_resume), ("stop", command_stop),
        ("profile", command_profile), ("stats", command_stats), ("streak", command_streak), ("plans", command_plans), ("plan", command_plan),
        ("settings", command_settings), ("dashboard", command_dashboard), ("subjects", command_subjects), ("history", command_history),
        ("leaderboard", command_leaderboard), ("achievements", command_achievements), ("reset", command_reset),
    ]
    for cmd, handler in commands:
        application.add_handler(CommandHandler(cmd, protected_handler(handler), filters=chat_filter))
    application.add_handler(CallbackQueryHandler(protected_handler(callback), pattern=r".*"))
    application.add_handler(MessageHandler(chat_filter & filters.TEXT & ~filters.COMMAND, protected_handler(text_message)))
    application.add_error_handler(error_handler)
    if not application.job_queue:
        raise RuntimeError("APScheduler/JobQueue is unavailable. Install python-telegram-bot[job-queue].")
    application.job_queue.run_repeating(timer_notifications, interval=10, first=5, name="study-timer-notifications")
    application.job_queue.run_repeating(persist_active_timers, interval=10, first=10, name="persist-active-timers")
    application.job_queue.run_repeating(scheduled_plan_alerts, interval=30, first=15, name="scheduled-plan-alerts")
    application.job_queue.run_repeating(maintain_recurring_and_carryover, interval=300, first=30, name="plan-maintenance")
    application.job_queue.run_repeating(streak_risk_warnings, interval=300, first=60, name="streak-risk-warnings")
    application.job_queue.run_repeating(automated_recaps, interval=60, first=90, name="automated-recaps")
    application.job_queue.run_repeating(cleanup_group_messages, interval=10, first=10, name="cleanup-group-messages")
    DB.recover_active_sessions()
    return application

def main() -> None:
    application = build_application()
    LOGGER.info("Starting Study Tracker Bot with database %s", DB_PATH)
    application.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=False)


if __name__ == "__main__":
    main()