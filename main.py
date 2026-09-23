import random
import copy
import os
import hashlib
import hmac
import json
import secrets
import sqlite3
import time
from datetime import datetime, timedelta, timezone
from collections import deque
from pathlib import Path
from typing import Optional

from fastapi import FastAPI, HTTPException, Request, Response
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, JSONResponse, PlainTextResponse
from pydantic import BaseModel, Field

BASE_DIR = Path(__file__).resolve().parent
DB_PATH = BASE_DIR / "cyber_dungeon.sqlite3"
DB_BACKUP_DIR = BASE_DIR / "backups"
MAX_DB_BACKUPS = 30
ACCOUNT_LOG_PATH = BASE_DIR / "account_log.txt"
USER_LOG_PATH = BASE_DIR / "user_logs.txt"
SESSION_COOKIE = "cyber_dungeon_session"
SESSION_DAYS = 30
STATE_SAVE_INTERVAL = 2.0
ADMIN_LOG_KEY_ENV = "CYBER_DUNGEON_ADMIN_KEY"

GRID_SIZE = 48
TILE = 0
WALL = 1
STAIRS = 2
SECRET_DOOR = 3
VENT = 4
TERMINAL = 5
LASER_CAGE = 6
EXIT_AIRLOCK = 7
SECRET_MAP_COUNT = 5

MAP_TILE_LABELS = {
    TILE: ".",
    WALL: "#",
    VENT: "V",
    TERMINAL: "T",
    LASER_CAGE: "C",
    EXIT_AIRLOCK: ">",
}

FOG_UNEXPLORED = 0
FOG_VISIBLE = 1
FOG_FOGGY = 2

EXP_TO_LEVEL = 100
ENEMY_COUNT = 8
MAX_ENEMY_COUNT = 20
CHEST_COUNT = 3
BASE_ATTACK = 15
ENEMY_KILL_GOLD = 15
ENEMY_KILL_EXP = 20
CHEST_GOLD = 50
CHEST_EXP = 20
BASE_MP = 50
MP_REGEN_SAFE = 2
FIREBALL_COST = 20
FIREBALL_DAMAGE = 30
FIREBALL_RANGE = 3
INVISIBILITY_DURATION = 15
QUEST_REWARD = 100
ITEM_DROP_CHANCE = 0.40
MAX_FLOOR = 100
BOSS_FLOOR = 100
BOSS_AOE_INTERVAL = 3

LEVEL_UP_CHOICES = {
    "power": {"name": "Guc", "description": "+5 Saldiri"},
    "vitality": {"name": "Dayaniklilik", "description": "+30 Maksimum HP"},
    "focus": {"name": "Odak", "description": "+15 Maksimum MP"},
}

QUEST_TEMPLATES = [
    {"type": "kill_enemies", "name": "Goblin Avla", "target": 3},
    {"type": "kill_enemies", "name": "Zindanı Temizle", "target": 5},
    {"type": "kill_enemies", "name": "Avcı Protokolü", "target": 8},
    {"type": "collect_gold", "name": "Altın Topla", "target": 50},
    {"type": "collect_gold", "name": "Hazine Kasasını Doldur", "target": 100},
    {"type": "collect_gold", "name": "Zenginlik Operasyonu", "target": 150},
    {"type": "open_chests", "name": "Sandık Avcısı", "target": 1},
    {"type": "open_chests", "name": "Kayıp Hazineler", "target": 2},
    {"type": "reach_floor", "name": "Derinliklere İn", "target": 3},
    {"type": "reach_floor", "name": "Son Seviyeye Yaklaş", "target": 5},
]

SHOP_ITEMS = {
    "potion":        {"cost": 20,  "label": "Can İksiri"},
    "sword_upgrade": {"cost": 100, "label": "Kılıç Geliştirmesi"},
    "bless_sword":   {"cost": 500, "label": "Bless Kılıç"},
    "armor_upgrade": {"cost": 150, "label": "Zırh Geliştirmesi"},
    "mana_potion":   {"cost": 30,  "label": "Mana İksiri"},
    "invisibility_potion": {"cost": 400, "label": "Görünmezlik İksiri"},
}

DIR_DELTA = {
    "up":    (0, -1),
    "down":  (0,  1),
    "left":  (-1, 0),
    "right": (1,  0),
}

CLASS_STATS = {
    "Warrior": {"hp": 150, "max_hp": 150, "mp": 20,  "max_mp": 20,  "attack_power": 12, "gold": 10},
    "Mage":    {"hp": 80,  "max_hp": 80,  "mp": 100, "max_mp": 100, "attack_power": 20, "gold": 10},
    "Rogue":   {"hp": 105, "max_hp": 105, "mp": 40,  "max_mp": 40,  "attack_power": 15, "gold": 50},
}

ITEM_POOL = {
    "weapon": [
        {"id": "iron_sword",    "name": "Demir Kılıç",      "slot": "weapon",    "atk": 5,  "def": 0,  "rarity": "common"},
        {"id": "steel_blade",   "name": "Çelik Bıçak",      "slot": "weapon",    "atk": 10, "def": 0,  "rarity": "uncommon"},
        {"id": "cyber_katana",  "name": "Siber Katana",     "slot": "weapon",    "atk": 18, "def": 0,  "rarity": "rare"},
        {"id": "plasma_sword",  "name": "Plazma Kılıcı",    "slot": "weapon",    "atk": 28, "def": 0,  "rarity": "legendary"},
    ],
    "armor": [
        {"id": "leather_vest",  "name": "Deri Yelek",       "slot": "armor",     "atk": 0,  "def": 3,  "rarity": "common"},
        {"id": "chain_mail",    "name": "Zincir Zırh",      "slot": "armor",     "atk": 0,  "def": 6,  "rarity": "uncommon"},
        {"id": "crystal_plate", "name": "Kristal Plaka",    "slot": "armor",     "atk": 0,  "def": 12, "rarity": "rare"},
        {"id": "neon_barrier",  "name": "Neon Bariyer",     "slot": "armor",     "atk": 0,  "def": 20, "rarity": "legendary"},
    ],
    "accessory": [
        {"id": "swift_ring",    "name": "Hız Yüzüğü",       "slot": "accessory", "atk": 3,  "def": 1,  "rarity": "common"},
        {"id": "power_amulet",  "name": "Güç Muskası",      "slot": "accessory", "atk": 8,  "def": 3,  "rarity": "uncommon"},
        {"id": "shadow_band",   "name": "Gölge Bant",       "slot": "accessory", "atk": 14, "def": 6,  "rarity": "rare"},
    ],
}

RARITY_DROP_WEIGHTS = {"common": 55, "uncommon": 30, "rare": 12, "legendary": 3}

ENEMY_TYPES = {
    "Goblin": {
        "hp": 30, "damage": 10, "exp": 20, "gold": 15,
        "move_speed": 1, "range": 1, "color": "#ff2244",
    },
    "Skeleton Archer": {
        "hp": 22, "damage": 8, "exp": 25, "gold": 18,
        "move_speed": 1, "range": 3, "color": "#ccaa44",
    },
    "Orc Bruiser": {
        "hp": 80, "damage": 18, "exp": 45, "gold": 35,
        "move_speed": 2, "range": 1, "color": "#44bb44",
    },
    "Poison Zombie": {
        "hp": 45, "damage": 3, "exp": 25, "gold": 20,
        "move_speed": 1, "range": 4, "color": "#00ff55",
    },
}

CYBER_DRAGON = {
    "id": 9999,
    "name": "Cyber-Dragon",
    "hp": 2000,
    "max_hp": 2000,
    "damage": 40,
    "defense": 15,
    "exp": 5000,
    "gold": 1000,
    "move_speed": 1,
    "range": 1,
    "color": "#ff6600",
    "is_boss": True,
    "aoe_timer": 0,
    "x": 0,
    "y": 0,
    "move_timer": 0,
}

app = FastAPI(title="Grid Dungeon Crawler v2")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

ACHIEVEMENTS = {
    "first_blood": {"name": "Ilk Kan", "description": "Ilk dusmani yen", "icon": "ATK"},
    "level_5": {"name": "Usta Savasci", "description": "5. seviyeye ulas", "icon": "LVL"},
    "floor_10": {"name": "Derinliklere", "description": "10. kata ulas", "icon": "MAP"},
    "gold_1000": {"name": "Hazine Avcisi", "description": "Toplam 1000 altin kazan", "icon": "GOLD"},
    "boss_slayer": {"name": "Üstün Başarı: Ejderha Avcısı", "description": "Cyber-Dragon'u yen", "icon": "BOSS"},
}


def append_user_log(action: str, username: str, request: Request) -> None:
    """Kullanıcının kayıt ve giriş işlemlerini IP ve Türkiye saatiyle txt'ye kaydeder."""
    tr_tz = timezone(timedelta(hours=3))
    now_str = datetime.now(tr_tz).strftime("%d.%m.%Y %H:%M:%S")
    
    # Render reverse-proxy arkasında çalıştığı için gerçek istemci IP'si X-Forwarded-For başlığındadır
    forwarded = request.headers.get("x-forwarded-for")
    if forwarded:
        client_ip = forwarded.split(",")[0].strip()
    elif request.client and request.client.host:
        client_ip = request.client.host
    else:
        client_ip = "Bilinmiyor"

    line = f"[{now_str}] | Islem: {action.upper()} | Kullanici: {username} | IP: {client_ip}\n"
    try:
        with USER_LOG_PATH.open("a", encoding="utf-8") as f:
            f.write(line)
    except OSError:
        pass


def db_connect() -> sqlite3.Connection:
    connection = sqlite3.connect(DB_PATH)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute("PRAGMA journal_mode = WAL")
    connection.execute("PRAGMA synchronous = FULL")
    return connection


def init_database() -> None:
    with db_connect() as connection:
        connection.executescript("""
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT NOT NULL UNIQUE COLLATE NOCASE,
                password_hash TEXT NOT NULL,
                created_at TEXT NOT NULL,
                last_login_at TEXT,
                failed_login_attempts INTEGER NOT NULL DEFAULT 0,
                is_active INTEGER NOT NULL DEFAULT 1
            );
            CREATE TABLE IF NOT EXISTS sessions (
                token TEXT PRIMARY KEY,
                user_id INTEGER NOT NULL,
                expires_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
            );
            CREATE TABLE IF NOT EXISTS profiles (
                user_id INTEGER PRIMARY KEY,
                state_json TEXT NOT NULL,
                achievements_json TEXT NOT NULL DEFAULT '[]',
                FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE CASCADE
            );
            CREATE TABLE IF NOT EXISTS auth_events (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                username TEXT NOT NULL,
                event_type TEXT NOT NULL,
                created_at TEXT NOT NULL,
                FOREIGN KEY(user_id) REFERENCES users(id) ON DELETE SET NULL
            );
            CREATE TABLE IF NOT EXISTS gravestones (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT NOT NULL,
                floor INTEGER NOT NULL,
                x INTEGER NOT NULL,
                y INTEGER NOT NULL,
                cause TEXT NOT NULL,
                gold INTEGER NOT NULL DEFAULT 0,
                is_looted INTEGER NOT NULL DEFAULT 0,
                created_at TEXT NOT NULL
            );
            CREATE TRIGGER IF NOT EXISTS prevent_user_delete
            BEFORE DELETE ON users
            BEGIN
                SELECT RAISE(ABORT, 'User accounts are permanent');
            END;
        """)
        user_columns = {row["name"] for row in connection.execute("PRAGMA table_info(users)")}
        migrations = {
            "last_login_at": "ALTER TABLE users ADD COLUMN last_login_at TEXT",
            "failed_login_attempts": "ALTER TABLE users ADD COLUMN failed_login_attempts INTEGER NOT NULL DEFAULT 0",
            "is_active": "ALTER TABLE users ADD COLUMN is_active INTEGER NOT NULL DEFAULT 1",
        }
        for column, statement in migrations.items():
            if column not in user_columns:
                connection.execute(statement)


def backup_database() -> None:
    if not DB_PATH.exists():
        return
    DB_BACKUP_DIR.mkdir(exist_ok=True)
    backup_path = DB_BACKUP_DIR / (
        "cyber_dungeon_" + datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S") + ".sqlite3"
    )
    source = db_connect()
    target = sqlite3.connect(backup_path)
    try:
        source.backup(target)
        target.commit()
    finally:
        target.close()
        source.close()
    backups = sorted(DB_BACKUP_DIR.glob("cyber_dungeon_*.sqlite3"), key=lambda path: path.stat().st_mtime, reverse=True)
    for old_backup in backups[MAX_DB_BACKUPS:]:
        old_backup.unlink(missing_ok=True)


def record_auth_event(username: str, event_type: str, user_id: Optional[int] = None) -> None:
    now = datetime.now(timezone.utc).isoformat()
    with db_connect() as connection:
        connection.execute(
            "INSERT INTO auth_events(user_id, username, event_type, created_at) VALUES (?, ?, ?, ?)",
            (user_id, username, event_type, now),
        )
        if user_id and event_type == "login_failed":
            connection.execute(
                "UPDATE users SET failed_login_attempts = failed_login_attempts + 1 WHERE id = ?",
                (user_id,),
            )
        elif user_id and event_type == "login_success":
            connection.execute(
                "UPDATE users SET last_login_at = ?, failed_login_attempts = 0 WHERE id = ?",
                (now, user_id),
            )


def append_account_log(event_type: str, username: str, timestamp: Optional[str] = None) -> None:
    timestamp = timestamp or datetime.now(timezone.utc).isoformat()
    labels = {
        "register": "KAYIT",
        "login_success": "GIRIS_BASARILI",
        "login_failed": "GIRIS_BASARISIZ",
    }
    line = f"{labels.get(event_type, event_type.upper())} | tarih={timestamp} | kullanici={username}\n"
    try:
        with ACCOUNT_LOG_PATH.open("a", encoding="utf-8") as log_file:
            log_file.write(line)
    except OSError:
        pass


def sync_registered_accounts_to_log() -> None:
    try:
        existing_log = ACCOUNT_LOG_PATH.read_text(encoding="utf-8") if ACCOUNT_LOG_PATH.exists() else ""
        with db_connect() as connection:
            users = connection.execute(
                "SELECT username, created_at FROM users ORDER BY created_at"
            ).fetchall()
        with ACCOUNT_LOG_PATH.open("a", encoding="utf-8") as log_file:
            for user in users:
                marker = f"KAYIT | tarih={user['created_at']} | kullanici={user['username']}"
                if marker not in existing_log:
                    log_file.write(marker + "\n")
                    existing_log += marker + "\n"
    except OSError:
        pass


def hash_password(password: str, salt: Optional[bytes] = None) -> str:
    salt = salt or secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 180_000)
    return f"pbkdf2_sha256$180000${salt.hex()}${digest.hex()}"


def verify_password(password: str, encoded: str) -> bool:
    try:
        algorithm, rounds, salt_hex, digest_hex = encoded.split("$")
        if algorithm != "pbkdf2_sha256":
            return False
        candidate = hashlib.pbkdf2_hmac("sha256", password.encode(), bytes.fromhex(salt_hex), int(rounds))
        return hmac.compare_digest(candidate.hex(), digest_hex)
    except (ValueError, TypeError):
        return False


def session_user_id(request: Request) -> Optional[int]:
    token = request.cookies.get(SESSION_COOKIE) or request.headers.get("x-session-token")
    if not token:
        return None
    now = datetime.now(timezone.utc).isoformat()
    with db_connect() as connection:
        row = connection.execute(
            "SELECT user_id FROM sessions WHERE token = ? AND expires_at > ?", (token, now)
        ).fetchone()
    return int(row["user_id"]) if row else None


def create_session(user_id: int, response: Response) -> str:
    token = secrets.token_urlsafe(32)
    expires = datetime.now(timezone.utc) + timedelta(days=SESSION_DAYS)
    with db_connect() as connection:
        connection.execute("DELETE FROM sessions WHERE user_id = ?", (user_id,))
        connection.execute(
            "INSERT INTO sessions(token, user_id, expires_at) VALUES (?, ?, ?)",
            (token, user_id, expires.isoformat()),
        )
    response.set_cookie(SESSION_COOKIE, token, max_age=SESSION_DAYS * 86400,
                        httponly=True, samesite="lax", secure=False, path="/")
    return token


def account_achievements() -> list:
    if not current_user_id:
        return []
    if achievement_cache_user_id == current_user_id:
        unlocked = achievement_cache
    else:
        with db_connect() as connection:
            row = connection.execute("SELECT achievements_json FROM profiles WHERE user_id = ?", (current_user_id,)).fetchone()
        unlocked = json.loads(row["achievements_json"]) if row else []
    return [
        {"id": achievement_id, **definition, "unlocked": achievement_id in unlocked}
        for achievement_id, definition in ACHIEVEMENTS.items()
    ]


game_map: list = []
fog_matrix: list = []
enemies: list = []
chests: list = []
gravestones: list = []
merchant_state = {"x": 0, "y": 0}
stairs_pos: dict = {"x": -1, "y": -1}
stairs_positions: list = []
next_enemy_id = 1
game_over = False
game_won = False
pending_level_ups = 0
boss_entity: Optional[dict] = None
current_user_id: Optional[int] = None
last_state_save_at = 0.0
achievement_cache_user_id: Optional[int] = None
achievement_cache: list = []
class_selected = False
character_class: Optional[str] = None
daily_quest: dict = {}
current_floor = 1
secret_map_index = 1
secret_key = {"x": -1, "y": -1, "active": False}
secret_door = {"x": -1, "y": -1, "open": False}
station_rooms: list = []
vents: list = []
terminals: list = []
cage_pos: dict = {"x": -1, "y": -1}
red_key = {"x": -1, "y": -1, "active": False}
cat_state: dict = {"active": False, "rescued": False, "x": -1, "y": -1, "trail": []}
red_hatch_pos: dict = {"x": -1, "y": -1}
cat_quest: dict = {
    "rescued": False, "in_red_map": False, "has_red_key": False,
    "spawner_open": False, "saved_floor_state": None, "red_map_data": {},
    "cat_x": -1, "cat_y": -1, "history": [],
}
has_secret_key = False

player_state = {
    "hp": 100, "max_hp": 100,
    "gold": 0, "exp": 0, "level": 1,
    "exp_to_next": EXP_TO_LEVEL,
    "attack_power": BASE_ATTACK,
    "damage_reduction": 0,
    "mp": BASE_MP, "max_mp": BASE_MP,
    "invisible_until": 0,
    "level_attack_bonus": 0, "level_defense_bonus": 0,
    "level_max_hp_bonus": 0, "level_max_mp_bonus": 0,
    "x": 0, "y": 0,
    "character_class": None,
    "stats": {"enemies_killed": 0, "total_gold_earned": 0, "highest_floor": 1, "games_won": 0},
}

equipment: dict = {"weapon": None, "armor": None, "accessory": None}
inventory: list = []
MAX_INVENTORY = 12


def runtime_state() -> dict:
    return {
        "game_map": game_map, "fog_matrix": fog_matrix, "enemies": enemies, "chests": chests,
        "gravestones": gravestones,
        "merchant_state": merchant_state, "stairs_pos": stairs_pos, "stairs_positions": stairs_positions,
        "next_enemy_id": next_enemy_id,
        "game_over": game_over, "game_won": game_won, "boss_entity": boss_entity,
        "class_selected": class_selected, "character_class": character_class,
        "daily_quest": daily_quest, "current_floor": current_floor, "secret_map_index": secret_map_index,
        "secret_key": secret_key, "secret_door": secret_door, "has_secret_key": has_secret_key,
        "red_key": red_key, "cat_state": cat_state,
        "red_hatch_pos": red_hatch_pos, "cat_quest": cat_quest,
        "station_rooms": station_rooms, "vents": vents, "terminals": terminals, "cage_pos": cage_pos,
        "player_state": player_state, "equipment": equipment, "inventory": inventory,
        "pending_level_ups": pending_level_ups,
    }


def clear_runtime_state() -> None:
    global game_map, fog_matrix, enemies, chests, gravestones, merchant_state, stairs_pos, stairs_positions, next_enemy_id
    global game_over, game_won, boss_entity, class_selected, character_class, daily_quest
    global current_floor, secret_map_index, secret_key, secret_door, has_secret_key
    global station_rooms, vents, terminals, cage_pos, red_key, cat_state, red_hatch_pos, cat_quest, equipment, inventory, pending_level_ups
    game_map, fog_matrix, enemies, chests, gravestones = [], [], [], [], []
    merchant_state, stairs_pos, stairs_positions = {"x": 0, "y": 0}, {"x": -1, "y": -1}, []
    station_rooms, vents, terminals = [], [], []
    cage_pos = {"x": -1, "y": -1}
    next_enemy_id = 1
    game_over = game_won = False
    boss_entity = None
    class_selected = False
    character_class = None
    daily_quest = {}
    current_floor = secret_map_index = 1
    secret_key = {"x": -1, "y": -1, "active": False}
    secret_door = {"x": -1, "y": -1, "open": False}
    red_key = {"x": -1, "y": -1, "active": False}
    cat_state = {"active": False, "rescued": False, "x": -1, "y": -1, "trail": []}
    red_hatch_pos = {"x": -1, "y": -1}
    cat_quest = {
        "rescued": False, "in_red_map": False, "has_red_key": False,
        "spawner_open": False, "saved_floor_state": None, "red_map_data": {},
        "cat_x": -1, "cat_y": -1, "history": [],
    }
    has_secret_key = False
    equipment = {"weapon": None, "armor": None, "accessory": None}
    inventory = []
    pending_level_ups = 0
    player_state.clear()
    player_state.update({
        "hp": 100, "max_hp": 100, "gold": 0, "exp": 0, "level": 1,
        "exp_to_next": EXP_TO_LEVEL, "attack_power": BASE_ATTACK, "damage_reduction": 0,
        "mp": BASE_MP, "max_mp": BASE_MP, "level_attack_bonus": 0,
        "level_defense_bonus": 0, "level_max_hp_bonus": 0, "level_max_mp_bonus": 0,
        "x": 0, "y": 0, "character_class": None,
        "stats": {"enemies_killed": 0, "total_gold_earned": 0, "highest_floor": 1, "games_won": 0},
    })
    init_daily_quest()


def load_game_state(user_id: int) -> None:
    global current_user_id, game_map, fog_matrix, enemies, chests, gravestones, merchant_state, stairs_pos, stairs_positions, next_enemy_id
    global game_over, game_won, boss_entity, class_selected, character_class, daily_quest
    global current_floor, secret_map_index, secret_key, secret_door, has_secret_key, red_key, cat_state, red_hatch_pos, cat_quest
    global player_state, equipment, inventory, pending_level_ups
    global achievement_cache_user_id, achievement_cache
    current_user_id = user_id
    with db_connect() as connection:
        row = connection.execute("SELECT state_json, achievements_json FROM profiles WHERE user_id = ?", (user_id,)).fetchone()
    achievement_cache_user_id = user_id
    achievement_cache = json.loads(row["achievements_json"]) if row and row["achievements_json"] else []
    if not row:
        clear_runtime_state()
        return
    state = json.loads(row["state_json"])
    if "player_state" not in state:
        clear_runtime_state()
        return
    game_map = state.get("game_map", [])
    if not state.get("cat_quest", {}).get("in_red_map"):
        ensure_map_connected(game_map)
    fog_matrix = state.get("fog_matrix", [])
    enemies = state.get("enemies", [])
    chests = state.get("chests", [])
    gravestones = state.get("gravestones", [])
    merchant_state = state.get("merchant_state", {"x": 0, "y": 0})
    stairs_pos = state.get("stairs_pos", {"x": -1, "y": -1})
    stairs_positions = state.get("stairs_positions", [])
    if not stairs_positions and stairs_pos.get("x", -1) >= 0:
        stairs_positions = [dict(stairs_pos)]
    next_enemy_id = state.get("next_enemy_id", 1)
    game_over, game_won = state.get("game_over", False), state.get("game_won", False)
    boss_entity = state.get("boss_entity")
    class_selected, character_class = state.get("class_selected", False), state.get("character_class")
    daily_quest = state.get("daily_quest", {})
    if daily_quest.get("completed"):
        init_daily_quest(exclude_name=daily_quest.get("name"))
    current_floor, secret_map_index = state.get("current_floor", 1), state.get("secret_map_index", 1)
    secret_key = state.get("secret_key", {"x": -1, "y": -1, "active": False})
    secret_door = state.get("secret_door", {"x": -1, "y": -1, "open": False})
    red_key = state.get("red_key", {"x": -1, "y": -1, "active": False})
    cat_state = state.get("cat_state", {"active": False, "rescued": False, "x": -1, "y": -1, "trail": []})
    red_hatch_pos = state.get("red_hatch_pos", {"x": -1, "y": -1})
    cat_quest = state.get("cat_quest", {
        "rescued": False, "in_red_map": False, "has_red_key": False,
        "spawner_open": False, "saved_floor_state": None, "red_map_data": {},
        "cat_x": -1, "cat_y": -1, "history": [],
    })
    if secret_map_index != 3 and not cat_quest.get("in_red_map"):
        red_hatch_pos = {"x": -1, "y": -1}
    if game_over:
        restore_floor_after_red_map_death()
    station_rooms = state.get("station_rooms", [])
    vents = state.get("vents", [])
    terminals = state.get("terminals", [])
    cage_pos = state.get("cage_pos", {"x": -1, "y": -1})
    has_secret_key = state.get("has_secret_key", False)
    player_state = state.get("player_state", player_state)
    player_state.setdefault("stats", {"enemies_killed": 0, "total_gold_earned": 0, "highest_floor": current_floor, "games_won": 0})
    player_state.setdefault("invisible_until", 0)
    if (game_map and not cat_quest.get("in_red_map") and secret_map_index < SECRET_MAP_COUNT
            and len(stairs_positions) < 3):
        for row in game_map:
            for x, tile in enumerate(row):
                if tile == STAIRS:
                    row[x] = TILE
        spawn_stairs()
        if secret_map_index == 3:
            setup_red_hatch()
    if station_rooms and not cat_quest.get("in_red_map"):
        game_map = generate_bsp_map()
        station_rooms, vents, terminals = [], [], []
        cage_pos = {"x": -1, "y": -1}
        player_state["x"], player_state["y"] = find_safe_spawn(game_map)
        init_fog()
        spawn_chests()
        spawn_merchant()
        spawn_stairs()
        spawn_secret_route()
        spawn_enemies()
    equipment = state.get("equipment", {"weapon": None, "armor": None, "accessory": None})
    inventory = state.get("inventory", [])
    pending_level_ups = state.get("pending_level_ups", 0)
    load_gravestones_for_floor()


def save_game_state() -> None:
    global last_state_save_at, achievement_cache_user_id, achievement_cache
    if not current_user_id:
        return
    stats = player_state.setdefault("stats", {"enemies_killed": 0, "total_gold_earned": 0, "highest_floor": 1, "games_won": 0})
    stats["highest_floor"] = max(stats.get("highest_floor", 1), current_floor)
    with db_connect() as connection:
        row = connection.execute("SELECT achievements_json FROM profiles WHERE user_id = ?", (current_user_id,)).fetchone()
        unlocked = set(json.loads(row["achievements_json"]) if row else [])
        if stats.get("enemies_killed", 0) >= 1: unlocked.add("first_blood")
        if player_state.get("level", 1) >= 5: unlocked.add("level_5")
        if stats.get("highest_floor", 1) >= 10: unlocked.add("floor_10")
        if stats.get("total_gold_earned", 0) >= 1000: unlocked.add("gold_1000")
        if stats.get("games_won", 0) >= 1: unlocked.add("boss_slayer")
        connection.execute(
            "INSERT INTO profiles(user_id, state_json, achievements_json) VALUES (?, ?, ?) "
            "ON CONFLICT(user_id) DO UPDATE SET state_json=excluded.state_json, achievements_json=excluded.achievements_json",
            (current_user_id, json.dumps(runtime_state(), ensure_ascii=False), json.dumps(sorted(unlocked))),
        )
    achievement_cache_user_id = current_user_id
    achievement_cache = sorted(unlocked)
    last_state_save_at = time.monotonic()


@app.middleware("http")
async def account_state_middleware(request: Request, call_next):
    public_paths = {
        "/", "/index.html", "/api/auth/register", "/api/auth/login", "/api/auth/logout",
        "/api/admin/account-log", "/api/log-user", "/favicon.ico", "/view-logs",
        "/icon.png", "/icon.svg", "/knight_sheet.png", "/monters.png"
    }
    if request.url.path.startswith("/api/") and request.url.path not in public_paths:
        user_id = session_user_id(request)
        if not user_id:
            return JSONResponse({"detail": "Giris yapman gerekiyor"}, status_code=401)
        if current_user_id != user_id:
            load_game_state(user_id)
        response = await call_next(request)
        request_is_move = request.url.path == "/api/move"
        now = time.monotonic()
        if response.status_code < 500 and (not request_is_move or now - last_state_save_at >= STATE_SAVE_INTERVAL):
            save_game_state()
        return response
    return await call_next(request)


class MoveRequest(BaseModel):
    direction: str = Field(..., pattern="^(up|down|left|right)$")

class BuyItemRequest(BaseModel):
    item: str

class FireballRequest(BaseModel):
    enemy_id: int

class SelectClassRequest(BaseModel):
    character_class: str = Field(..., pattern="^(Warrior|Mage|Rogue)$")

class EquipRequest(BaseModel):
    item_index: int

class UseItemRequest(BaseModel):
    item_index: int

class UnequipRequest(BaseModel):
    slot: str

class LevelUpRequest(BaseModel):
    choice: str = Field(..., pattern="^(power|vitality|focus)$")

class AuthRequest(BaseModel):
    username: str = Field(..., min_length=3, max_length=24, pattern="^[A-Za-z0-9_]+$")
    password: str = Field(..., min_length=6, max_length=128)

class UserLogPayload(BaseModel):
    username: str
    action: str


class BSPNode:
    def __init__(self, x, y, w, h):
        self.x, self.y, self.w, self.h = x, y, w, h
        self.left = self.right = None
        self.room = None

    def split(self, min_size=7):
        if self.left or self.right:
            return
        can_h = self.w >= min_size * 2
        can_v = self.h >= min_size * 2
        if not can_h and not can_v:
            return
        horizontal = random.choice([True, False]) if (can_h and can_v) else can_v
        if horizontal:
            split_at = random.randint(min_size, self.h - min_size)
            self.left  = BSPNode(self.x, self.y, self.w, split_at)
            self.right = BSPNode(self.x, self.y + split_at, self.w, self.h - split_at)
        else:
            split_at = random.randint(min_size, self.w - min_size)
            self.left  = BSPNode(self.x, self.y, split_at, self.h)
            self.right = BSPNode(self.x + split_at, self.y, self.w - split_at, self.h)
        self.left.split(min_size)
        self.right.split(min_size)

    def create_rooms(self, grid):
        if self.left or self.right:
            if self.left:  self.left.create_rooms(grid)
            if self.right: self.right.create_rooms(grid)
            lr = self.left.get_room() if self.left else None
            rr = self.right.get_room() if self.right else None
            if lr and rr:
                _carve_corridor(grid, lr, rr)
        else:
            pad = 1
            rw = random.randint(4, max(4, self.w - pad * 2))
            rh = random.randint(4, max(4, self.h - pad * 2))
            rx = self.x + pad + random.randint(0, max(0, self.w - pad * 2 - rw))
            ry = self.y + pad + random.randint(0, max(0, self.h - pad * 2 - rh))
            rx = max(1, min(rx, GRID_SIZE - rw - 1))
            ry = max(1, min(ry, GRID_SIZE - rh - 1))
            rw = min(rw, GRID_SIZE - rx - 1)
            rh = min(rh, GRID_SIZE - ry - 1)
            self.room = (rx, ry, rw, rh)
            for yy in range(ry, ry + rh):
                for xx in range(rx, rx + rw):
                    grid[yy][xx] = TILE

    def get_room(self):
        if self.room:
            return self.room
        lr = self.left.get_room() if self.left else None
        rr = self.right.get_room() if self.right else None
        if lr and rr:
            return random.choice([lr, rr])
        return lr or rr


def _room_center(room):
    rx, ry, rw, rh = room
    return rx + rw // 2, ry + rh // 2


def _carve_corridor(grid, room_a, room_b):
    ax, ay = _room_center(room_a)
    bx, by = _room_center(room_b)
    if random.random() < 0.5:
        for x in range(min(ax, bx), max(ax, bx) + 1):
            if 0 < x < GRID_SIZE - 1: grid[ay][x] = TILE
        for y in range(min(ay, by), max(ay, by) + 1):
            if 0 < y < GRID_SIZE - 1: grid[y][bx] = TILE
    else:
        for y in range(min(ay, by), max(ay, by) + 1):
            if 0 < y < GRID_SIZE - 1: grid[y][ax] = TILE
        for x in range(min(ax, bx), max(ax, bx) + 1):
            if 0 < x < GRID_SIZE - 1: grid[ay][x] = TILE


def generate_station_map() -> tuple[list, list, list, list, dict]:
    grid = [[WALL] * GRID_SIZE for _ in range(GRID_SIZE)]
    rooms = [
        {"name": "Kafeterya", "x1": 8, "y1": 9, "x2": 24, "y2": 20},
        {"name": "Elektrik Odası", "x1": 2, "y1": 3, "x2": 11, "y2": 12},
        {"name": "Reaktör Odası", "x1": 22, "y1": 19, "x2": 30, "y2": 29},
        {"name": "Güvenlik Odası", "x1": 22, "y1": 3, "x2": 30, "y2": 12},
    ]

    for room in rooms:
        for y in range(room["y1"], room["y2"] + 1):
            for x in range(room["x1"], room["x2"] + 1):
                grid[y][x] = TILE

    connects = [
        ((17, 14), (17, 19)),
        ((17, 14), (8, 8)),
        ((17, 14), (26, 14)),
        ((17, 14), (26, 24)),
    ]
    for (x1, y1), (x2, y2) in connects:
        x, y = x1, y1
        while x != x2:
            grid[y][x] = TILE
            x += 1 if x < x2 else -1
        while y != y2:
            grid[y][x] = TILE
            y += 1 if y < y2 else -1

    for room in rooms:
        cx = (room["x1"] + room["x2"]) // 2
        cy = (room["y1"] + room["y2"]) // 2
        for y in range(cy - 1, cy + 2):
            for x in range(cx - 1, cx + 2):
                if 0 <= x < GRID_SIZE and 0 <= y < GRID_SIZE:
                    grid[y][x] = TILE

    room_list = []
    for room in rooms:
        room_list.append({
            "name": room["name"],
            "x1": room["x1"], "y1": room["y1"],
            "x2": room["x2"], "y2": room["y2"],
        })

    vent_positions = [
        {"id": 1, "x": 12, "y": 14},
        {"id": 2, "x": 23, "y": 14},
        {"id": 3, "x": 26, "y": 24},
    ]
    terminals = [
        {"id": 1, "x": 6, "y": 8, "type": "electrical", "completed": False},
        {"id": 2, "x": 25, "y": 22, "type": "reactor", "completed": False},
    ]
    for vent in vent_positions:
        grid[vent["y"]][vent["x"]] = VENT
    for terminal in terminals:
        grid[terminal["y"]][terminal["x"]] = TERMINAL

    cage_pos = {"x": 27, "y": 7}
    grid[cage_pos["y"]][cage_pos["x"]] = LASER_CAGE
    exit_pos = {"x": 28, "y": 26}
    grid[exit_pos["y"]][exit_pos["x"]] = EXIT_AIRLOCK

    caf_x, caf_y = 17, 15
    player_state["x"], player_state["y"] = caf_x, caf_y
    grid[caf_y][caf_x] = TILE

    return grid, room_list, vent_positions, terminals, cage_pos


def generate_bsp_map() -> list:
    grid = [[WALL] * GRID_SIZE for _ in range(GRID_SIZE)]
    root = BSPNode(0, 0, GRID_SIZE, GRID_SIZE)
    root.split(min_size=7)
    root.create_rooms(grid)
    for yy in range(5):
        for xx in range(5):
            grid[yy][xx] = TILE
    ensure_map_connected(grid)
    return grid


def generate_level_map() -> list:
    grid, rooms, vents_data, terminals_data, cage = generate_station_map()
    global station_rooms, vents, terminals, cage_pos
    station_rooms = rooms
    vents = vents_data
    terminals = terminals_data
    cage_pos = cage
    return grid


def default_cat_quest() -> dict:
    return {
        "rescued": False, "in_red_map": False, "has_red_key": False,
        "spawner_open": False, "saved_floor_state": None, "red_map_data": {},
        "cat_x": -1, "cat_y": -1, "history": [],
    }


def generate_red_map() -> tuple[list, dict]:
    width, height = 18, 9
    grid = [[WALL] * width for _ in range(height)]
    for y in range(1, 8):
        for x in range(1, 17):
            grid[y][x] = TILE
    for x in range(2, 6):
        grid[2][x] = TILE
    for y in range(2, 7):
        grid[y][5] = TILE
    hatch = {"x": 1, "y": 2}
    spawner = {"x": 4, "y": 6, "width": 2, "height": 2}
    grid[hatch["y"]][hatch["x"]] = STAIRS
    for y in range(spawner["y"], spawner["y"] + spawner["height"]):
        for x in range(spawner["x"], spawner["x"] + spawner["width"]):
            grid[y][x] = LASER_CAGE
    red_key_pos = {"x": 10, "y": 4, "active": True}
    data = {
        "width": width, "height": height, "theme": "red",
        "hatch_pos": hatch, "spawner_pos": spawner,
        "red_key": red_key_pos,
        "rooms": [
            {"name": "Kırmızı Koridor", "x1": 1, "y1": 1, "x2": 16, "y2": 5},
            {"name": "Siber Spawner", "x1": 4, "y1": 6, "x2": 5, "y2": 7},
        ],
    }
    return grid, data


def setup_red_hatch() -> None:
    global red_hatch_pos
    if secret_map_index != 3 or not game_map:
        red_hatch_pos = {"x": -1, "y": -1}
        return
    candidates = [(17, 14), (17, 15), (16, 14), (18, 14)]
    candidates += [(x, y) for y in range(1, GRID_SIZE - 1) for x in range(1, GRID_SIZE - 1)]
    hx, hy = next((x, y) for x, y in candidates if is_in_bounds(x, y) and game_map[y][x] == TILE)
    red_hatch_pos = {"x": hx, "y": hy}
    game_map[hy][hx] = STAIRS


def update_cat_follow_history() -> None:
    if not cat_quest.get("rescued"):
        return
    history = cat_quest.setdefault("history", [])
    history.append([player_state["x"], player_state["y"]])
    while len(history) > 4:
        history.pop(0)
    if len(history) >= 3:
        cat_quest["cat_x"], cat_quest["cat_y"] = history[-3]
        cat_state["x"], cat_state["y"] = cat_quest["cat_x"], cat_quest["cat_y"]


def is_at_red_hatch() -> bool:
    return (not cat_quest.get("in_red_map") and secret_map_index == 3 and
            (player_state["x"], player_state["y"]) == (red_hatch_pos.get("x"), red_hatch_pos.get("y")))


def is_at_red_exit() -> bool:
    hatch = cat_quest.get("red_map_data", {}).get("hatch_pos", {})
    if not cat_quest.get("in_red_map"):
        return False
    return abs(player_state["x"] - hatch.get("x", -99)) <= 1 and abs(player_state["y"] - hatch.get("y", -99)) <= 1


def restore_floor_after_red_map_death() -> None:
    global game_map, enemies, chests, fog_matrix, stairs_pos, stairs_positions, merchant_state, boss_entity
    global station_rooms, vents, terminals, cage_pos
    if not cat_quest.get("in_red_map"):
        return
    saved = cat_quest.get("saved_floor_state")
    if not saved:
        return
    game_map = saved["game_map"]
    enemies = saved["enemies"]
    chests = saved["chests"]
    fog_matrix = saved["fog_matrix"]
    stairs_pos = saved["stairs_pos"]
    stairs_positions = saved.get("stairs_positions", [dict(stairs_pos)])
    merchant_state = saved["merchant_state"]
    boss_entity = saved["boss_entity"]
    station_rooms = saved["station_rooms"]
    vents = saved["vents"]
    terminals = saved["terminals"]
    cage_pos = saved["cage_pos"]
    player_state["x"], player_state["y"] = saved["player_x"], saved["player_y"]
    cat_quest["in_red_map"] = False


def find_safe_spawn(grid: list) -> tuple[int, int]:
    preferred = (17, 15)
    if (is_in_bounds(*preferred)
            and grid[preferred[1]][preferred[0]] != WALL):
        return preferred
    for y in range(1, GRID_SIZE - 1):
        for x in range(1, GRID_SIZE - 1):
            if grid[y][x] != WALL:
                return x, y
    return 1, 1


def get_reachable_cells(grid: list, start: tuple = (0, 0)) -> set:
    if not grid or not is_in_bounds(start[0], start[1]):
        return set()
    if grid[start[1]][start[0]] == WALL:
        grid[start[1]][start[0]] = TILE
    reachable = {start}
    queue = deque([start])
    while queue:
        x, y = queue.popleft()
        for dx, dy in DIR_DELTA.values():
            nx, ny = x + dx, y + dy
            if not is_in_bounds(nx, ny) or (nx, ny) in reachable:
                continue
            if grid[ny][nx] == WALL:
                continue
            reachable.add((nx, ny))
            queue.append((nx, ny))
    return reachable


def ensure_map_connected(grid: list) -> None:
    if not grid:
        return
    walkable = {(x, y) for y in range(GRID_SIZE) for x in range(GRID_SIZE) if grid[y][x] != WALL}
    reachable = get_reachable_cells(grid)
    while walkable - reachable:
        target = min(walkable - reachable, key=lambda cell: min(manhattan(cell[0], cell[1], p[0], p[1]) for p in reachable))
        anchor = min(reachable, key=lambda p: manhattan(p[0], p[1], target[0], target[1]))
        ax, ay = anchor
        tx, ty = target
        for x in range(min(ax, tx), max(ax, tx) + 1):
            grid[ay][x] = TILE
        for y in range(min(ay, ty), max(ay, ty) + 1):
            grid[y][tx] = TILE
        walkable = {(x, y) for y in range(GRID_SIZE) for x in range(GRID_SIZE) if grid[y][x] != WALL}
        reachable = get_reachable_cells(grid)


def get_all_floor_tiles() -> list:
    tiles = []
    for y in range(GRID_SIZE):
        for x in range(GRID_SIZE):
            if game_map[y][x] == TILE:
                tiles.append((x, y))
    return tiles


def heuristic(a, b):
    return abs(a[0] - b[0]) + abs(a[1] - b[1])


def astar(start, goal, occupied: set) -> Optional[tuple]:
    if start == goal:
        return None
    open_set = [(0, start)]
    came_from = {}
    g_score = {start: 0}
    visited = set()
    while open_set:
        open_set.sort(key=lambda x: x[0])
        _, current = open_set.pop(0)
        if current in visited:
            continue
        visited.add(current)
        if current == goal:
            path = [current]
            while path[-1] in came_from:
                path.append(came_from[path[-1]])
            path.reverse()
            return path[1] if len(path) > 1 else None
        cx, cy = current
        for dx, dy in [(0, -1), (0, 1), (-1, 0), (1, 0)]:
            nx, ny = cx + dx, cy + dy
            nb = (nx, ny)
            if not is_in_bounds(nx, ny) or game_map[ny][nx] == WALL or nb in visited:
                continue
            if nb != goal and nb in occupied:
                continue
            ng = g_score.get(current, 9999) + 1
            if ng < g_score.get(nb, 9999):
                g_score[nb] = ng
                f = ng + heuristic(nb, goal)
                came_from[nb] = current
                open_set.append((f, nb))
    return None


def is_in_bounds(x: int, y: int) -> bool:
    if game_map:
        return 0 <= y < len(game_map) and 0 <= x < len(game_map[y])
    return 0 <= x < GRID_SIZE and 0 <= y < GRID_SIZE


def find_enemy_by_id(enemy_id: int) -> Optional[dict]:
    for e in enemies:
        if e["id"] == enemy_id:
            return e
    return None


def tile_distance(x1, y1, x2, y2) -> int:
    return max(abs(x1 - x2), abs(y1 - y2))


def manhattan(x1, y1, x2, y2) -> int:
    return abs(x1 - x2) + abs(y1 - y2)


def find_enemy_at(x: int, y: int) -> Optional[dict]:
    for e in enemies:
        if e["x"] == x and e["y"] == y:
            return e
    return None


def get_occupied_cells(exclude_enemy_id: Optional[int] = None) -> set:
    occupied = {(player_state["x"], player_state["y"])}
    for c in chests:
        if c["active"]:
            occupied.add((c["x"], c["y"]))
    occupied.add((merchant_state["x"], merchant_state["y"]))
    for e in enemies:
        if exclude_enemy_id is not None and e["id"] == exclude_enemy_id:
            continue
        occupied.add((e["x"], e["y"]))
    return occupied


def get_spawn_candidates(exclude: Optional[set] = None) -> list:
    exclude = exclude or set()
    return [(x, y) for y in range(GRID_SIZE) for x in range(GRID_SIZE)
            if game_map[y][x] == TILE and (x, y) not in exclude]


def spawn_stairs() -> None:
    global stairs_pos, stairs_positions
    if current_floor >= BOSS_FLOOR or secret_map_index >= SECRET_MAP_COUNT:
        stairs_pos = {"x": -1, "y": -1}
        stairs_positions = []
        return
    exclude = {(player_state["x"], player_state["y"]), (0, 0)}
    for c in chests:
        exclude.add((c["x"], c["y"]))
    exclude.add((merchant_state["x"], merchant_state["y"]))
    candidates = get_spawn_candidates(exclude)
    random.shuffle(candidates)
    spaced_candidates = []
    for candidate in candidates:
        if all(manhattan(candidate[0], candidate[1], selected[0], selected[1]) >= 12
               for selected in spaced_candidates):
            spaced_candidates.append(candidate)
        if len(spaced_candidates) == 3:
            break
    if len(spaced_candidates) < 3:
        spaced_candidates.extend(candidate for candidate in candidates if candidate not in spaced_candidates)
    stairs_positions = [{"x": x, "y": y} for x, y in spaced_candidates[:3]]
    stairs_positions.sort(key=lambda point: (point["y"], point["x"]))
    for stair in stairs_positions:
        sx, sy = stair["x"], stair["y"]
        game_map[sy][sx] = STAIRS
        if fog_matrix:
            for dy in range(-1, 2):
                for dx in range(-1, 2):
                    nx, ny = sx + dx, sy + dy
                    if is_in_bounds(nx, ny) and fog_matrix[ny][nx] == FOG_UNEXPLORED:
                        fog_matrix[ny][nx] = FOG_FOGGY
    stairs_pos = dict(stairs_positions[0]) if stairs_positions else {"x": -1, "y": -1}


def spawn_chests() -> None:
    global chests
    chests = []
    candidates = get_spawn_candidates({(0, 0)})
    random.shuffle(candidates)
    for i, (x, y) in enumerate(candidates[:CHEST_COUNT]):
        chests.append({"id": i + 1, "x": x, "y": y, "active": True,
                       "treasure": secret_map_index >= SECRET_MAP_COUNT and i == 0})


def spawn_merchant() -> None:
    global merchant_state
    exclude = {(player_state["x"], player_state["y"]), (0, 0), (0, 1), (1, 0), (1, 1)}
    for c in chests:
        if c["active"]:
            exclude.add((c["x"], c["y"]))
    candidates = [c for c in get_spawn_candidates(exclude) if c not in exclude]
    if not candidates:
        merchant_state = {"x": GRID_SIZE // 2, "y": GRID_SIZE // 2}
        return
    x, y = random.choice(candidates)
    merchant_state = {"x": x, "y": y}


def _scale_enemy(etype: str, floor: int) -> dict:
    base = ENEMY_TYPES[etype]
    scale = 1.0 + (floor - 1) * 0.18
    return {
        "hp":     max(1, int(base["hp"]     * scale)),
        "max_hp": max(1, int(base["hp"]     * scale)),
        "damage": max(1, int(base["damage"] * scale)),
        "exp":    int(base["exp"]   * scale),
        "gold":   int(base["gold"]  * scale),
        "move_speed": base["move_speed"],
        "range":  base["range"],
        "color":  base["color"],
    }


def spawn_enemies() -> None:
    global enemies, next_enemy_id
    enemies = []
    next_enemy_id = 1
    if current_floor >= BOSS_FLOOR or secret_map_index >= SECRET_MAP_COUNT:
        return

    exclude = {(player_state["x"], player_state["y"])}
    for c in chests:
        if c["active"]:
            exclude.add((c["x"], c["y"]))
    exclude.add((merchant_state["x"], merchant_state["y"]))
    exclude.add((stairs_pos["x"], stairs_pos["y"]))
    if secret_key["active"]:
        exclude.add((secret_key["x"], secret_key["y"]))
    exclude.add((secret_door["x"], secret_door["y"]))
    candidates = get_spawn_candidates(exclude)
    random.shuffle(candidates)

    enemy_count = min(MAX_ENEMY_COUNT, ENEMY_COUNT + (current_floor - 1) // 5)
    type_pool = ["Goblin"] * 4 + ["Skeleton Archer"] * 2 + ["Poison Zombie"] * 6 + (["Orc Bruiser"] * 2 if current_floor >= 2 else [])

    for x, y in candidates[:enemy_count]:
        etype = random.choice(type_pool)
        stats = _scale_enemy(etype, current_floor)
        enemy = {
            "id": next_enemy_id,
            "name": etype,
            "x": x, "y": y,
            **stats,
            "move_timer": 0,
            "last_throw": 0.0,
        }
        enemies.append(enemy)
        next_enemy_id += 1


def spawn_boss() -> None:
    global boss_entity
    exclude = {(player_state["x"], player_state["y"]), (0, 0)}
    for c in chests:
        exclude.add((c["x"], c["y"]))
    candidates = get_spawn_candidates(exclude)
    candidates.sort(key=lambda p: -(p[0] + p[1]))
    bx, by = candidates[0] if candidates else (GRID_SIZE // 2, GRID_SIZE // 2)

    import copy
    boss_entity = copy.deepcopy(CYBER_DRAGON)
    boss_entity["x"] = bx
    boss_entity["y"] = by
    boss_entity["aoe_timer"] = 0


def spawn_secret_route() -> None:
    global secret_key, secret_door, has_secret_key
    has_secret_key = False
    secret_key = {"x": -1, "y": -1, "active": False}
    secret_door = {"x": -1, "y": -1, "open": False}
    if secret_map_index >= SECRET_MAP_COUNT:
        return
    exclude = {(player_state["x"], player_state["y"]), (0, 0),
               (stairs_pos["x"], stairs_pos["y"]),
               (merchant_state["x"], merchant_state["y"])}
    exclude.update((c["x"], c["y"]) for c in chests if c["active"])
    floor_candidates = get_spawn_candidates(exclude)
    if not floor_candidates:
        return
    random.shuffle(floor_candidates)
    key_pos = floor_candidates[0]
    distant_candidates = [p for p in floor_candidates[1:]
                          if abs(p[0] - key_pos[0]) + abs(p[1] - key_pos[1]) >= GRID_SIZE // 3]
    if not distant_candidates:
        distant_candidates = floor_candidates[1:]
    if not distant_candidates:
        return

    wall_candidates = []
    for y in range(1, GRID_SIZE - 1):
        for x in range(1, GRID_SIZE - 1):
            if game_map[y][x] != WALL or (x, y) in exclude:
                continue
            has_floor_neighbor = any(
                game_map[y + dy][x + dx] == TILE
                for dx, dy in DIR_DELTA.values()
            )
            if has_floor_neighbor:
                wall_candidates.append((x, y))
    if not wall_candidates:
        return
    door_pos = random.choice(wall_candidates)
    secret_key = {"x": key_pos[0], "y": key_pos[1], "active": True}
    secret_door = {"x": door_pos[0], "y": door_pos[1], "open": False}
    game_map[door_pos[1]][door_pos[0]] = SECRET_DOOR


def init_fog() -> None:
    global fog_matrix
    height = len(game_map) or GRID_SIZE
    width = len(game_map[0]) if game_map else GRID_SIZE
    fog_matrix = [[FOG_UNEXPLORED] * width for _ in range(height)]


def update_fog(px: int, py: int, radius: int = 4) -> None:
    for y in range(len(fog_matrix)):
        for x in range(len(fog_matrix[y])):
            if fog_matrix[y][x] == FOG_VISIBLE:
                fog_matrix[y][x] = FOG_FOGGY
    for dy in range(-radius, radius + 1):
        for dx in range(-radius, radius + 1):
            if abs(dx) + abs(dy) <= radius:
                nx, ny = px + dx, py + dy
                if is_in_bounds(nx, ny):
                    fog_matrix[ny][nx] = FOG_VISIBLE


def is_tile_visible(x: int, y: int) -> bool:
    return fog_matrix[y][x] == FOG_VISIBLE


def get_visible_enemies() -> list:
    return [dict(e) for e in enemies if is_tile_visible(e["x"], e["y"])]


def get_visible_chests() -> list:
    result = []
    for c in chests:
        d = dict(c)
        d["visible"] = c["active"] and is_tile_visible(c["x"], c["y"])
        result.append(d)
    return result


def get_visible_merchant() -> dict:
    m = dict(merchant_state)
    m["visible"] = is_tile_visible(m["x"], m["y"])
    return m


def is_at_merchant() -> bool:
    return (player_state["x"] == merchant_state["x"] and player_state["y"] == merchant_state["y"])


def is_at_stairs() -> bool:
    return any((player_state["x"], player_state["y"]) == (stair["x"], stair["y"])
               for stair in stairs_positions)


def is_at_secret_door() -> bool:
    return (player_state["x"] == secret_door["x"] and player_state["y"] == secret_door["y"])


def collect_secret_key(logs: list) -> None:
    global secret_key, secret_door, has_secret_key
    if secret_key["active"] and (player_state["x"], player_state["y"]) == (secret_key["x"], secret_key["y"]):
        secret_key["active"] = False
        has_secret_key = True
        secret_door["open"] = True
        logs.append({"type": "quest", "message": f"🗝️ Gizli geçit anahtarını buldun! Harita {secret_map_index}/5"})


def spawn_cat_cage_floor3() -> None:
    global red_key, cat_state, cage_pos
    if current_floor != 3:
        return
    if not isinstance(cage_pos, dict) or cage_pos.get("x") is None:
        cage_pos = {"x": 27, "y": 7}
    if 0 <= cage_pos["x"] < GRID_SIZE and 0 <= cage_pos["y"] < GRID_SIZE:
        game_map[cage_pos["y"]][cage_pos["x"]] = LASER_CAGE

    if red_key.get("active") is False and red_key.get("x", -1) == -1:
        candidates = []
        for y in range(1, GRID_SIZE - 1):
            for x in range(1, GRID_SIZE - 1):
                if game_map[y][x] != WALL and (x, y) not in {(player_state["x"], player_state["y"]), (cage_pos["x"], cage_pos["y"]), (0, 0)}:
                    candidates.append((x, y))
        if candidates:
            candidate = random.choice(candidates)
            red_key = {"x": candidate[0], "y": candidate[1], "active": True}

    cat_state = {
        "active": True,
        "rescued": False,
        "x": cage_pos["x"],
        "y": max(0, cage_pos["y"] - 1),
        "trail": [(player_state["x"], player_state["y"])],
    }


def clear_cat_state() -> None:
    global red_key, cat_state
    red_key = {"x": -1, "y": -1, "active": False}
    cat_state = {"active": False, "rescued": False, "x": -1, "y": -1, "trail": []}


def collect_red_key(logs: list) -> None:
    global red_key
    if cat_quest.get("in_red_map"):
        red_map_key = cat_quest.get("red_map_data", {}).get("red_key", {})
        if red_map_key.get("active") and (player_state["x"], player_state["y"]) == (red_map_key.get("x"), red_map_key.get("y")):
            red_map_key["active"] = False
            cat_quest["has_red_key"] = True
            logs.append({"type": "quest", "message": "🟥 Kırmızı anahtar alındı. Spawner açılabilir."})
        return
    if red_key.get("active") and (player_state["x"], player_state["y"]) == (red_key["x"], red_key["y"]):
        red_key["active"] = False
        logs.append({"type": "quest", "message": "🟥 Kırmızı anahtar alındı. Lazer kafes açılabilir."})


def is_adjacent(ax: int, ay: int, bx: int, by: int) -> bool:
    return abs(ax - bx) + abs(ay - by) <= 1


def update_cat_follow() -> None:
    if not cat_state.get("active") or not cat_state.get("rescued"):
        return
    trail = cat_state.setdefault("trail", [])
    trail.append((player_state["x"], player_state["y"]))
    if len(trail) > 3:
        trail[:] = trail[-3:]
    if len(trail) < 2:
        return
    target_x, target_y = trail[-2]
    cx, cy = cat_state["x"], cat_state["y"]
    if (cx, cy) == (target_x, target_y):
        return
    options = []
    for dx, dy in DIR_DELTA.values():
        nx, ny = cx + dx, cy + dy
        if not is_in_bounds(nx, ny):
            continue
        if game_map[ny][nx] == WALL:
            continue
        if (nx, ny) == (player_state["x"], player_state["y"]):
            continue
        score = abs(nx - target_x) + abs(ny - target_y)
        options.append((score, nx, ny))
    if not options:
        return
    _, nx, ny = min(options)
    cat_state["x"], cat_state["y"] = nx, ny


@app.post("/api/unlock-cat")
async def unlock_cat():
    require_class_selected()
    if cat_quest.get("in_red_map"):
        spawner = cat_quest.get("red_map_data", {}).get("spawner_pos", {})
        distance = ((player_state["x"] - spawner.get("x", -99)) ** 2 +
                    (player_state["y"] - spawner.get("y", -99)) ** 2) ** 0.5
        if cat_quest.get("rescued"):
            return {**build_status(), "success": True, "logs": [{"type": "info", "message": "🐾 Siber kedi seni takip ediyor."}]}
        if not cat_quest.get("has_red_key"):
            raise HTTPException(400, detail="Kırmızı anahtar eksik")
        if distance > 1.5:
            raise HTTPException(400, detail="Spawner'ın yanında olmalısın")
        cat_quest["rescued"] = True
        cat_quest["spawner_open"] = True
        cat_quest["has_red_key"] = False
        cat_quest["cat_x"], cat_quest["cat_y"] = player_state["x"] - 1, player_state["y"]
        if not is_in_bounds(cat_quest["cat_x"], cat_quest["cat_y"]):
            cat_quest["cat_x"], cat_quest["cat_y"] = player_state["x"], player_state["y"] - 1
        cat_quest["history"] = [[player_state["x"], player_state["y"]]] * 3
        cat_state.update({"active": True, "rescued": True, "x": cat_quest["cat_x"], "y": cat_quest["cat_y"], "trail": []})
        return {**build_status(), "success": True, "message": "Kafes açıldı", "logs": [{"type": "quest", "message": "🐾 Siber Kedi kurtarıldı! Arkandan geliyor."}]}
    if not cat_state.get("active"):
        raise HTTPException(400, detail="Kafes aktif değil")
    if cat_state.get("rescued"):
        return {**build_status(), "success": True, "message": "Siber kedi zaten serbest", "logs": [{"type": "info", "message": "🐾 Siber kedi seni takip ediyor."}]}
    if red_key.get("active"):
        raise HTTPException(400, detail="Kırmızı anahtar eksik")
    if not cage_pos or not is_adjacent(player_state["x"], player_state["y"], cage_pos["x"], cage_pos["y"]):
        raise HTTPException(400, detail="Lazer kafesin yanındasın ama anahtar hazır değil")

    cat_state["rescued"] = True
    cat_state["x"], cat_state["y"] = cage_pos["x"], max(0, cage_pos["y"] - 1)
    cat_state["trail"] = [(player_state["x"], player_state["y"])]
    logs = [{"type": "quest", "message": "🔓 Lazer kafes açıldı. Siber kedi serbest kaldı!"}]
    return {**build_status(), "success": True, "message": "Kafes açıldı", "logs": logs}


@app.post("/api/enter-red-map")
async def enter_red_map():
    global game_map, enemies, chests, fog_matrix, stairs_pos, stairs_positions, merchant_state, boss_entity
    require_class_selected()
    if secret_map_index != 3 or cat_quest.get("in_red_map") or not is_at_red_hatch():
        raise HTTPException(400, detail="Kırmızı Oda girişinde değilsin")
    cat_quest["saved_floor_state"] = {
        "game_map": copy.deepcopy(game_map), "enemies": copy.deepcopy(enemies),
        "chests": copy.deepcopy(chests), "player_x": player_state["x"],
        "player_y": player_state["y"], "fog_matrix": copy.deepcopy(fog_matrix),
        "stairs_pos": copy.deepcopy(stairs_pos), "stairs_positions": copy.deepcopy(stairs_positions),
        "merchant_state": copy.deepcopy(merchant_state),
        "boss_entity": copy.deepcopy(boss_entity), "station_rooms": copy.deepcopy(station_rooms),
        "vents": copy.deepcopy(vents), "terminals": copy.deepcopy(terminals),
        "cage_pos": copy.deepcopy(cage_pos), "red_hatch_pos": copy.deepcopy(red_hatch_pos),
    }
    red_grid, red_data = generate_red_map()
    cat_quest["red_map_data"] = red_data
    cat_quest["in_red_map"] = True
    game_map, enemies, chests = red_grid, [], []
    stairs_pos = dict(red_data["hatch_pos"])
    stairs_positions = [dict(stairs_pos)]
    merchant_state = {"x": -1, "y": -1}
    boss_entity = None
    player_state["x"], player_state["y"] = 1, 2
    init_fog()
    update_fog(1, 2)
    return {**build_status(), "success": True, "message": "Kırmızı Odaya indin", "logs": [{"type": "quest", "message": "🔻 Kırmızı Oda açıldı."}]}


@app.post("/api/exit-red-map")
async def exit_red_map():
    global game_map, enemies, chests, fog_matrix, stairs_pos, stairs_positions, merchant_state, boss_entity
    global station_rooms, vents, terminals, cage_pos
    require_class_selected()
    if not is_at_red_exit():
        raise HTTPException(400, detail="Kırmızı Oda çıkış merdiveninde değilsin")
    saved = cat_quest.get("saved_floor_state")
    if not saved:
        raise HTTPException(400, detail="Kat durumu bulunamadı")
    game_map, enemies, chests = saved["game_map"], saved["enemies"], saved["chests"]
    fog_matrix = saved["fog_matrix"]
    stairs_pos = saved["stairs_pos"]
    stairs_positions = saved.get("stairs_positions", [dict(stairs_pos)])
    merchant_state, boss_entity = saved["merchant_state"], saved["boss_entity"]
    station_rooms, vents = saved["station_rooms"], saved["vents"]
    terminals, cage_pos = saved["terminals"], saved["cage_pos"]
    player_state["x"], player_state["y"] = red_hatch_pos["x"], red_hatch_pos["y"]
    cat_quest["in_red_map"] = False
    if cat_quest.get("rescued"):
        cat_quest["cat_x"], cat_quest["cat_y"] = player_state["x"] - 1, player_state["y"]
        cat_state.update({"active": True, "rescued": True, "x": cat_quest["cat_x"], "y": cat_quest["cat_y"]})
    return {**build_status(), "success": True, "message": "3. kata döndün", "logs": [{"type": "quest", "message": "🔺 Kırmızı Odadan çıktın."}]}


def enter_secret_map(logs: list) -> None:
    global secret_map_index, game_map, boss_entity, current_floor, has_secret_key
    if secret_map_index >= SECRET_MAP_COUNT:
        return
    secret_map_index += 1
    has_secret_key = False
    current_floor = 1
    player_state["x"], player_state["y"] = 0, 0
    player_state["hp"] = min(player_state["max_hp"], player_state["hp"] + max(15, player_state["max_hp"] // 5))
    game_map = generate_bsp_map()
    boss_entity = None
    init_fog()
    spawn_chests()
    spawn_merchant()
    spawn_stairs()
    spawn_secret_route()
    spawn_enemies()
    setup_red_hatch()
    load_gravestones_for_floor()
    if secret_map_index >= SECRET_MAP_COUNT:
        spawn_boss()
        logs.append({"type": "combat", "message": "🏛️ FINAL HARİTA — Hazineyi koruyan Cyber-Dragon uyandı!"})
    else:
        logs.append({"type": "quest", "message": f"🚪 Gizli geçitten geçtin! Harita {secret_map_index}/5"})
    update_fog(0, 0)


def init_daily_quest(exclude_name: Optional[str] = None) -> None:
    global daily_quest
    candidates = [tmpl for tmpl in QUEST_TEMPLATES if tmpl["name"] != exclude_name]
    tmpl = random.choice(candidates or QUEST_TEMPLATES)
    daily_quest = {
        "type": tmpl["type"], "name": tmpl["name"],
        "target": tmpl["target"], "progress": 0,
        "reward": QUEST_REWARD, "completed": False,
    }


def get_daily_quest_status() -> dict:
    return dict(daily_quest)


def try_complete_quest(logs: list) -> bool:
    if daily_quest.get("completed") or daily_quest["progress"] < daily_quest["target"]:
        return False
    completed_name = daily_quest["name"]
    reward = daily_quest["reward"]
    daily_quest["completed"] = True
    player_state["gold"] += reward
    logs.append({"type": "quest", "message": f"Görev tamamlandı: {completed_name}! +{reward} Altın"})
    init_daily_quest(exclude_name=completed_name)
    logs.append({"type": "quest", "message": f"Yeni görev: {daily_quest['name']}"})
    return True


def on_enemy_killed(logs: list) -> None:
    if daily_quest.get("completed"): return
    if daily_quest.get("type") == "kill_enemies":
        daily_quest["progress"] += 1
        try_complete_quest(logs)


def on_gold_collected(amount: int, logs: list) -> None:
    if daily_quest.get("completed"): return
    if daily_quest.get("type") == "collect_gold":
        daily_quest["progress"] = min(daily_quest["target"], daily_quest["progress"] + amount)
        try_complete_quest(logs)


def on_chest_opened(logs: list) -> None:
    if daily_quest.get("completed"): return
    if daily_quest.get("type") == "open_chests":
        daily_quest["progress"] += 1
        try_complete_quest(logs)


def on_floor_reached(logs: list) -> None:
    if daily_quest.get("completed"): return
    if daily_quest.get("type") == "reach_floor":
        daily_quest["progress"] += 1
        try_complete_quest(logs)


def recalc_stats() -> None:
    cls = player_state["character_class"]
    if not cls:
        return
    base = CLASS_STATS[cls]
    atk = base["attack_power"]
    dfn = 0
    for slot_item in equipment.values():
        if slot_item:
            atk += slot_item.get("atk", 0)
            dfn += slot_item.get("def", 0)
    atk += (player_state["level"] - 1) * 2 + player_state["level_attack_bonus"]
    player_state["attack_power"] = atk
    player_state["damage_reduction"] = dfn + player_state["level_defense_bonus"]


def roll_item_drop() -> Optional[dict]:
    if random.random() > ITEM_DROP_CHANCE:
        return None
    keys = list(RARITY_DROP_WEIGHTS.keys())
    weights = [RARITY_DROP_WEIGHTS[k] for k in keys]
    rarity = random.choices(keys, weights=weights, k=1)[0]
    slot = random.choice(["weapon", "armor", "accessory"])
    pool = [i for i in ITEM_POOL[slot] if i["rarity"] == rarity]
    if not pool:
        pool = ITEM_POOL[slot]
    return dict(random.choice(pool))


def add_to_inventory(item: dict) -> bool:
    if len(inventory) >= MAX_INVENTORY:
        return False
    inventory.append(item)
    return True


def descend_floor(logs: list) -> None:
    global current_floor, game_map, next_enemy_id, boss_entity
    current_floor += 1
    player_state["stats"]["highest_floor"] = max(player_state["stats"].get("highest_floor", 1), current_floor)
    heal = max(10, player_state["max_hp"] // 5)
    player_state["hp"] = min(player_state["max_hp"], player_state["hp"] + heal)
    player_state["x"], player_state["y"] = 0, 0

    game_map = generate_bsp_map()
    boss_entity = None

    init_fog()
    spawn_chests()
    spawn_merchant()
    spawn_stairs()
    spawn_secret_route()
    spawn_enemies()
    load_gravestones_for_floor()

    if current_floor >= BOSS_FLOOR:
        spawn_boss()
        logs.append({"type": "combat", "message": f"⚠️ KAT {current_floor} — CYBER-DRAGON UYANDI! Son savaş başlıyor!"})
    else:
        logs.append({"type": "exp", "message": f"🔽 Kat {current_floor}/{MAX_FLOOR}'e indin! +{heal} HP iyileşti."})

    on_floor_reached(logs)
    update_fog(0, 0)


def init_game_with_class(cls: str) -> None:
    global game_map, game_over, game_won, boss_entity, next_enemy_id, character_class
    global class_selected, current_floor, equipment, inventory, secret_map_index, pending_level_ups, cat_quest, red_hatch_pos
    global station_rooms, vents, terminals, cage_pos, cat_state, red_key
    saved_progress = copy.deepcopy(player_state)
    saved_equipment = copy.deepcopy(equipment)
    saved_inventory = copy.deepcopy(inventory)
    character_class = cls
    class_selected = True
    current_floor = 1
    secret_map_index = 1
    game_won = False
    pending_level_ups = 0
    cat_quest = default_cat_quest()
    cat_state = {"active": False, "rescued": False, "x": -1, "y": -1, "trail": []}
    red_key = {"x": -1, "y": -1, "active": False}
    red_hatch_pos = {"x": -1, "y": -1}
    boss_entity = None
    equipment = saved_equipment
    inventory = saved_inventory

    game_map = generate_bsp_map()
    station_rooms, vents, terminals = [], [], []
    cage_pos = {"x": -1, "y": -1}
    spawn_x, spawn_y = find_safe_spawn(game_map)
    stats = CLASS_STATS[cls]
    player_state.update({
        "hp": stats["hp"], "max_hp": stats["max_hp"],
        "gold": max(stats["gold"], saved_progress.get("gold", 0)),
        "exp": saved_progress.get("exp", 0),
        "level": saved_progress.get("level", 1),
        "exp_to_next": saved_progress.get("exp_to_next", EXP_TO_LEVEL),
        "attack_power": stats["attack_power"],
        "damage_reduction": 0,
        "mp": stats["mp"], "max_mp": stats["max_mp"],
        "level_attack_bonus": saved_progress.get("level_attack_bonus", 0),
        "level_defense_bonus": saved_progress.get("level_defense_bonus", 0),
        "level_max_hp_bonus": saved_progress.get("level_max_hp_bonus", 0),
        "level_max_mp_bonus": saved_progress.get("level_max_mp_bonus", 0),
        "x": spawn_x, "y": spawn_y,
        "character_class": cls,
        "stats": copy.deepcopy(saved_progress.get(
            "stats", {"enemies_killed": 0, "total_gold_earned": 0, "highest_floor": 1, "games_won": 0})),
    })
    recalc_stats()
    game_over = False
    init_daily_quest()
    init_fog()
    spawn_chests()
    spawn_merchant()
    spawn_stairs()
    spawn_secret_route()
    spawn_enemies()
    load_gravestones_for_floor()
    update_fog(0, 0)


def apply_exp(amount: int) -> dict:
    global pending_level_ups
    player_state["exp"] += amount
    leveled_up = False
    new_level = None
    while player_state["exp"] >= player_state["exp_to_next"]:
        player_state["exp"] -= player_state["exp_to_next"]
        player_state["level"] += 1
        player_state["max_hp"] += 20
        player_state["hp"] = player_state["max_hp"]
        player_state["exp_to_next"] = int(player_state["exp_to_next"] * 1.5)
        pending_level_ups += 1
        leveled_up = True
        new_level = player_state["level"]
    if leveled_up:
        recalc_stats()
    return {"leveled_up": leveled_up, "new_level": new_level}


def require_level_choice() -> None:
    if pending_level_ups:
        raise HTTPException(409, detail="Seviye ödülünü seçmelisin")


def check_game_over(cause: str = "Bilinmeyen düşman") -> None:
    global game_over
    if player_state["hp"] <= 0 and not game_over:
        player_state["hp"] = 0
        game_over = True
        restore_floor_after_red_map_death()
        record_gravestone(cause)


def regen_mp_safe() -> None:
    player_state["mp"] = min(player_state["max_mp"], player_state["mp"] + MP_REGEN_SAFE)


def apply_enemy_kill_rewards(enemy: dict, logs: list) -> dict:
    gold_gain = enemy.get("gold", ENEMY_KILL_GOLD)
    exp_gain  = enemy.get("exp",  ENEMY_KILL_EXP)
    player_state["gold"] += gold_gain
    player_state["stats"]["enemies_killed"] += 1
    player_state["stats"]["total_gold_earned"] += gold_gain
    apply_exp(exp_gain)
    enemies[:] = [e for e in enemies if e["id"] != enemy["id"]]
    logs.append({"type": "gold", "message": f"{enemy['name']} yenildi! +{gold_gain} GOLD +{exp_gain} EXP"})
    on_enemy_killed(logs)
    on_gold_collected(gold_gain, logs)
    dropped = roll_item_drop()
    if dropped:
        added = add_to_inventory(dropped)
        if added:
            logs.append({"type": "item", "message": f"💎 Eşya düştü: {dropped['name']} ({dropped['rarity']})"})
        else:
            logs.append({"type": "info", "message": "Envanter dolu! Eşya kayboldu."})
    return {"gold_gained": gold_gain, "exp_gained": exp_gain, "item_drop": dropped}


def calc_enemy_damage(enemy: dict) -> int:
    return max(1, enemy["damage"] - player_state["damage_reduction"])


def invisibility_active() -> bool:
    return player_state.get("invisible_until", 0) > datetime.now(timezone.utc).timestamp()


def resolve_combat(enemy: dict, logs: list) -> dict:
    atk = player_state["attack_power"]
    enemy["hp"] -= atk
    logs.append({"type": "combat", "message": f"{enemy['name']}'e {atk} hasar vurdun!"})
    result = {
        "enemy_id": enemy["id"], "enemy_name": enemy["name"],
        "enemy_x": enemy["x"],   "enemy_y": enemy["y"],
        "enemy_killed": False, "gold_gained": 0, "exp_gained": 0,
        "damage_dealt": atk, "item_drop": None,
    }
    if enemy["hp"] <= 0:
        result["enemy_killed"] = True
        rewards = apply_enemy_kill_rewards(enemy, logs)
        result.update({"gold_gained": rewards["gold_gained"],
                       "exp_gained":  rewards["exp_gained"],
                       "item_drop":   rewards["item_drop"]})
    else:
        dmg = calc_enemy_damage(enemy)
        player_state["hp"] = max(0, player_state["hp"] - dmg)
        logs.append({"type": "combat", "message": f"{enemy['name']} sana {dmg} hasar vurdu!"})
        check_game_over(enemy["name"])
    return result


def collect_chest(logs: list) -> None:
    for c in chests:
        if not c["active"]: continue
        if player_state["x"] != c["x"] or player_state["y"] != c["y"]: continue
        c["active"] = False
        player_state["gold"] += CHEST_GOLD
        player_state["stats"]["total_gold_earned"] += CHEST_GOLD
        apply_exp(CHEST_EXP)
        logs.append({"type": "gold", "message": f"Hazine buldun! +{CHEST_GOLD} GOLD +{CHEST_EXP} EXP"})
        if daily_quest.get("type") == "collect_gold":
            on_gold_collected(CHEST_GOLD, logs)
        elif daily_quest.get("type") == "open_chests":
            on_chest_opened(logs)
        break


def collect_gravestone(logs: list) -> Optional[dict]:
    global gravestones
    for stone in gravestones:
        if (player_state["x"], player_state["y"]) != (stone["x"], stone["y"]):
            continue
        with db_connect() as connection:
            updated = connection.execute(
                "UPDATE gravestones SET is_looted = 1 WHERE id = ? AND is_looted = 0",
                (stone["id"],),
            ).rowcount
        if not updated:
            return None
        player_state["gold"] += stone["gold"]
        player_state["stats"]["total_gold_earned"] += stone["gold"]
        logs.append({
            "type": "gold",
            "message": f"🪦 {stone['username']} burada {stone['cause']} tarafından katledildi! "
                       f"Kalıntıları topladın: +{stone['gold']} Altın",
        })
        gravestones = [candidate for candidate in gravestones if candidate["id"] != stone["id"]]
        return {"x": stone["x"], "y": stone["y"], "gold": stone["gold"]}
    return None


def move_enemies(logs: list) -> list:
    battles = []
    if game_over:
        return battles

    px, py = player_state["x"], player_state["y"]
    invisible = invisibility_active()
    shuffled = enemies[:]
    random.shuffle(shuffled)

    for enemy in shuffled:
        if game_over:
            break

        if enemy.get("move_speed", 1) > 1:
            enemy["move_timer"] = enemy.get("move_timer", 0) + 1
            if enemy["move_timer"] % enemy["move_speed"] != 0:
                continue
        
        if secret_map_index >= SECRET_MAP_COUNT and not game_over and not game_won:
            step_damage = 5
            player_state["hp"] = max(0, player_state["hp"] - step_damage)
            logs.append({"type": "combat", "message": f"🌋 5. haritada adım attığın için {step_damage} hasar aldın!"})
            check_game_over("5. Harita Zorluğu")

        old_x, old_y = enemy["x"], enemy["y"]
        occupied = get_occupied_cells(exclude_enemy_id=enemy["id"])
        dist = tile_distance(enemy["x"], enemy["y"], px, py)
        is_visible = is_tile_visible(enemy["x"], enemy["y"])

        if enemy["name"] == "Poison Zombie" and not invisible and is_visible and dist <= enemy["range"]:
            now = time.time()
            if now - float(enemy.get("last_throw", 0.0)) >= 2.0:
                enemy["last_throw"] = now
                dmg = max(1, 4 - player_state["damage_reduction"])
                player_state["hp"] = max(0, player_state["hp"] - dmg)
                logs.append({"type": "combat", "message": f"🧪 Zombi zehir şişesi fırlattı! ({dmg} hasar, başın dönüyor...)"})
                check_game_over(enemy["name"])
                battles.append({
                    "enemy_id": enemy["id"], "enemy_name": enemy["name"],
                    "enemy_x": enemy["x"], "enemy_y": enemy["y"],
                    "enemy_killed": False, "potion_throw": True, "dizzy": True,
                    "damage_dealt": dmg, "gold_gained": 0, "exp_gained": 0,
                })
                continue

        if not invisible and enemy.get("range", 1) >= 3 and dist <= enemy["range"] and is_visible:
            dmg = calc_enemy_damage(enemy)
            player_state["hp"] = max(0, player_state["hp"] - dmg)
            logs.append({"type": "combat", "message": f"🏹 {enemy['name']} sana {dmg} ok attı!"})
            check_game_over(enemy["name"])
            battles.append({
                "enemy_id": enemy["id"], "enemy_name": enemy["name"],
                "enemy_x": enemy["x"],   "enemy_y": enemy["y"],
                "enemy_killed": False, "ranged": True,
                "damage_dealt": 0, "gold_gained": 0, "exp_gained": 0,
            })
            continue

        if not invisible and is_visible and dist <= 8:
            step = astar((old_x, old_y), (px, py), occupied)
        else:
            dirs = list(DIR_DELTA.values())
            random.shuffle(dirs)
            step = None
            for dx, dy in dirs:
                nx2, ny2 = old_x + dx, old_y + dy
                if not is_in_bounds(nx2, ny2) or game_map[ny2][nx2] == WALL:
                    continue
                if (nx2, ny2) in occupied:
                    continue
                step = (nx2, ny2)
                break

        if step is None:
            continue

        nx, ny = step
        if (nx, ny) == (px, py) and not invisible:
            battle = resolve_combat(enemy, logs)
            battles.append(battle)
            if not battle["enemy_killed"]:
                enemy["x"], enemy["y"] = old_x, old_y
        elif (nx, ny) == (px, py):
            continue
        else:
            enemy["x"], enemy["y"] = nx, ny

    return battles


def move_boss(logs: list) -> list:
    global boss_entity, game_won
    battles = []
    if boss_entity is None or game_over or invisibility_active():
        return battles

    px, py = player_state["x"], player_state["y"]
    boss_entity["aoe_timer"] = boss_entity.get("aoe_timer", 0) + 1

    if boss_entity["aoe_timer"] >= BOSS_AOE_INTERVAL:
        boss_entity["aoe_timer"] = 0
        aoe_dmg = max(1, boss_entity["damage"] // 2 - player_state["damage_reduction"])
        player_state["hp"] = max(0, player_state["hp"] - aoe_dmg)
        check_game_over("Cyber-Dragon")
        logs.append({"type": "combat", "message": f"🔥 Cyber-Dragon'un NEON ALEVI! {aoe_dmg} AoE hasar!"})
        battles.append({
            "enemy_id": 9999, "enemy_name": "Cyber-Dragon",
            "enemy_x": boss_entity["x"], "enemy_y": boss_entity["y"],
            "enemy_killed": False, "aoe": True,
            "aoe_radius": 1, "aoe_cx": px, "aoe_cy": py,
            "damage_dealt": aoe_dmg, "gold_gained": 0, "exp_gained": 0,
        })
        return battles

    old_x, old_y = boss_entity["x"], boss_entity["y"]
    occupied = get_occupied_cells()
    dist = tile_distance(old_x, old_y, px, py)
    step = astar((old_x, old_y), (px, py), occupied) if dist <= 15 else None

    if step is None:
        return battles

    nx, ny = step
    if (nx, ny) == (px, py):
        raw_dmg = boss_entity["damage"]
        dmg = max(1, raw_dmg - player_state["damage_reduction"])
        player_state["hp"] = max(0, player_state["hp"] - dmg)
        check_game_over("Cyber-Dragon")
        logs.append({"type": "combat", "message": f"Cyber-Dragon sana {dmg} hasar vurdu!"})
        battles.append({
            "enemy_id": 9999, "enemy_name": "Cyber-Dragon",
            "enemy_x": old_x, "enemy_y": old_y,
            "enemy_killed": False, "damage_dealt": 0,
            "gold_gained": 0, "exp_gained": 0,
        })
    else:
        boss_entity["x"], boss_entity["y"] = nx, ny

    return battles


def attack_boss(atk: int, logs: list) -> dict:
    global boss_entity, game_won
    effective_atk = max(1, atk - boss_entity.get("defense", 0))
    boss_entity["hp"] -= effective_atk
    logs.append({"type": "combat", "message": f"Cyber-Dragon'a {effective_atk} hasar vurdun! (HP: {max(0,boss_entity['hp'])}/{boss_entity['max_hp']})"})
    if boss_entity["hp"] <= 0:
        boss_entity["hp"] = 0
        game_won = True
        player_state["gold"] += boss_entity["gold"]
        player_state["stats"]["total_gold_earned"] += boss_entity["gold"]
        player_state["stats"]["games_won"] += 1
        apply_exp(boss_entity["exp"])
        logs.append({"type": "quest", "message": "CYBER-DRAGON YENİLDİ! Zindan fethedildi! ZAFER!"})
        return {"enemy_killed": True, "gold_gained": boss_entity["gold"],
                "exp_gained": boss_entity["exp"], "game_won": True,
                "enemy_id": 9999, "enemy_name": "Cyber-Dragon",
                "enemy_x": boss_entity["x"], "enemy_y": boss_entity["y"],
                "damage_dealt": effective_atk}
    return {"enemy_killed": False, "gold_gained": 0, "exp_gained": 0,
            "game_won": False, "enemy_id": 9999, "enemy_name": "Cyber-Dragon",
            "enemy_x": boss_entity["x"], "enemy_y": boss_entity["y"],
            "damage_dealt": effective_atk}


def cat_attack_boss(logs: list) -> Optional[dict]:
    global boss_entity, game_won
    if (boss_entity is None or game_won or secret_map_index < SECRET_MAP_COUNT
            or not cat_quest.get("rescued")
            or not is_tile_visible(boss_entity["x"], boss_entity["y"])):
        return None

    cat_damage = 300
    boss_entity["hp"] -= cat_damage
    logs.append({"type": "combat", "message": f"🐾 Siber Kedi boss'a saldırdı! -{cat_damage} HP"})
    if boss_entity["hp"] <= 0:
        boss_entity["hp"] = 0
        game_won = True
        player_state["gold"] += boss_entity["gold"]
        player_state["stats"]["total_gold_earned"] += boss_entity["gold"]
        player_state["stats"]["games_won"] += 1
        apply_exp(boss_entity["exp"])
        logs.append({"type": "quest", "message": "Siber Kedi'nin saldırısıyla CYBER-DRAGON yenildi! ZAFER!"})

    return {
        "cat_attack": True, "enemy_id": 9999,
        "enemy_name": "Cyber-Dragon", "enemy_x": boss_entity["x"],
        "enemy_y": boss_entity["y"], "damage_dealt": cat_damage,
        "enemy_killed": boss_entity["hp"] <= 0, "game_won": game_won,
        "gold_gained": boss_entity["gold"] if game_won else 0,
        "exp_gained": boss_entity["exp"] if game_won else 0,
    }


def build_status() -> dict:
    base = {
        "class_selected": class_selected,
        "character_class": character_class,
        "grid_size": GRID_SIZE,
        "grid_width": len(game_map[0]) if game_map else GRID_SIZE,
        "grid_height": len(game_map) if game_map else GRID_SIZE,
        "floor": current_floor,
        "secret_map": secret_map_index,
        "theme": "red" if cat_quest.get("in_red_map") else "station",
        "in_red_map": cat_quest.get("in_red_map", False),
        "cat_quest": cat_quest,
        "red_hatch_pos": dict(red_hatch_pos),
        "can_enter_red_map": is_at_red_hatch(),
        "can_exit_red_map": is_at_red_exit(),
    }
    if not class_selected:
        return {
            **base,
            "hp": 0, "max_hp": 0, "mp": 0, "max_mp": 0,
            "gold": 0, "exp": 0, "level": 1,
            "invisible": False, "invisible_until": 0,
            "exp_to_next": EXP_TO_LEVEL,
            "attack_power": 0, "damage_reduction": 0,
            "x": 0, "y": 0,
            "map": [], "fog_matrix": [],
            "enemies": [], "chests": [], "gravestones": [],
            "merchant": {"x": 0, "y": 0, "visible": False},
            "stairs": {"x": -1, "y": -1}, "stairs_positions": [],
            "station_rooms": [], "vents": [], "terminals": [], "cage_pos": {"x": -1, "y": -1},
            "red_key": {"x": -1, "y": -1, "active": False},
            "cat_state": {"active": False, "rescued": False, "x": -1, "y": -1, "trail": []},
            "cat_quest": default_cat_quest(), "red_hatch_pos": {"x": -1, "y": -1},
            "can_enter_red_map": False, "can_exit_red_map": False, "theme": "station", "in_red_map": False,
            "secret_key": {"x": -1, "y": -1, "active": False},
            "secret_door": {"x": -1, "y": -1, "open": False},
            "at_merchant": False, "at_stairs": False,
            "game_over": False,
            "pending_level_ups": 0, "level_up_choices": LEVEL_UP_CHOICES,
            "daily_quest": get_daily_quest_status() if daily_quest else {},
            "inventory": [], "equipment": equipment,
            "authenticated": bool(current_user_id),
            "username": get_username(current_user_id) if current_user_id else None,
            "achievements": account_achievements(),
        }
    return {
        **base,
        "hp": player_state["hp"], "max_hp": player_state["max_hp"],
        "mp": player_state["mp"], "max_mp": player_state["max_mp"],
        "gold": player_state["gold"], "exp": player_state["exp"],
        "invisible": invisibility_active(),
        "invisible_until": player_state.get("invisible_until", 0),
        "level": player_state["level"],
        "exp_to_next": player_state["exp_to_next"],
        "attack_power": player_state["attack_power"],
        "damage_reduction": player_state["damage_reduction"],
        "x": player_state["x"], "y": player_state["y"],
        "map": game_map,
        "fog_matrix": [row[:] for row in fog_matrix],
        "enemies": get_visible_enemies(),
        "chests": get_visible_chests(),
        "gravestones": [
            {"id": stone["id"], "x": stone["x"], "y": stone["y"],
             "username": stone["username"], "cause": stone["cause"], "gold": stone["gold"]}
            for stone in gravestones
        ],
        "merchant": get_visible_merchant(),
        "stairs": dict(stairs_pos), "stairs_positions": [dict(stair) for stair in stairs_positions],
        "station_rooms": station_rooms,
        "vents": list(vents),
        "terminals": list(terminals),
        "cage_pos": dict(cage_pos),
        "red_key": dict(red_key),
        "cat_state": dict(cat_state),
        "cat_quest": cat_quest,
        "red_hatch_pos": dict(red_hatch_pos),
        "theme": "red" if cat_quest.get("in_red_map") else "station",
        "in_red_map": cat_quest.get("in_red_map", False),
        "can_enter_red_map": is_at_red_hatch(),
        "can_exit_red_map": is_at_red_exit(),
        "secret_key": dict(secret_key),
        "secret_door": dict(secret_door),
        "has_secret_key": has_secret_key,
        "at_merchant": is_at_merchant(),
        "at_stairs": is_at_stairs(),
        "game_over": game_over,
        "game_won": game_won,
        "pending_level_ups": pending_level_ups,
        "level_up_choices": LEVEL_UP_CHOICES,
        "max_floor": MAX_FLOOR,
        "boss": dict(boss_entity) if boss_entity else None,
        "daily_quest": get_daily_quest_status(),
        "inventory": [dict(i) for i in inventory],
        "equipment": {k: dict(v) if v else None for k, v in equipment.items()},
        "authenticated": bool(current_user_id),
        "username": get_username(current_user_id) if current_user_id else None,
        "achievements": account_achievements(),
    }


def require_class_selected():
    if not class_selected:
        raise HTTPException(400, detail="Önce karakter sınıfı seçin")


@app.on_event("startup")
async def on_startup():
    init_database()
    backup_database()
    sync_registered_accounts_to_log()
    clear_runtime_state()


@app.get("/")
@app.get("/index.html")
async def serve_index():
    return FileResponse(BASE_DIR / "index.html")

@app.get("/icon.svg")
async def serve_icon():
    return FileResponse(BASE_DIR / "icon.svg", media_type="image/svg+xml")

@app.get("/icon.png")
async def serve_icon_png():
    return FileResponse(BASE_DIR / "icon.png")

@app.get("/knight_sheet.png")
async def get_knight_sheet():
    return FileResponse(BASE_DIR / "knight_sheet.png")

@app.get("/monters.png")
async def get_monsters():
    return FileResponse(BASE_DIR / "monters.png")

@app.get("/kedi.png")
async def get_cat_sprite():
    return FileResponse(BASE_DIR / "kedi.png", media_type="image/png")


def get_username(user_id: Optional[int]) -> Optional[str]:
    if not user_id:
        return None
    with db_connect() as connection:
        row = connection.execute("SELECT username FROM users WHERE id = ?", (user_id,)).fetchone()
    return row["username"] if row else None


def load_gravestones_for_floor() -> None:
    global gravestones
    with db_connect() as connection:
        rows = connection.execute(
            "SELECT id, username, floor, x, y, cause, gold FROM gravestones "
            "WHERE floor = ? AND is_looted = 0 ORDER BY id",
            (current_floor,),
        ).fetchall()
    gravestones = [dict(row) for row in rows]


def record_gravestone(cause: str) -> None:
    if not current_user_id:
        return
    username = get_username(current_user_id) or "Bilinmeyen oyuncu"
    lost_gold = max(15, int(player_state.get("gold", 0) * 0.2))
    created_at = datetime.now(timezone.utc).isoformat()
    with db_connect() as connection:
        cursor = connection.execute(
            "INSERT INTO gravestones(username, floor, x, y, cause, gold, created_at) "
            "VALUES (?, ?, ?, ?, ?, ?, ?)",
            (username, current_floor, player_state["x"], player_state["y"], cause, lost_gold, created_at),
        )
    gravestones.append({
        "id": cursor.lastrowid, "username": username, "floor": current_floor,
        "x": player_state["x"], "y": player_state["y"], "cause": cause, "gold": lost_gold,
    })


@app.post("/api/auth/register")
async def register(payload: AuthRequest, request: Request, response: Response):
    created_at = datetime.now(timezone.utc).isoformat()
    try:
        with db_connect() as connection:
            cursor = connection.execute(
                "INSERT INTO users(username, password_hash, created_at) VALUES (?, ?, ?)",
                (payload.username, hash_password(payload.password), created_at),
            )
            user_id = cursor.lastrowid
            connection.execute(
                "INSERT INTO profiles(user_id, state_json, achievements_json) VALUES (?, ?, ?)",
                (user_id, json.dumps({}), json.dumps([])),
            )
    except sqlite3.IntegrityError:
        raise HTTPException(409, detail="Bu kullanici adi zaten alinmis")
    record_auth_event(payload.username, "register", user_id)
    append_account_log("register", payload.username, created_at)
    append_user_log("KAYIT", payload.username, request)
    load_game_state(user_id)
    token = create_session(user_id, response)
    return {**build_status(), "success": True, "message": "Hesap olusturuldu", "session_token": token}


@app.post("/api/auth/login")
async def login(payload: AuthRequest, request: Request, response: Response):
    with db_connect() as connection:
        row = connection.execute("SELECT id, password_hash FROM users WHERE username = ?", (payload.username,)).fetchone()
    if not row or not verify_password(payload.password, row["password_hash"]):
        record_auth_event(payload.username, "login_failed", int(row["id"]) if row else None)
        append_account_log("login_failed", payload.username)
        append_user_log("GIRIS_BASARISIZ", payload.username, request)
        raise HTTPException(401, detail="Kullanici adi veya parola hatali")
    user_id = int(row["id"])
    record_auth_event(payload.username, "login_success", user_id)
    append_account_log("login_success", payload.username)
    append_user_log("GIRIS", payload.username, request)
    load_game_state(user_id)
    token = create_session(user_id, response)
    return {**build_status(), "success": True, "message": "Giris yapildi", "session_token": token}


@app.post("/api/log-user")
async def log_user_activity(payload: UserLogPayload, request: Request):
    append_user_log(payload.action, payload.username, request)
    return {"status": "success"}


@app.get("/view-logs")
async def view_logs():
    if not USER_LOG_PATH.exists():
        return PlainTextResponse("Henüz kaydedilmiş kullanıcı girişi veya kaydı bulunmuyor.")
    return FileResponse(USER_LOG_PATH, media_type="text/plain; charset=utf-8")


def require_admin_log_key(request: Request) -> None:
    expected = os.getenv(ADMIN_LOG_KEY_ENV)
    provided = request.headers.get("x-admin-key", "")
    if not expected:
        raise HTTPException(503, detail="Admin log anahtari yapılandırılmamış")
    if not provided or not secrets.compare_digest(provided, expected):
        raise HTTPException(403, detail="Admin yetkisi gerekiyor")


@app.get("/api/admin/account-log")
async def account_log(request: Request):
    require_admin_log_key(request)
    with db_connect() as connection:
        users = connection.execute(
            "SELECT username, created_at, last_login_at, failed_login_attempts, is_active "
            "FROM users ORDER BY created_at DESC"
        ).fetchall()
        events = connection.execute(
            "SELECT username, event_type, created_at FROM auth_events "
            "ORDER BY id DESC LIMIT 100"
        ).fetchall()
    return {
        "accounts": [
            {
                "username": row["username"],
                "created_at": row["created_at"],
                "last_login_at": row["last_login_at"],
                "failed_login_attempts": row["failed_login_attempts"],
                "status": "active" if row["is_active"] else "disabled",
            }
            for row in users
        ],
        "events": [dict(row) for row in events],
        "passwords_included": False,
    }


@app.post("/api/auth/logout")
async def logout(request: Request, response: Response):
    token = request.cookies.get(SESSION_COOKIE)
    if token:
        with db_connect() as connection:
            connection.execute("DELETE FROM sessions WHERE token = ?", (token,))
    response.delete_cookie(SESSION_COOKIE, path="/")
    clear_runtime_state()
    return {"success": True}


@app.get("/api/status")
async def get_status():
    return build_status()


@app.get("/api/map")
async def get_map():
    if not class_selected:
        return {
            "class_selected": False, "grid_size": GRID_SIZE,
            "map": [], "fog_matrix": [], "enemies": [], "chests": [],
            "merchant": {"x": 0, "y": 0, "visible": False},
            "stairs": {"x": -1, "y": -1}, "stairs_positions": [],
            "station_rooms": [], "vents": [], "terminals": [], "cage_pos": {"x": -1, "y": -1},
            "red_key": {"x": -1, "y": -1, "active": False},
            "cat_state": {"active": False, "rescued": False, "x": -1, "y": -1, "trail": []},
            "x": 0, "y": 0,
        }
    return {
        "class_selected": True, "grid_size": GRID_SIZE,
        "map": game_map,
        "fog_matrix": [row[:] for row in fog_matrix],
        "enemies": get_visible_enemies(),
        "chests": get_visible_chests(),
        "merchant": get_visible_merchant(),
        "stairs": dict(stairs_pos), "stairs_positions": [dict(stair) for stair in stairs_positions],
        "station_rooms": list(station_rooms),
        "vents": list(vents),
        "terminals": list(terminals),
        "cage_pos": dict(cage_pos),
        "red_key": dict(red_key),
        "cat_state": dict(cat_state),
        "x": player_state["x"], "y": player_state["y"],
    }


@app.post("/api/use-vent")
async def use_vent():
    require_class_selected()
    if not vents:
        raise HTTPException(400, detail="Haritada vent yok")

    current = next((vent for vent in vents if vent["x"] == player_state["x"] and vent["y"] == player_state["y"]), None)
    if current is None:
        raise HTTPException(400, detail="Oyuncu vent üzerinde değil")

    ordered = sorted(vents, key=lambda item: item["id"])
    dest = next((vent for vent in ordered if vent["id"] > current["id"]), ordered[0])
    if dest["x"] == current["x"] and dest["y"] == current["y"]:
        dest = ordered[0]

    player_state["x"] = dest["x"]
    player_state["y"] = dest["y"]
    update_fog(player_state["x"], player_state["y"])

    logs = [{"type": "info", "message": "💨 Havalandırma ızgarasından diğer odaya süzüldün!"}]
    return {**build_status(), "success": True, "message": "Vent kullanıldı", "logs": logs}


@app.post("/api/use-stairs")
async def use_stairs():
    require_class_selected()
    if cat_quest.get("in_red_map") or not stairs_positions:
        raise HTTPException(400, detail="Bu haritada kullanılabilir merdiven yok")
    current_index = next((index for index, stair in enumerate(stairs_positions)
                          if (stair["x"], stair["y"]) == (player_state["x"], player_state["y"])), None)
    if current_index is None:
        raise HTTPException(400, detail="Merdivenin üzerinde değilsin")

    next_index = (current_index + 1) % len(stairs_positions)
    destination = stairs_positions[next_index]
    logs = []
    player_state["x"], player_state["y"] = destination["x"], destination["y"]
    update_fog(player_state["x"], player_state["y"])
    logs.append({"type": "info", "message": f"Merdiven {next_index + 1}'e ışınlandın!"})
    return {**build_status(), "success": True, "message": "Merdiven kullanıldı",
            "logs": logs, "floor_changed": False}


@app.post("/api/select-class")
async def select_class(payload: SelectClassRequest):
    if payload.character_class not in CLASS_STATS:
        raise HTTPException(400, detail="Geçersiz sınıf")
    init_game_with_class(payload.character_class)
    return build_status()


@app.post("/api/select-level-up")
async def select_level_up(payload: LevelUpRequest):
    global pending_level_ups
    require_class_selected()
    if not pending_level_ups:
        raise HTTPException(400, detail="Bekleyen seviye ödülü yok")

    if payload.choice == "power":
        player_state["level_attack_bonus"] += 5
        reward = LEVEL_UP_CHOICES["power"]
    elif payload.choice == "vitality":
        player_state["level_max_hp_bonus"] += 30
        player_state["max_hp"] += 30
        player_state["hp"] += 30
        reward = LEVEL_UP_CHOICES["vitality"]
    else:
        player_state["level_max_mp_bonus"] += 15
        player_state["max_mp"] += 15
        player_state["mp"] += 15
        reward = LEVEL_UP_CHOICES["focus"]

    pending_level_ups -= 1
    recalc_stats()
    return {**build_status(), "success": True, "reward": reward}


@app.post("/api/move")
async def move_player(payload: MoveRequest):
    global game_over
    require_class_selected()
    require_level_choice()
    if game_over:
        raise HTTPException(400, detail="Oyun bitti")

    logs: list = []
    battles: list = []
    gravestone_collected = None
    floor_changed = False
    secret_map_changed = False
    spawner_damage = 0
    blocked = False

    dx, dy = DIR_DELTA[payload.direction]
    old_x, old_y = player_state["x"], player_state["y"]
    if not is_in_bounds(old_x, old_y) or game_map[old_y][old_x] == WALL:
        old_x, old_y = find_safe_spawn(game_map)
        player_state["x"], player_state["y"] = old_x, old_y
    new_x, new_y = old_x + dx, old_y + dy

    if not is_in_bounds(new_x, new_y) or game_map[new_y][new_x] == WALL:
        blocked = True
        logs.append({"type": "info", "message": "Duvara çarptın!"})
    elif game_map[new_y][new_x] == SECRET_DOOR and not has_secret_key:
        blocked = True
        logs.append({"type": "info", "message": "Gizli geçit kilitli. Anahtarı bulmalısın!"})
    else:
        if boss_entity and (new_x, new_y) == (boss_entity["x"], boss_entity["y"]):
            battle = attack_boss(player_state["attack_power"], logs)
            battles.append(battle)
            if not battle["enemy_killed"]:
                battles += move_boss(logs)
        else:
            target_enemy = find_enemy_at(new_x, new_y)
            if target_enemy:
                battle = resolve_combat(target_enemy, logs)
                battles.append(battle)
                if battle["enemy_killed"]:
                    player_state["x"], player_state["y"] = new_x, new_y
            else:
                player_state["x"], player_state["y"] = new_x, new_y

        if not game_over and not game_won:
            collect_chest(logs)
            gravestone_collected = collect_gravestone(logs)
            collect_secret_key(logs)
            collect_red_key(logs)

        if not game_over and not game_won and not blocked:
            battles += move_enemies(logs)
            if boss_entity and not game_won:
                battles += move_boss(logs)
            if cat_quest.get("rescued"):
                update_cat_follow_history()
            if cat_state.get("rescued") and not cat_quest.get("rescued"):
                update_cat_follow()

        if (cat_quest.get("in_red_map") and is_in_bounds(player_state["x"], player_state["y"])
                and game_map[player_state["y"]][player_state["x"]] == LASER_CAGE):
            spawner_damage = 1
            player_state["hp"] = max(0, player_state["hp"] - spawner_damage)
            logs.append({"type": "combat", "message": "🔥 Spawner'ın üstündesin! -1 HP"})
            check_game_over("Siber Spawner")

        update_fog(player_state["x"], player_state["y"])

        if not game_over and not game_won and has_secret_key and is_at_secret_door():
            enter_secret_map(logs)
            secret_map_changed = True

        cat_battle = cat_attack_boss(logs)
        if cat_battle:
            battles.append(cat_battle)

        if not battles:
            regen_mp_safe()

    if game_over:
        logs.append({"type": "combat", "message": "GAME OVER — Şövalyen düştü!"})

    return {
        **build_status(),
        "logs": logs, "battles": battles,
        "gravestone_collected": gravestone_collected,
        "spawner_damage": spawner_damage,
        "blocked": blocked, "floor_changed": floor_changed,
        "secret_map_changed": secret_map_changed,
        "combat_occurred": len(battles) > 0,
        "game_won": game_won,
    }


@app.post("/api/buy-item")
async def buy_item(payload: BuyItemRequest):
    require_class_selected()
    require_level_choice()
    if game_over:
        raise HTTPException(400, detail="Oyun bitti")
    if not is_at_merchant():
        raise HTTPException(400, detail="Tüccarın yanında değilsin")
    if payload.item not in SHOP_ITEMS:
        raise HTTPException(400, detail="Geçersiz eşya")
    cost = SHOP_ITEMS[payload.item]["cost"]
    if player_state["gold"] < cost:
        raise HTTPException(400, detail="Yetersiz altın")
    if payload.item == "invisibility_potion" and len(inventory) >= MAX_INVENTORY:
        raise HTTPException(400, detail="Envanter dolu")

    player_state["gold"] -= cost
    message = ""
    if payload.item == "potion":
        gained = min(player_state["max_hp"], player_state["hp"] + 30) - player_state["hp"]
        player_state["hp"] += gained
        message = f"Can İksiri! +{gained} HP"
    elif payload.item == "mana_potion":
        gained = min(player_state["max_mp"], player_state["mp"] + 40) - player_state["mp"]
        player_state["mp"] += gained
        message = f"Mana İksiri! +{gained} MP"
    elif payload.item == "sword_upgrade":
        player_state["attack_power"] += 5
        message = f"Kılıç güçlendi! ATK: {player_state['attack_power']}"
    elif payload.item == "bless_sword":
        player_state["attack_power"] += 500
        message = f"Bless Kılıç kuşanıldı! ATK: {player_state['attack_power']}"
    elif payload.item == "armor_upgrade":
        player_state["damage_reduction"] += 3
        message = f"Zırh güçlendi! DEF: -{player_state['damage_reduction']}"
    elif payload.item == "invisibility_potion":
        inventory.append({
            "id": "invisibility_potion",
            "name": SHOP_ITEMS[payload.item]["label"],
            "type": "consumable",
        })
        message = "Görünmezlik İksiri envantere eklendi."

    return {**build_status(), "success": True, "message": message,
            "logs": [{"type": "gold", "message": message}]}


@app.post("/api/cast-fireball")
async def cast_fireball(payload: FireballRequest):
    require_class_selected()
    require_level_choice()
    if game_over: raise HTTPException(400, detail="Oyun bitti")
    if player_state["mp"] < FIREBALL_COST:
        raise HTTPException(400, detail="Yetersiz mana")

    enemy = find_enemy_by_id(payload.enemy_id)
    if not enemy: raise HTTPException(400, detail="Düşman bulunamadı")
    if tile_distance(player_state["x"], player_state["y"], enemy["x"], enemy["y"]) > FIREBALL_RANGE:
        raise HTTPException(400, detail="Düşman menzil dışında")
    if not is_tile_visible(enemy["x"], enemy["y"]):
        raise HTTPException(400, detail="Düşman görüş alanında değil")

    logs: list = []
    player_state["mp"] -= FIREBALL_COST
    enemy["hp"] -= FIREBALL_DAMAGE
    logs.append({"type": "magic", "message": f"🔥 Alev Topu! {enemy['name']}'e {FIREBALL_DAMAGE} hasar (-{FIREBALL_COST} MP)"})

    enemy_killed = enemy["hp"] <= 0
    item_drop = None
    if enemy_killed:
        rewards = apply_enemy_kill_rewards(enemy, logs)
        item_drop = rewards.get("item_drop")

    return {**build_status(), "logs": logs,
            "enemy_killed": enemy_killed, "item_drop": item_drop, "success": True}


@app.post("/api/equip")
async def equip_item(payload: EquipRequest):
    require_class_selected()
    if payload.item_index < 0 or payload.item_index >= len(inventory):
        raise HTTPException(400, detail="Geçersiz envanter indeksi")

    item = inventory[payload.item_index]
    slot = item.get("slot")
    if slot not in equipment:
        raise HTTPException(400, detail="Bu eşya donanılamaz")

    if equipment[slot]:
        inventory.append(equipment[slot])

    equipment[slot] = item
    inventory.pop(payload.item_index)
    recalc_stats()
    return {**build_status(), "success": True, "message": f"{item['name']} donanıldı! ({slot})"}


@app.post("/api/use-item")
async def use_item(payload: UseItemRequest):
    require_class_selected()
    require_level_choice()
    if game_over or game_won:
        raise HTTPException(400, detail="Oyun aktif değil")
    if payload.item_index < 0 or payload.item_index >= len(inventory):
        raise HTTPException(400, detail="Geçersiz envanter indeksi")

    item = inventory[payload.item_index]
    if item.get("id") != "invisibility_potion":
        raise HTTPException(400, detail="Bu eşya kullanılamaz")

    inventory.pop(payload.item_index)
    player_state["invisible_until"] = datetime.now(timezone.utc).timestamp() + INVISIBILITY_DURATION
    message = f"Görünmezlik İksiri kullanıldı! {INVISIBILITY_DURATION} saniye görünmezsin."
    return {**build_status(), "success": True, "message": message,
            "logs": [{"type": "magic", "message": message}]}


@app.post("/api/unequip")
async def unequip_item(payload: UnequipRequest):
    require_class_selected()
    if payload.slot not in equipment:
        raise HTTPException(400, detail="Geçersiz slot")
    item = equipment[payload.slot]
    if not item:
        raise HTTPException(400, detail="Bu slot boş")
    if not add_to_inventory(item):
        raise HTTPException(400, detail="Envanter dolu")
    equipment[payload.slot] = None
    recalc_stats()
    return {**build_status(), "success": True, "message": f"{item['name']} çıkarıldı."}


@app.post("/api/reset")
async def reset_game():
    global class_selected, character_class, game_map, enemies, chests
    global game_over, game_won, pending_level_ups, boss_entity, current_floor, equipment, inventory
    global secret_map_index, secret_key, secret_door, has_secret_key, cat_quest, red_hatch_pos, cat_state, red_key
    class_selected = False
    character_class = None
    game_map = []
    enemies = []
    chests = []
    game_over = False
    game_won = False
    pending_level_ups = 0
    boss_entity = None
    current_floor = 1
    secret_map_index = 1
    secret_key = {"x": -1, "y": -1, "active": False}
    secret_door = {"x": -1, "y": -1, "open": False}
    has_secret_key = False
    cat_quest = default_cat_quest()
    cat_state = {"active": False, "rescued": False, "x": -1, "y": -1, "trail": []}
    red_key = {"x": -1, "y": -1, "active": False}
    red_hatch_pos = {"x": -1, "y": -1}
    init_daily_quest()
    return build_status()


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(
        "main:app",
        host=os.getenv("HOST", "0.0.0.0"),
        port=int(os.getenv("PORT", "8001")),
        reload=False,
    )