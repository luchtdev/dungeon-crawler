import random
import os
import hashlib
import hmac
import json
import secrets
import sqlite3
from datetime import datetime, timedelta, timezone
from collections import deque
from pathlib import Path
from typing import Optional

from fastapi import FastAPI, HTTPException, Request, Response
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse, JSONResponse
from pydantic import BaseModel, Field

BASE_DIR = Path(__file__).resolve().parent
DB_PATH = BASE_DIR / "cyber_dungeon.sqlite3"
SESSION_COOKIE = "cyber_dungeon_session"
SESSION_DAYS = 30
ADMIN_LOG_KEY_ENV = "CYBER_DUNGEON_ADMIN_KEY"

GRID_SIZE = 48
TILE = 0
WALL = 1
STAIRS = 2
SECRET_DOOR = 3
SECRET_MAP_COUNT = 5

FOG_UNEXPLORED = 0
FOG_VISIBLE = 1
FOG_FOGGY = 2

EXP_TO_LEVEL = 100
ENEMY_COUNT = 8
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
BOSS_AOE_INTERVAL = 3   # boss every N turns fires neon flame AoE

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

# ---------------------------------------------------------------------------
# Item / Equipment tables
# ---------------------------------------------------------------------------
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
}

CYBER_DRAGON = {
    "id": 9999,
    "name": "Cyber-Dragon",
    "hp": 2000,
    "max_hp": 2000,
    "damage": 40,
    "defense": 15,         # flat damage reduction
    "exp": 5000,
    "gold": 1000,
    "move_speed": 1,
    "range": 1,
    "color": "#ff6600",
    "is_boss": True,
    "aoe_timer": 0,        # counts turns since last AoE
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


def db_connect() -> sqlite3.Connection:
    connection = sqlite3.connect(DB_PATH)
    connection.row_factory = sqlite3.Row
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
    token = request.cookies.get(SESSION_COOKIE)
    if not token:
        return None
    now = datetime.now(timezone.utc).isoformat()
    with db_connect() as connection:
        row = connection.execute(
            "SELECT user_id FROM sessions WHERE token = ? AND expires_at > ?", (token, now)
        ).fetchone()
    return int(row["user_id"]) if row else None


def create_session(user_id: int, response: Response) -> None:
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


def account_achievements() -> list:
    if not current_user_id:
        return []
    with db_connect() as connection:
        row = connection.execute("SELECT achievements_json FROM profiles WHERE user_id = ?", (current_user_id,)).fetchone()
    unlocked = json.loads(row["achievements_json"]) if row else []
    return [
        {"id": achievement_id, **definition, "unlocked": achievement_id in unlocked}
        for achievement_id, definition in ACHIEVEMENTS.items()
    ]

# ---------------------------------------------------------------------------
# Global state
# ---------------------------------------------------------------------------
game_map: list = []
fog_matrix: list = []
enemies: list = []
chests: list = []
merchant_state = {"x": 0, "y": 0}
stairs_pos: dict = {"x": -1, "y": -1}
next_enemy_id = 1
game_over = False
game_won = False
pending_level_ups = 0
boss_entity: Optional[dict] = None   # active boss on floor 100
current_user_id: Optional[int] = None
class_selected = False
character_class: Optional[str] = None
daily_quest: dict = {}
current_floor = 1
secret_map_index = 1
secret_key = {"x": -1, "y": -1, "active": False}
secret_door = {"x": -1, "y": -1, "open": False}
has_secret_key = False

player_state = {
    "hp": 100, "max_hp": 100,
    "gold": 0, "exp": 0, "level": 1,
    "exp_to_next": EXP_TO_LEVEL,
    "attack_power": BASE_ATTACK,
    "damage_reduction": 0,
    "mp": BASE_MP, "max_mp": BASE_MP,
    "invisible_until": 0,
    "invisible_until": 0,
    "level_attack_bonus": 0, "level_defense_bonus": 0,
    "level_max_hp_bonus": 0, "level_max_mp_bonus": 0,
    "x": 0, "y": 0,
    "character_class": None,
    "stats": {"enemies_killed": 0, "total_gold_earned": 0, "highest_floor": 1, "games_won": 0},
}

# Equipment slots: None or item dict
equipment: dict = {"weapon": None, "armor": None, "accessory": None}
# Backpack inventory list of item dicts
inventory: list = []
MAX_INVENTORY = 12


def runtime_state() -> dict:
    return {
        "game_map": game_map, "fog_matrix": fog_matrix, "enemies": enemies, "chests": chests,
        "merchant_state": merchant_state, "stairs_pos": stairs_pos, "next_enemy_id": next_enemy_id,
        "game_over": game_over, "game_won": game_won, "boss_entity": boss_entity,
        "class_selected": class_selected, "character_class": character_class,
        "daily_quest": daily_quest, "current_floor": current_floor, "secret_map_index": secret_map_index,
        "secret_key": secret_key, "secret_door": secret_door, "has_secret_key": has_secret_key,
        "player_state": player_state, "equipment": equipment, "inventory": inventory,
        "pending_level_ups": pending_level_ups,
    }


def clear_runtime_state() -> None:
    global game_map, fog_matrix, enemies, chests, merchant_state, stairs_pos, next_enemy_id
    global game_over, game_won, boss_entity, class_selected, character_class, daily_quest
    global current_floor, secret_map_index, secret_key, secret_door, has_secret_key
    global equipment, inventory, pending_level_ups
    game_map, fog_matrix, enemies, chests = [], [], [], []
    merchant_state, stairs_pos = {"x": 0, "y": 0}, {"x": -1, "y": -1}
    next_enemy_id = 1
    game_over = game_won = False
    boss_entity = None
    class_selected = False
    character_class = None
    daily_quest = {}
    current_floor = secret_map_index = 1
    secret_key = {"x": -1, "y": -1, "active": False}
    secret_door = {"x": -1, "y": -1, "open": False}
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
    global current_user_id, game_map, fog_matrix, enemies, chests, merchant_state, stairs_pos, next_enemy_id
    global game_over, game_won, boss_entity, class_selected, character_class, daily_quest
    global current_floor, secret_map_index, secret_key, secret_door, has_secret_key
    global player_state, equipment, inventory, pending_level_ups
    current_user_id = user_id
    with db_connect() as connection:
        row = connection.execute("SELECT state_json FROM profiles WHERE user_id = ?", (user_id,)).fetchone()
    if not row:
        clear_runtime_state()
        return
    state = json.loads(row["state_json"])
    if "player_state" not in state:
        clear_runtime_state()
        return
    game_map = state.get("game_map", [])
    ensure_map_connected(game_map)
    fog_matrix = state.get("fog_matrix", [])
    enemies = state.get("enemies", [])
    chests = state.get("chests", [])
    merchant_state = state.get("merchant_state", {"x": 0, "y": 0})
    stairs_pos = state.get("stairs_pos", {"x": -1, "y": -1})
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
    has_secret_key = state.get("has_secret_key", False)
    player_state = state.get("player_state", player_state)
    player_state.setdefault("stats", {"enemies_killed": 0, "total_gold_earned": 0, "highest_floor": current_floor, "games_won": 0})
    player_state.setdefault("invisible_until", 0)
    equipment = state.get("equipment", {"weapon": None, "armor": None, "accessory": None})
    inventory = state.get("inventory", [])
    pending_level_ups = state.get("pending_level_ups", 0)


def save_game_state() -> None:
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


@app.middleware("http")
async def account_state_middleware(request: Request, call_next):
    public_paths = {"/", "/index.html", "/api/auth/register", "/api/auth/login", "/api/auth/logout",
                    "/api/admin/account-log", "/favicon.ico"}
    if request.url.path.startswith("/api/") and request.url.path not in public_paths:
        user_id = session_user_id(request)
        if not user_id:
            return JSONResponse({"detail": "Giris yapman gerekiyor"}, status_code=401)
        load_game_state(user_id)
        response = await call_next(request)
        if response.status_code < 500:
            save_game_state()
        return response
    return await call_next(request)

# ---------------------------------------------------------------------------
# Pydantic models
# ---------------------------------------------------------------------------
class MoveRequest(BaseModel):
    direction: str = Field(..., pattern="^(up|down|left|right)$")

class BuyItemRequest(BaseModel):
    item: str

class FireballRequest(BaseModel):
    enemy_id: int

class SelectClassRequest(BaseModel):
    character_class: str = Field(..., pattern="^(Warrior|Mage|Rogue)$")

class EquipRequest(BaseModel):
    item_index: int   # index into inventory list

class UnequipRequest(BaseModel):
    slot: str   # "weapon" | "armor" | "accessory"

class LevelUpRequest(BaseModel):
    choice: str = Field(..., pattern="^(power|vitality|focus)$")

class AuthRequest(BaseModel):
    username: str = Field(..., min_length=3, max_length=24, pattern="^[A-Za-z0-9_]+$")
    password: str = Field(..., min_length=6, max_length=128)

# ---------------------------------------------------------------------------
# BSP Dungeon Generation
# ---------------------------------------------------------------------------
class BSPNode:
    def __init__(self, x, y, w, h):
        self.x, self.y, self.w, self.h = x, y, w, h
        self.left = self.right = None
        self.room = None  # (rx, ry, rw, rh)

    def split(self, min_size=7):
        if self.left or self.right:
            return
        can_h = self.w >= min_size * 2
        can_v = self.h >= min_size * 2
        if not can_h and not can_v:
            return
        if can_h and can_v:
            horizontal = random.choice([True, False])
        else:
            horizontal = can_v
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
            # Connect child rooms with a corridor
            lr = self.left.get_room() if self.left else None
            rr = self.right.get_room() if self.right else None
            if lr and rr:
                _carve_corridor(grid, lr, rr)
        else:
            # Leaf: carve a room
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
        lr = self.left.get_room()  if self.left  else None
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
    # L-shaped corridor
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


def generate_bsp_map() -> list:
    grid = [[WALL] * GRID_SIZE for _ in range(GRID_SIZE)]
    root = BSPNode(0, 0, GRID_SIZE, GRID_SIZE)
    root.split(min_size=7)
    root.create_rooms(grid)
    # Guarantee a comfortable 5x5 starting room around the player spawn.
    for yy in range(5):
        for xx in range(5):
            grid[yy][xx] = TILE
    ensure_map_connected(grid)
    return grid


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
    """Join every walkable map component so no destination is unreachable."""
    if not grid:
        return
    walkable = {(x, y) for y in range(GRID_SIZE) for x in range(GRID_SIZE)
                if grid[y][x] != WALL}
    reachable = get_reachable_cells(grid)
    while walkable - reachable:
        target = min(walkable - reachable,
                     key=lambda cell: min(manhattan(cell[0], cell[1], point[0], point[1])
                                          for point in reachable))
        anchor = min(reachable,
                     key=lambda point: manhattan(point[0], point[1], target[0], target[1]))
        ax, ay = anchor
        tx, ty = target
        for x in range(min(ax, tx), max(ax, tx) + 1):
            grid[ay][x] = TILE
        for y in range(min(ay, ty), max(ay, ty) + 1):
            grid[y][tx] = TILE
        walkable = {(x, y) for y in range(GRID_SIZE) for x in range(GRID_SIZE)
                    if grid[y][x] != WALL}
        reachable = get_reachable_cells(grid)


def get_all_floor_tiles() -> list:
    tiles = []
    for y in range(GRID_SIZE):
        for x in range(GRID_SIZE):
            if game_map[y][x] == TILE:
                tiles.append((x, y))
    return tiles

# ---------------------------------------------------------------------------
# A* pathfinding
# ---------------------------------------------------------------------------
def heuristic(a, b):
    return abs(a[0] - b[0]) + abs(a[1] - b[1])


def astar(start, goal, occupied: set) -> Optional[tuple]:
    """Return the first step toward goal, or None if unreachable."""
    if start == goal:
        return None
    open_set = [(0, start)]
    came_from = {}
    g_score = {start: 0}
    visited = set()
    while open_set:
        # manual min extraction (no heapq import needed; small grid)
        open_set.sort(key=lambda x: x[0])
        _, current = open_set.pop(0)
        if current in visited:
            continue
        visited.add(current)
        if current == goal:
            # Reconstruct first step
            path = [current]
            while path[-1] in came_from:
                path.append(came_from[path[-1]])
            path.reverse()
            return path[1] if len(path) > 1 else None
        cx, cy = current
        for dx, dy in [(0,-1),(0,1),(-1,0),(1,0)]:
            nx, ny = cx + dx, cy + dy
            nb = (nx, ny)
            if not is_in_bounds(nx, ny):
                continue
            if game_map[ny][nx] == WALL:
                continue
            if nb in visited:
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


# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------
def is_in_bounds(x: int, y: int) -> bool:
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

# ---------------------------------------------------------------------------
# Spawn helpers
# ---------------------------------------------------------------------------
def spawn_stairs() -> None:
    global stairs_pos
    # No stairs on the final boss floor
    if current_floor >= BOSS_FLOOR or secret_map_index >= SECRET_MAP_COUNT:
        stairs_pos = {"x": -1, "y": -1}
        return
    exclude = {(player_state["x"], player_state["y"]), (0, 0)}
    for c in chests:
        exclude.add((c["x"], c["y"]))
    exclude.add((merchant_state["x"], merchant_state["y"]))
    candidates = get_spawn_candidates(exclude)
    candidates.sort(key=lambda p: -(abs(p[0]) + abs(p[1])))
    if candidates:
        sx, sy = candidates[0]
        stairs_pos = {"x": sx, "y": sy}
        game_map[sy][sx] = STAIRS
        # Pre-reveal stairs tile so player can see it on the map (foggy = visited)
        if fog_matrix:
            for dy in range(-1, 2):
                for dx in range(-1, 2):
                    nx, ny = sx + dx, sy + dy
                    if is_in_bounds(nx, ny) and fog_matrix[ny][nx] == FOG_UNEXPLORED:
                        fog_matrix[ny][nx] = FOG_FOGGY
    else:
        stairs_pos = {"x": -1, "y": -1}


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
    exclude = {(player_state["x"], player_state["y"]), (0,0),(0,1),(1,0),(1,1)}
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

    # Floor 100 = boss only — handled by spawn_boss()
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

    type_pool = ["Goblin"] * 5 + ["Skeleton Archer"] * 3 + (["Orc Bruiser"] * 2 if current_floor >= 2 else [])

    for x, y in candidates[:ENEMY_COUNT]:
        etype = random.choice(type_pool)
        stats = _scale_enemy(etype, current_floor)
        enemies.append({
            "id": next_enemy_id,
            "name": etype,
            "x": x, "y": y,
            **stats,
            "move_timer": 0,
        })
        next_enemy_id += 1


def spawn_boss() -> None:
    """Spawn the Cyber-Dragon on floor 100. Places it far from the player."""
    global boss_entity
    exclude = {(player_state["x"], player_state["y"]), (0, 0)}
    for c in chests:
        exclude.add((c["x"], c["y"]))
    candidates = get_spawn_candidates(exclude)
    # Pick farthest floor tile from player spawn
    candidates.sort(key=lambda p: -(p[0] + p[1]))
    bx, by = candidates[0] if candidates else (GRID_SIZE // 2, GRID_SIZE // 2)

    import copy
    boss_entity = copy.deepcopy(CYBER_DRAGON)
    boss_entity["x"] = bx
    boss_entity["y"] = by
    boss_entity["aoe_timer"] = 0


def spawn_secret_route() -> None:
    """Place a key and locked door on maps 1-4."""
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
    candidates = get_spawn_candidates(exclude)
    if len(candidates) < 2:
        return
    random.shuffle(candidates)
    key_pos = candidates[0]
    distant_candidates = [p for p in candidates[1:]
                          if abs(p[0] - key_pos[0]) + abs(p[1] - key_pos[1]) >= GRID_SIZE // 3]
    door_pos = random.choice(distant_candidates or candidates[1:])
    secret_key = {"x": key_pos[0], "y": key_pos[1], "active": True}
    secret_door = {"x": door_pos[0], "y": door_pos[1], "open": False}
    game_map[door_pos[1]][door_pos[0]] = SECRET_DOOR

# ---------------------------------------------------------------------------
# Fog of war
# ---------------------------------------------------------------------------
def init_fog() -> None:
    global fog_matrix
    fog_matrix = [[FOG_UNEXPLORED] * GRID_SIZE for _ in range(GRID_SIZE)]


def update_fog(px: int, py: int, radius: int = 4) -> None:
    for y in range(GRID_SIZE):
        for x in range(GRID_SIZE):
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
    return (player_state["x"] == merchant_state["x"]
            and player_state["y"] == merchant_state["y"])


def is_at_stairs() -> bool:
    return (player_state["x"] == stairs_pos["x"]
            and player_state["y"] == stairs_pos["y"])


def is_at_secret_door() -> bool:
    return (player_state["x"] == secret_door["x"]
            and player_state["y"] == secret_door["y"])


def collect_secret_key(logs: list) -> None:
    global secret_key, secret_door, has_secret_key
    if secret_key["active"] and (player_state["x"], player_state["y"]) == (secret_key["x"], secret_key["y"]):
        secret_key["active"] = False
        has_secret_key = True
        secret_door["open"] = True
        logs.append({"type": "quest", "message": f"🗝️ Gizli geçit anahtarını buldun! Harita {secret_map_index}/5"})


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
    if secret_map_index >= SECRET_MAP_COUNT:
        spawn_boss()
        logs.append({"type": "combat", "message": "🏛️ FINAL HARİTA — Hazineyi koruyan Cyber-Dragon uyandı!"})
    else:
        logs.append({"type": "quest", "message": f"🚪 Gizli geçitten geçtin! Harita {secret_map_index}/5"})
    update_fog(0, 0)

# ---------------------------------------------------------------------------
# Quest
# ---------------------------------------------------------------------------
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
    logs.append({"type": "quest",
                 "message": f"Görev tamamlandı: {completed_name}! +{reward} Altın"})
    init_daily_quest(exclude_name=completed_name)
    logs.append({"type": "quest",
                 "message": f"Yeni görev: {daily_quest['name']}"})
    return True


def on_enemy_killed(logs: list) -> None:
    if daily_quest.get("completed"): return
    if daily_quest.get("type") == "kill_enemies":
        daily_quest["progress"] += 1
        try_complete_quest(logs)


def on_gold_collected(amount: int, logs: list) -> None:
    if daily_quest.get("completed"): return
    if daily_quest.get("type") == "collect_gold":
        daily_quest["progress"] = min(daily_quest["target"],
                                      daily_quest["progress"] + amount)
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


# ---------------------------------------------------------------------------
# Equipment / Inventory helpers
# ---------------------------------------------------------------------------
def recalc_stats() -> None:
    """Recompute attack_power and damage_reduction from base class + equipped items."""
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
    # Add level bonus
    atk += (player_state["level"] - 1) * 2 + player_state["level_attack_bonus"]
    player_state["attack_power"] = atk
    player_state["damage_reduction"] = dfn + player_state["level_defense_bonus"]


def roll_item_drop() -> Optional[dict]:
    if random.random() > ITEM_DROP_CHANCE:
        return None
    # Pick rarity
    keys = list(RARITY_DROP_WEIGHTS.keys())
    weights = [RARITY_DROP_WEIGHTS[k] for k in keys]
    rarity = random.choices(keys, weights=weights, k=1)[0]
    # Pick slot
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


# ---------------------------------------------------------------------------
# Floor progression
# ---------------------------------------------------------------------------
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

    # Floor 100: spawn the boss instead of regular enemies
    if current_floor >= BOSS_FLOOR:
        spawn_boss()
        logs.append({"type": "combat",
                     "message": f"⚠️ KAT {current_floor} — CYBER-DRAGON UYANDIN! Son savaş başlıyor!"})
    else:
        logs.append({"type": "exp",
                     "message": f"🔽 Kat {current_floor}/{MAX_FLOOR}'e indin! +{heal} HP iyileşti."})

    on_floor_reached(logs)
    update_fog(0, 0)

# ---------------------------------------------------------------------------
# Core game logic
# ---------------------------------------------------------------------------
def init_game_with_class(cls: str) -> None:
    global game_map, game_over, game_won, boss_entity, next_enemy_id, character_class
    global class_selected, current_floor, equipment, inventory, secret_map_index, pending_level_ups
    character_class = cls
    class_selected = True
    current_floor = 1
    secret_map_index = 1
    game_won = False
    pending_level_ups = 0
    boss_entity = None
    equipment = {"weapon": None, "armor": None, "accessory": None}
    inventory = []

    game_map = generate_bsp_map()
    stats = CLASS_STATS[cls]
    player_state.update({
        "hp": stats["hp"], "max_hp": stats["max_hp"],
        "gold": stats["gold"], "exp": 0, "level": 1,
        "exp_to_next": EXP_TO_LEVEL,
        "attack_power": stats["attack_power"],
        "damage_reduction": 0,
        "mp": stats["mp"], "max_mp": stats["max_mp"],
        "level_attack_bonus": 0, "level_defense_bonus": 0,
        "level_max_hp_bonus": 0, "level_max_mp_bonus": 0,
        "x": 0, "y": 0,
        "character_class": cls,
        "stats": {"enemies_killed": 0, "total_gold_earned": 0, "highest_floor": 1, "games_won": 0},
    })
    game_over = False
    init_daily_quest()
    init_fog()
    spawn_chests()
    spawn_merchant()
    spawn_stairs()
    spawn_secret_route()
    spawn_enemies()
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


def check_game_over() -> None:
    global game_over
    if player_state["hp"] <= 0:
        player_state["hp"] = 0
        game_over = True


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
    logs.append({"type": "gold",
                     "message": f"{enemy['name']} yenildi! +{gold_gain} GOLD +{exp_gain} EXP"})
    on_enemy_killed(logs)
    on_gold_collected(gold_gain, logs)
    # Item drop
    dropped = roll_item_drop()
    if dropped:
        added = add_to_inventory(dropped)
        if added:
            logs.append({"type": "item",
                         "message": f"💎 Eşya düştü: {dropped['name']} ({dropped['rarity']})"})
        else:
            logs.append({"type": "info", "message": "Envanter dolu! Eşya kayboldu."})
    return {"gold_gained": gold_gain, "exp_gained": exp_gain,
            "item_drop": dropped}


def calc_enemy_damage(enemy: dict) -> int:
    return max(1, enemy["damage"] - player_state["damage_reduction"])


def invisibility_active() -> bool:
    return player_state.get("invisible_until", 0) > datetime.now(timezone.utc).timestamp()


def resolve_combat(enemy: dict, logs: list) -> dict:
    atk = player_state["attack_power"]
    enemy["hp"] -= atk
    logs.append({"type": "combat",
                 "message": f"{enemy['name']}'e {atk} hasar vurdun!"})
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
        logs.append({"type": "combat",
                     "message": f"{enemy['name']} sana {dmg} hasar vurdu!"})
        check_game_over()
    return result


def collect_chest(logs: list) -> None:
    for c in chests:
        if not c["active"]: continue
        if player_state["x"] != c["x"] or player_state["y"] != c["y"]: continue
        c["active"] = False
        player_state["gold"] += CHEST_GOLD
        player_state["stats"]["total_gold_earned"] += CHEST_GOLD
        apply_exp(CHEST_EXP)
        logs.append({"type": "gold",
                     "message": f"Hazine buldun! +{CHEST_GOLD} GOLD +{CHEST_EXP} EXP"})
        if daily_quest.get("type") == "collect_gold":
            on_gold_collected(CHEST_GOLD, logs)
        elif daily_quest.get("type") == "open_chests":
            on_chest_opened(logs)
        break

# ---------------------------------------------------------------------------
# Enemy AI — A* for visible enemies, random walk otherwise
# ---------------------------------------------------------------------------
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

        # Orc Bruiser moves every other turn
        if enemy.get("move_speed", 1) > 1:
            enemy["move_timer"] = enemy.get("move_timer", 0) + 1
            if enemy["move_timer"] % enemy["move_speed"] != 0:
                continue

        old_x, old_y = enemy["x"], enemy["y"]
        occupied = get_occupied_cells(exclude_enemy_id=enemy["id"])
        dist = tile_distance(enemy["x"], enemy["y"], px, py)
        is_visible = is_tile_visible(enemy["x"], enemy["y"])

        # Skeleton Archer — ranged attack
        if not invisible and enemy.get("range", 1) >= 3 and dist <= enemy["range"] and is_visible:
            dmg = calc_enemy_damage(enemy)
            player_state["hp"] = max(0, player_state["hp"] - dmg)
            logs.append({"type": "combat",
                         "message": f"🏹 {enemy['name']} sana {dmg} ok attı!"})
            check_game_over()
            battles.append({
                "enemy_id": enemy["id"], "enemy_name": enemy["name"],
                "enemy_x": enemy["x"],   "enemy_y": enemy["y"],
                "enemy_killed": False, "ranged": True,
                "damage_dealt": 0, "gold_gained": 0, "exp_gained": 0,
            })
            continue

        # Decide move target
        if not invisible and is_visible and dist <= 8:
            # A* toward player
            step = astar((old_x, old_y), (px, py), occupied)
        else:
            # Random walk
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


# ---------------------------------------------------------------------------
# Boss AI — Cyber-Dragon
# ---------------------------------------------------------------------------
def move_boss(logs: list) -> list:
    """Handle the Cyber-Dragon's turn: move toward player + AoE every N turns."""
    global boss_entity, game_won
    battles = []
    if boss_entity is None or game_over:
        return battles

    if invisibility_active():
        return battles

    px, py = player_state["x"], player_state["y"]
    boss_entity["aoe_timer"] = boss_entity.get("aoe_timer", 0) + 1

    # Every BOSS_AOE_INTERVAL turns: Neon Flame AoE on 3x3 around player
    if boss_entity["aoe_timer"] >= BOSS_AOE_INTERVAL:
        boss_entity["aoe_timer"] = 0
        aoe_dmg = max(1, boss_entity["damage"] // 2 - player_state["damage_reduction"])
        player_state["hp"] = max(0, player_state["hp"] - aoe_dmg)
        check_game_over()
        logs.append({"type": "combat",
                     "message": f"🔥 Cyber-Dragon'un NEON ALEVI! {aoe_dmg} AoE hasar!"})
        battles.append({
            "enemy_id": 9999, "enemy_name": "Cyber-Dragon",
            "enemy_x": boss_entity["x"], "enemy_y": boss_entity["y"],
            "enemy_killed": False, "aoe": True,
            "aoe_radius": 1, "aoe_cx": px, "aoe_cy": py,
            "damage_dealt": aoe_dmg, "gold_gained": 0, "exp_gained": 0,
        })
        return battles

    # Normal move toward player (A*)
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
        check_game_over()
        logs.append({"type": "combat",
                     "message": f"Cyber-Dragon sana {dmg} hasar vurdu!"})
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
    """Player attacks the boss. Returns result dict."""
    global boss_entity, game_won
    effective_atk = max(1, atk - boss_entity.get("defense", 0))
    boss_entity["hp"] -= effective_atk
    logs.append({"type": "combat",
                 "message": f"Cyber-Dragon'a {effective_atk} hasar vurdun! (HP: {max(0,boss_entity['hp'])}/{boss_entity['max_hp']})"})
    if boss_entity["hp"] <= 0:
        boss_entity["hp"] = 0
        game_won = True
        player_state["gold"] += boss_entity["gold"]
        player_state["stats"]["total_gold_earned"] += boss_entity["gold"]
        player_state["stats"]["games_won"] += 1
        apply_exp(boss_entity["exp"])
        logs.append({"type": "quest",
                     "message": "CYBER-DRAGON YENİLDİ! Zindan fethedildi! ZAFER!"})
        return {"enemy_killed": True, "gold_gained": boss_entity["gold"],
                "exp_gained": boss_entity["exp"], "game_won": True,
                "enemy_id": 9999, "enemy_name": "Cyber-Dragon",
                "enemy_x": boss_entity["x"], "enemy_y": boss_entity["y"],
                "damage_dealt": effective_atk}
    return {"enemy_killed": False, "gold_gained": 0, "exp_gained": 0,
            "game_won": False, "enemy_id": 9999, "enemy_name": "Cyber-Dragon",
            "enemy_x": boss_entity["x"], "enemy_y": boss_entity["y"],
            "damage_dealt": effective_atk}

# ---------------------------------------------------------------------------
# build_status — full state payload
# ---------------------------------------------------------------------------
def build_status() -> dict:
    base = {
        "class_selected": class_selected,
        "character_class": character_class,
        "grid_size": GRID_SIZE,
        "floor": current_floor,
        "secret_map": secret_map_index,
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
            "enemies": [], "chests": [],
            "merchant": {"x": 0, "y": 0, "visible": False},
            "stairs": {"x": -1, "y": -1},
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
        "merchant": get_visible_merchant(),
        "stairs": dict(stairs_pos),
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


# ---------------------------------------------------------------------------
# FastAPI endpoints
# ---------------------------------------------------------------------------
def require_class_selected():
    if not class_selected:
        raise HTTPException(400, detail="Önce karakter sınıfı seçin")


@app.on_event("startup")
async def on_startup():
    init_database()
    clear_runtime_state()

@app.get("/icon.svg")
async def get_icon():
    return FileResponse(BASE_DIR / "icon.svg", media_type="image/svg+xml")

@app.get("/knight_sheet.png")
async def get_knight_sheet():
    return FileResponse(BASE_DIR / "knight_sheet.png")

@app.get("/monters.png")
async def get_monsters():
    return FileResponse(BASE_DIR / "monters.png")


@app.get("/")
@app.get("/index.html")
async def serve_index():
    return FileResponse(BASE_DIR / "index.html")

@app.get("/icon.png")
async def get_icon():
    return FileResponse(BASE_DIR / "icon.png")


@app.get("/icon.svg")
async def serve_icon():
    return FileResponse(BASE_DIR / "icon.svg", media_type="image/svg+xml")


def get_username(user_id: Optional[int]) -> Optional[str]:
    if not user_id:
        return None
    with db_connect() as connection:
        row = connection.execute("SELECT username FROM users WHERE id = ?", (user_id,)).fetchone()
    return row["username"] if row else None


@app.post("/api/auth/register")
async def register(payload: AuthRequest, response: Response):
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
    load_game_state(user_id)
    create_session(user_id, response)
    return {**build_status(), "success": True, "message": "Hesap olusturuldu"}


@app.post("/api/auth/login")
async def login(payload: AuthRequest, response: Response):
    with db_connect() as connection:
        row = connection.execute("SELECT id, password_hash FROM users WHERE username = ?", (payload.username,)).fetchone()
    if not row or not verify_password(payload.password, row["password_hash"]):
        record_auth_event(payload.username, "login_failed", int(row["id"]) if row else None)
        raise HTTPException(401, detail="Kullanici adi veya parola hatali")
    user_id = int(row["id"])
    record_auth_event(payload.username, "login_success", user_id)
    load_game_state(user_id)
    create_session(user_id, response)
    return {**build_status(), "success": True, "message": "Giris yapildi"}


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
            "stairs": {"x": -1, "y": -1},
            "x": 0, "y": 0,
        }
    return {
        "class_selected": True, "grid_size": GRID_SIZE,
        "map": game_map,
        "fog_matrix": [row[:] for row in fog_matrix],
        "enemies": get_visible_enemies(),
        "chests": get_visible_chests(),
        "merchant": get_visible_merchant(),
        "stairs": dict(stairs_pos),
        "x": player_state["x"], "y": player_state["y"],
    }


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
    floor_changed = False
    secret_map_changed = False
    blocked = False

    dx, dy = DIR_DELTA[payload.direction]
    old_x, old_y = player_state["x"], player_state["y"]
    if not is_in_bounds(old_x, old_y) or game_map[old_y][old_x] == WALL:
        player_state["x"], player_state["y"] = 0, 0
        old_x, old_y = 0, 0
    new_x, new_y = old_x + dx, old_y + dy

    if not is_in_bounds(new_x, new_y) or game_map[new_y][new_x] == WALL:
        blocked = True
        logs.append({"type": "info", "message": "Duvara çarptın!"})
    elif game_map[new_y][new_x] == SECRET_DOOR and not has_secret_key:
        blocked = True
        logs.append({"type": "info", "message": "Gizli geçit kilitli. Anahtarı bulmalısın!"})
    else:
        # Check if moving into boss
        if boss_entity and (new_x, new_y) == (boss_entity["x"], boss_entity["y"]):
            battle = attack_boss(player_state["attack_power"], logs)
            battles.append(battle)
            if not battle["enemy_killed"]:
                # Boss counter-attacks immediately after being hit
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
            collect_secret_key(logs)

        if not game_over and not game_won and not blocked:
            battles += move_enemies(logs)
            if boss_entity and not game_won:
                battles += move_boss(logs)

        update_fog(player_state["x"], player_state["y"])

        # Check stairs
        if not game_over and not game_won and is_at_stairs():
            descend_floor(logs)
            floor_changed = True

        if not game_over and not game_won and has_secret_key and is_at_secret_door():
            enter_secret_map(logs)
            secret_map_changed = True

        if not battles:
            regen_mp_safe()

    if game_over:
        logs.append({"type": "combat", "message": "GAME OVER — Şövalyen düştü!"})

    return {
        **build_status(),
        "logs": logs, "battles": battles,
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
    elif payload.item == "armor_upgrade":
        player_state["damage_reduction"] += 3
        message = f"Zırh güçlendi! DEF: -{player_state['damage_reduction']}"
    elif payload.item == "invisibility_potion":
        player_state["invisible_until"] = datetime.now(timezone.utc).timestamp() + INVISIBILITY_DURATION
        message = f"Görünmezlik İksiri! {INVISIBILITY_DURATION} saniye görünmezsin."

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
    logs.append({"type": "magic",
                 "message": f"🔥 Alev Topu! {enemy['name']}'e {FIREBALL_DAMAGE} hasar (-{FIREBALL_COST} MP)"})

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

    # Unequip current item → back to inventory
    if equipment[slot]:
        inventory.append(equipment[slot])

    equipment[slot] = item
    inventory.pop(payload.item_index)
    recalc_stats()
    return {**build_status(), "success": True,
            "message": f"{item['name']} donanıldı! ({slot})"}


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
    return {**build_status(), "success": True,
            "message": f"{item['name']} çıkarıldı."}


@app.post("/api/reset")
async def reset_game():
    global class_selected, character_class, game_map, enemies, chests
    global game_over, game_won, pending_level_ups, boss_entity, current_floor, equipment, inventory
    global secret_map_index, secret_key, secret_door, has_secret_key
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
    equipment = {"weapon": None, "armor": None, "accessory": None}
    inventory = []
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
