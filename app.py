# ============================================================
# BG  —  Auto-Bio + Per-Match Squad Loop + /glory Auto-Farm
# ============================================================
import sys, os, json, time, uuid, random, asyncio, base64, struct, socket
import itertools, traceback, ssl, hmac, hashlib, string, re, subprocess
import httpx
import aiohttp
import aiohttp.web
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Any

if sys.platform == "win32":
    try:
        if hasattr(sys.stdout, 'reconfigure'):
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
            sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception: pass

from google_play_scraper import app as play_scraper
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from protobuf_decoder.protobuf_decoder import Parser
from message_ids import MESSAGE_ID_TO_NAME
import thunderFF_pb2

import config as _cfg
import tools as _tools
import toolsudp as _toolsudp
import ff_udp as _ff_udp
import ff_match as _ff_match

import infoClan_pb2

try:
    import StartMatch_pb2
except Exception:
    StartMatch_pb2 = None

try:
    import reqClan_pb2
    _CLAN_PB_AVAILABLE = True
except Exception:
    _CLAN_PB_AVAILABLE = False

# ==================== CONFIG ====================
WEB_HOST = "0.0.0.0"
WEB_PORT = 20331
TOKEN_CACHE_FILE = "token_cache.json"
DEVICES_FILE = "devices.json"
TOKEN_CACHE_TTL = 1200
INDEX_HTML_PATH = "templates/index.html"

TEAMS_DIR = "teams"
os.makedirs(TEAMS_DIR, exist_ok=True)

START_MATCH_INTERVAL = 5.0
NEW_MATCH_DELAY      = 4.0
MAX_MATCH_DURATION   = 1500
MATCH_IDLE_TIMEOUT   = 90.0

_accept_friend_request = True
DEBUG_ALL_PACKETS = False

TEAM_MODE = True
TEAM_SIZE = 4
TEAM_READY_DELAY = 6.0
TEAM_INVITE_WAIT = 2.5
CLAN_ID_DEFAULT = ""

# ==================== PER-MATCH LOOP ====================
MATCH_CYCLE_DELAY   = 3.0    # seconds between consecutive matches
MATCH_REFORM_WAIT   = 20.0   # max wait for team to re-form after a match
MATCH_MAX_PER_LOOP  = 0      # 0 = infinite, >0 = stop loop after N matches

# ==================== AUTO BIO ====================
AUTO_BIO_ENABLED      = True
AUTO_BIO_TEXT         = "[B]Guild Glory Available DM @zestyji @bashantcodex"
AUTO_BIO_MAX_LEN      = 100
AUTO_BIO_REFRESH_SEC  = 600
AUTO_BIO_ON_LOGIN     = True
AUTO_BIO_URL          = "https://clientbp.ggpolarbear.com/UpdateSocialBasicInfo"
AUTO_BIO_RELEASE_VER  = "OB55"

# ==================== AUTO FARM (each /glory = new squad) ====================
AUTO_FARM_ON_GLORY       = True
AUTO_FARM_BOT_COUNT      = 4
AUTO_FARM_WAIT_LOGIN     = 120.0
AUTO_FARM_WAIT_GUILD     = 30.0
AUTO_FARM_REGION_DEFAULT = "BD"

AES_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
AES_IV  = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])
KEYSTREAM = bytes([0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30])
HEX_KEY = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"
API_KEY = HEX_KEY.encode()

REGION_LANG = {"ME":"ar","IND":"hi","ID":"id","VN":"vi","TH":"th","BD":"bn",
               "PK":"ur","TW":"zh","RU":"ru","SAC":"es","BR":"pt","NA":"pt",
               "SG":"pt","US":"pt"}

# ==================== STATE ====================
class BotState:
    def __init__(self):
        self.accounts: Dict[str, dict] = {}
        self.account_credentials: Dict[str, dict] = {}
        self.account_workers: Dict[str, asyncio.Task] = {}
        self.auth_to_game_id: Dict[str, str] = {}
        self.game_to_auth_id: Dict[str, str] = {}
        self.paused: set = set()
        self.writers: Dict[str, list] = {}
        self.logs: List[dict] = []
        self.total_matches = 0
        self.matches_started = 0
        self.total_exp_gained = 0
        self.create_progress: List[str] = []
        self.creating = False
        self.start_time = time.time()
        self._writer_lock = asyncio.Lock()
        self.auto_farm_squads: Dict[str, dict] = {}
        self.auto_farm_counter = 0

    def log(self, msg, level="info"):
        try:
            t = datetime.now().strftime("%H:%M:%S")
            self.logs.append({"t": time.time(), "time": t, "message": str(msg), "level": level})
            if len(self.logs) > 500: self.logs = self.logs[-500:]
        except Exception: pass

    def register_account(self, uid, nickname, region="BD", level=1, exp=0,
                         likes=0, token=None, auth_uid=None):
        uid = str(uid)
        existing = self.accounts.get(uid, {})
        self.accounts[uid] = {
            "uid": uid, "nickname": nickname, "region": region,
            "level": level, "exp": exp, "likes": likes,
            "token": token, "auth_uid": auth_uid, "status": "ONLINE",
            "current_exp": exp,
            "initial_exp": existing.get("initial_exp", exp),
            "gained_exp": existing.get("gained_exp", 0),
            "matches": existing.get("matches", 0),
            "active_matches": 0,
            "uptime_seconds": existing.get("uptime_seconds", 0),
            "last_match_time": existing.get("last_match_time", "Running..."),
            "is_paused": False}

    def update_status(self, uid, status, matches=0):
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["status"] = status
            self.accounts[uid]["active_matches"] = matches
            self.accounts[uid]["is_paused"] = (status == "PAUSED")

    def update_exp(self, uid, exp, level=None):
        uid = str(uid)
        if uid in self.accounts:
            a = self.accounts[uid]
            old = a.get("current_exp", 0)
            if exp > old:
                a["gained_exp"] = a.get("gained_exp", 0) + (exp - old)
                self.total_exp_gained += (exp - old)
            a["current_exp"] = exp; a["exp"] = exp
            if level: a["level"] = level

    def increment_match(self, uid):
        self.total_matches += 1
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["matches"] = self.accounts[uid].get("matches", 0) + 1
            self.accounts[uid]["last_match_time"] = datetime.now().strftime("%H:%M:%S")

    def increment_match_started(self): self.matches_started += 1

    def register_writer(self, uid, w): self.writers.setdefault(str(uid), []).append(w)

    def unregister_writer(self, uid, w):
        try: self.writers.get(str(uid), []).remove(w)
        except Exception: pass

    def close_writers_for_account(self, uid):
        for w in list(self.writers.get(str(uid), [])):
            try: w.close()
            except Exception: pass
        self.writers[str(uid)] = []

    def is_paused(self, uid): return str(uid) in self.paused

    def toggle_pause(self, uid, state):
        uid = str(uid)
        if state:
            self.paused.add(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = True
                self.accounts[uid]["status"] = "PAUSED"
        else:
            self.paused.discard(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = False
                if self.accounts[uid].get("status") == "PAUSED":
                    self.accounts[uid]["status"] = "ONLINE"

bot_state = BotState()

# ==================== TEAM STATE ====================
_team_states: Dict[str, dict] = {}
_team_states_lock = asyncio.Lock()

def get_team_state(group_id: str) -> dict:
    gid = str(group_id or "default")
    if gid not in _team_states:
        _team_states[gid] = {
            "peers": {}, "leader_uid": None, "team_code": None,
            "lock": asyncio.Lock(),
            "match_finished_uids": set(), "match_total_uids": set(),
            "cycle_count": 0}
    return _team_states[gid]

def drop_team_state(group_id: str):
    gid = str(group_id or "default")
    ts = _team_states.get(gid)
    if ts and not ts["peers"]: _team_states.pop(gid, None)

# ==================== PRINT ====================
class C:
    GREEN='\033[92m'; FAIL='\033[91m'; WARNING='\033[93m'
    CYAN='\033[96m'; MAGENTA='\033[95m'; WHITE='\033[97m'; ENDC='\033[0m'

def print_success(t): print(f"{C.GREEN}[+] {t}{C.ENDC}"); bot_state.log(t, "success")
def print_error(t):   print(f"{C.FAIL}[-] {t}{C.ENDC}");   bot_state.log(t, "error")
def print_warning(t): print(f"{C.WARNING}[!] {t}{C.ENDC}"); bot_state.log(t, "warning")
def print_info(t):    print(f"{C.CYAN}[i] {t}{C.ENDC}");   bot_state.log(t, "info")

GGRE_RAW = bytes.fromhex(
    "47475245010101006d020000b260ee08e1f86b4c57f9c70f86bba26ed5d1436bcf52e142db3249d905eded757764991ca31a8373cdd26eab91b80f3f1f6f262f4f10b895d7b6937ddba30a27197453890e9da49373f736c679b8254e2f8e1623e91084a5fdd5374fe478ff99e010834553fddeb0bec4018d142e49df9bb236675b67e852f92a43586f7a7d4d0d7a197a1d4da32714dab4d069ad53214e2c33b3877420a12459738c4c619cbd815fa878bbd104776bb3e1ac7818d5397b04a666ac57f682763ff2df31bc2f846ddc7904f3dce1bda0c4b01f9698e9166f98c84f92640abe3f6317834a42e5c12573b46842c1a6ea8fe6ca9c006dca48a2087e1f983dfb5692771e4a0b15b337ad669b1d08b40862b176bace5331b49a767375b1a8469012aa70a67b55fe71b72478201d0b3ac7269c064c960361e92ee7ba8a42cc6b582bf9b965fb388fa9172ad44c4b073ac23c02080a6bcd106b691ffdf4c7cf71e42f2063fcf196e9bddc5e85be1fe5048eb1b31b460efbb46d76195eef9904c4cba326f2e17ff51fec17dd965aa06dadd4ab07d6966e4a7c38e8afd66dfde56c872bb87516a8f7313c797e4d80e5ad4a5f7afad95c1e0449254adae052e71a3fb98399f93ab30848e0d23252dd45e6fd41bc5fa7303dfb846a8fd713a0032a0b0ae96dfba1bbe41d20abd8099e2cb7fccc329d25bd153029139ef05d090a5093ea557693c0a8d491395b8a23ca844b3887dd5dfc29ac06f4b9be87883a793211b973465e2644c4f5de02b8ab01571401203fc2740423826858cc6da0194c195d27aac4ec4b9d23d506c1501d06440aca3fc180926d75d4a004d3dff21eb4ea1e8c86e6c9627248eff953e1d192d5c8efc006a7e512388ef2ebdb72ee3ad42d719f28e8f994e12ebf4c79f2ffe3abd7408ccd2236a7b89b2606247a732c10c4"
)

def _encode_proto_std(fields):
    out = b""
    for f in sorted(fields.keys()):
        v = fields[f]
        if isinstance(v, bool):
            out += encode_varint((f << 3) | 0) + encode_varint(int(v))
        elif isinstance(v, int):
            out += encode_varint((f << 3) | 0) + encode_varint(v)
        elif isinstance(v, (str, bytes)):
            if isinstance(v, str): v = v.encode()
            out += encode_varint((f << 3) | 2) + encode_varint(len(v)) + v
    return out

async def major_register(release_v, access_token, open_id, name, game_version,
                          login_url, lang_code="en"):
    field14 = bytes(ord(c) ^ KEYSTREAM[i % 32] for i, c in enumerate(open_id))
    fields = {1: name, 2: access_token, 3: open_id,
        5: 102000007, 6: 4, 7: 1, 13: 1, 14: field14, 15: lang_code,
        16: 2, 20: game_version, 21: 1, 22: GGRE_RAW}
    proto = _encode_proto_std(fields)
    payload = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(proto, 16))
    url = f"{login_url.rstrip('/')}/MajorRegister"
    hdrs = {"Accept": "*/*", "Authorization": "Bearer ",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_v}",
        "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "X-GA": "v1 1", "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1"}
    try:
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as resp:
                content = await resp.read()
                if resp.status != 200: return None
                if not content: return None
                for off in [0, 64, 48, 32, 16]:
                    if off >= len(content): continue
                    try:
                        r = decode_protobuf_2(content[off:])
                        if r and 3 in r:
                            return {str(k): {"data": v} for k, v in r.items()}
                    except Exception: pass
                return None
    except Exception as e:
        print_error(f"[MAJOR-REG] {e}"); return None

# ==================== CLAN ====================
def _enc_clan_req(clan_id: int) -> Optional[bytes]:
    try:
        msg = infoClan_pb2.GuildReq()
        msg.guildId = int(clan_id); msg.garena = 1
        raw = msg.SerializeToString()
        return AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(raw, AES.block_size))
    except Exception as e:
        print_error(f"[CLAN-ENC] {e}"); return None

def _decode_repeated(data: bytes) -> list:
    results = []; offset = 0; data_len = len(data)
    while offset < data_len:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            value = data[offset:offset+length]; offset += length
            if fn == 1: results.append(decode_protobuf_2(value))
        elif wt == 0: _, offset = decode_varint(data, offset)
        elif wt == 1: offset += 8
        elif wt == 5: offset += 4
        else: break
    return results

async def get_clan_info(jwt_token: str, clan_id: str) -> Optional[Dict]:
    if not _CLAN_PB_AVAILABLE: return None
    payload = _enc_clan_req(int(clan_id))
    if not payload: return None
    ssl_ctx = ssl.create_default_context()
    ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
    hdrs_main = {"User-Agent":"UnityPlayer/2022.3.47f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "Accept":"*/*","Accept-Encoding":"deflate, gzip",
        "Authorization":f"Bearer {jwt_token}",
        "Content-Type":"application/x-www-form-urlencoded",
        "X-GA":"v1 1","X-GA-SV":str(int(time.time())),
        "ReleaseVersion":"OB55","X-Unity-Version":"2022.3.47f1",
        "Host":"clientbp.ppmainecoonghj.com"}
    hdrs_members = {**hdrs_main,
        "User-Agent":"UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "X-Unity-Version":"2018.4.12f1"}
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as s:
            clan_info_result = {}
            async with s.post("https://clientbp.ppmainecoonghj.com/GetClanMainPageInfo",
                              headers=hdrs_main, data=payload, ssl=ssl_ctx) as r:
                if r.status == 200:
                    binary = await r.read()
                    if binary and len(binary) >= 10:
                        raw = decode_protobuf_2(binary)
                        guild = raw.get(1, {})
                        if isinstance(guild, dict):
                            clan_info_result = {
                                "clan_id":      int(guild.get(1, int(clan_id)) or int(clan_id)),
                                "clan_name":    str(guild.get(2, "") or ""),
                                "leader_uid":   int(guild.get(4, 0) or 0),
                                "region":       str(guild.get(13, "") or ""),
                                "level":        int(guild.get(5, 0) or 0),
                                "capacity":     int(guild.get(6, 0) or 0),
                                "member_count": int(guild.get(7, 0) or 0),
                                "honor_points": int(guild.get(39, 0) or 0),
                                "weekly_glory": int(guild.get(37, 0) or 0),
                                "total_glory":  int(guild.get(36, 0) or 0)}
            members = []
            async with s.post("https://clientbp.ppmainecoonghj.com/GetClanMembers",
                              headers=hdrs_members, data=payload, ssl=ssl_ctx) as r:
                if r.status == 200:
                    binary = await r.read()
                    if binary and len(binary) >= 10:
                        for m in _decode_repeated(binary):
                            if not isinstance(m, dict): continue
                            try:
                                basic = m.get(1, {}) if isinstance(m.get(1, {}), dict) else {}
                                uid = int(basic.get(1, 0) or 0)
                                nickname = str(basic.get(3, "") or "")
                                region = str(basic.get(5, "") or "")
                                level = int(basic.get(6, 0) or 0)
                                role_v = int(m.get(4, 1) or 1)
                                weekly = int(m.get(11, 0) or 0)
                                total = int(m.get(10, 0) or 0)
                                role = {3:"leader",2:"co-leader",1:"member"}.get(role_v,"member")
                                if uid:
                                    members.append({"uid": uid, "nickname": nickname, "level": level,
                                        "region": region, "weekly_glory": weekly,
                                        "total_glory": total, "role": role})
                            except Exception: continue
                        members.sort(key=lambda x: x["weekly_glory"], reverse=True)
        if not clan_info_result:
            clan_info_result = {"clan_id": int(clan_id), "clan_name": "", "leader_uid": 0,
                "region": "BD", "level": 0, "capacity": 0, "member_count": len(members),
                "honor_points": 0, "weekly_glory": 0, "total_glory": 0,
                "has_bot": False, "bot_count": 0, "bots": []}
        bot_uids = set()
        try:
            for t in load_all_team_files():
                if str(t["clan_id"]) == str(clan_id):
                    for a in t["accounts"]:
                        auth_uid = str(a["uid"])
                        game_uid = bot_state.auth_to_game_id.get(auth_uid, auth_uid)
                        try: bot_uids.add(int(game_uid))
                        except Exception: pass
        except Exception: pass
        bots_list = []
        for m in members:
            if m["uid"] in bot_uids:
                m["is_bot"] = True
                bots_list.append({"uid": m["uid"], "nickname": m["nickname"],
                    "level": m["level"], "region": m["region"], "role": m["role"],
                    "weekly_glory": m["weekly_glory"], "total_glory": m["total_glory"]})
            else: m["is_bot"] = False
        clan_info_result["has_bot"] = len(bots_list) > 0
        clan_info_result["bot_count"] = len(bots_list)
        clan_info_result["bots"] = bots_list
        clan_info_result["member_count"] = len(members) or clan_info_result["member_count"]
        return clan_info_result
    except Exception as e:
        print_error(f"[CLAN-INFO] {e}"); return None

# ==================== TEAM FILES ====================
def _generate_group_id() -> str:
    return f"{random.randint(10000000, 99999999)}"

def _team_file_path(group_id: str) -> str:
    safe_id = re.sub(r'[^0-9A-Za-z_]', '', str(group_id))
    return os.path.join(TEAMS_DIR, f"group_{safe_id}.json")

def save_team_file(clan_id: str, region: str, accounts: List[Dict],
                   group_id: Optional[str] = None) -> Optional[str]:
    try:
        os.makedirs(TEAMS_DIR, exist_ok=True)
        if not group_id:
            for _ in range(10):
                gid = _generate_group_id()
                if not os.path.exists(_team_file_path(gid)):
                    group_id = gid; break
            else: group_id = _generate_group_id()
        data = {"group_id": str(group_id), "clan_id": str(clan_id),
            "region": str(region).upper(), "created_at": datetime.now().isoformat(),
            "accounts": [{"nickname": str(a.get("nickname","")),
                "account_id": str(a.get("account_id","")),
                "uid": str(a["uid"]), "password": str(a["password"])} for a in accounts]}
        path = _team_file_path(group_id)
        with open(path, "w", encoding="utf-8") as f: json.dump(data, f, indent=2)
        print_success(f"[TEAM-FILE] Saved {path} ({len(accounts)} accounts)")
        return str(group_id)
    except Exception as e:
        print_error(f"[TEAM-FILE] save error: {e}"); return None

def load_all_team_files() -> List[Dict]:
    teams = []
    if not os.path.isdir(TEAMS_DIR): return teams
    for fname in sorted(os.listdir(TEAMS_DIR)):
        if not fname.endswith(".json"): continue
        path = os.path.join(TEAMS_DIR, fname)
        try:
            with open(path, "r", encoding="utf-8") as f: data = json.load(f)
            if not isinstance(data, dict): continue
            clan_id = str(data.get("clan_id", "")).strip()
            group_id = str(data.get("group_id", "")).strip() or fname.replace("group_","").replace(".json","")
            accounts = data.get("accounts", [])
            region = str(data.get("region", "BD")).upper()
            if not clan_id or not isinstance(accounts, list) or not accounts: continue
            clean = []
            for a in accounts:
                if not isinstance(a, dict): continue
                u = str(a.get("uid", "")).strip(); p = str(a.get("password", "")).strip()
                if u and p: clean.append({"uid": u, "password": p})
            if not clean: continue
            teams.append({"clan_id": clan_id, "group_id": group_id,
                "region": region, "file": fname, "accounts": clean})
        except Exception as e:
            print_error(f"[TEAM-FILE] Failed to read {fname}: {e}")
    return teams

def delete_team_file(group_id: str) -> bool:
    try:
        path = _team_file_path(group_id)
        if os.path.exists(path): os.remove(path); return True
        return False
    except Exception as e:
        print_error(f"[TEAM-FILE] delete error: {e}"); return False

# ==================== DEVICE / DNS ====================
def _generate_new_device() -> dict:
    device_list = [("Samsung","SM-G998B","Adreno (TM) 660","Android OS 12 / API-31"),
        ("Xiaomi","2201122G","Adreno (TM) 730","Android OS 13 / API-33"),
        ("Realme","RMX3700","Mali-G710","Android OS 14 / API-34"),
        ("OnePlus","CPH2451","Adreno (TM) 740","Android OS 13 / API-33"),
        ("OPPO","CPH2611","Adreno (TM) 720","Android OS 14 / API-34")]
    brand, model, gpu, os_ver = random.choice(device_list)
    return {"unique_device_id":f"Google|{uuid.uuid4()}","brand":brand,"model":model,
        "gpu_renderer":gpu,"system_software":os_ver,
        "screen_width":random.choice([1080,1440,720]),
        "screen_height":random.choice([2400,3200,1600]),
        "screen_dpi":str(random.randint(300,420)),"memory":random.randint(2800,6500)}

def get_device_for_account(acc_key: str) -> dict:
    devices = {}
    if os.path.exists(DEVICES_FILE):
        try:
            with open(DEVICES_FILE,"r",encoding="utf-8") as f:
                devices = json.load(f)
                if not isinstance(devices, dict): devices = {}
        except Exception: devices = {}
    if acc_key in devices: return devices[acc_key]
    nd = _generate_new_device(); devices[acc_key] = nd
    try:
        with open(DEVICES_FILE,"w",encoding="utf-8") as f: json.dump(devices, f, indent=2)
    except Exception: pass
    return nd

_DNS_CACHE: Dict[str, Tuple[str,float]] = {}
_DNS_CACHE_TTL = 300.0

async def resolve_host_cloudflare(hostname: str) -> str:
    if not hostname: return hostname
    parts = hostname.split('.')
    if len(parts)==4 and all(p.isdigit() for p in parts): return hostname
    now = time.time()
    if hostname in _DNS_CACHE:
        ip, exp = _DNS_CACHE[hostname]
        if now < exp: return ip
    try:
        loop = asyncio.get_running_loop()
        info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
        if info:
            ip = info[0][4][0]
            _DNS_CACHE[hostname] = (ip, now + _DNS_CACHE_TTL)
            return ip
    except Exception: pass
    return hostname

def optimize_tcp_socket(sock):
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception: pass

async def safe_close_writer(writer):
    if not writer: return
    try:
        if not writer.is_closing(): writer.close()
        await asyncio.wait_for(writer.wait_closed(), timeout=1.5)
    except Exception: pass

def optimize_udp_socket(sock):
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception: pass

# ==================== HTTP CLIENT ====================
client = httpx.AsyncClient(verify=False, timeout=15.0,
    limits=httpx.Limits(max_connections=300, max_keepalive_connections=150))
_LOGIN_SEMAPHORE = asyncio.Semaphore(4)

# ==================== CRYPTO / PROTOBUF ====================
CRC7_TABLE = bytes([
    0,9,18,27,36,45,54,63,72,65,90,83,108,101,126,119,
    25,16,11,2,61,52,47,38,81,88,67,74,117,124,103,110,
    50,59,32,41,22,31,4,13,122,115,104,97,94,87,76,69,
    43,34,57,48,15,6,29,20,99,106,113,120,71,78,85,92,
    100,109,118,127,64,73,82,91,44,37,62,55,8,1,26,19,
    125,116,111,102,89,80,75,66,53,60,39,46,17,24,3,10,
    86,95,68,77,114,123,96,105,30,23,12,5,58,51,40,33,
    79,70,93,84,107,98,121,112,7,14,21,28,35,42,49,56,
    65,72,83,90,101,108,119,126,9,0,27,18,45,36,63,54,
    88,81,74,67,124,117,110,103,16,25,2,11,52,61,38,47,
    115,122,97,104,87,94,69,76,59,50,41,32,31,22,13,4,
    106,99,120,113,78,71,92,85,34,43,48,57,6,15,20,29,
    37,44,55,62,1,8,19,26,109,100,127,118,73,64,91,82,
    60,53,46,39,24,17,10,3,116,125,102,111,80,89,66,75,
    23,30,5,12,51,58,33,40,95,86,77,68,123,114,105,96,
    14,7,28,21,42,35,56,49,70,79,84,93,98,107,112,121,
])
_DELTA = 0x9E3779B9
_ROUNDS = 16

def crc7_sync(data: bytes) -> int:
    c = 0
    for b in data:
        c = CRC7_TABLE[((2*(c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F

def encode_varint(n: int) -> bytes:
    out = bytearray()
    if n < 0: n &= 0xFFFFFFFFFFFFFFFF
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)

def _pb_varint(fn, val): return encode_varint((fn<<3)|0) + encode_varint(val)
def _pb_length(fn, val):
    enc = val.encode('utf-8') if isinstance(val,str) else val
    return encode_varint((fn<<3)|2) + encode_varint(len(enc)) + enc

def create_proto(fields) -> bytes:
    packet = bytearray()
    for field, value in fields.items():
        if isinstance(field, str): field = int(field)
        if isinstance(value, dict):
            packet.extend(_pb_length(field, bytes(create_proto(value))))
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict):
                    packet.extend(_pb_length(field, bytes(create_proto(item))))
                elif isinstance(item, str):
                    packet.extend(_pb_length(field, item))
                elif isinstance(item, (bytes, bytearray)):
                    packet.extend(_pb_length(field, bytes(item)))
                elif isinstance(item, bool):
                    packet.extend(_pb_varint(field, 1 if item else 0))
                elif isinstance(item, int):
                    packet.extend(_pb_varint(field, item))
        elif isinstance(value, bool):
            packet.extend(_pb_varint(field, 1 if value else 0))
        elif isinstance(value, int):
            packet.extend(_pb_varint(field, value))
        elif isinstance(value, str):
            packet.extend(_pb_length(field, value))
        elif isinstance(value, (bytes, bytearray)):
            packet.extend(_pb_length(field, bytes(value)))
    return bytes(packet)

def encrypt_aes(hex_data: str) -> str:
    cipher = AES.new(AES_KEY, AES.MODE_CBC, AES_IV)
    return cipher.encrypt(pad(bytes.fromhex(hex_data), AES.block_size)).hex()

def decode_varint(data, offset):
    result = 0; shift = 0
    while offset < len(data):
        byte = data[offset]
        result |= (byte & 0x7F) << shift
        offset += 1
        if not (byte & 0x80): return result, offset
        shift += 7
    return None, offset

def decode_protobuf_2(data):
    result = {}; offset = 0; data_len = len(data)
    while offset < data_len:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            value = data[offset:offset+length]; offset += length
            try:
                s = value.decode('utf-8')
                result[fn] = s if s else value.hex()
            except UnicodeDecodeError:
                nested = decode_protobuf_2(value)
                result[fn] = nested if nested else value.hex()
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def extract_raw_fields(data: bytes) -> dict:
    result = {}; offset = 0; data_len = len(data)
    while offset < data_len:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            if offset + length > data_len: break
            result[fn] = bytes(data[offset:offset+length]); offset += length
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def _parse_results_sync(results):
    out = {}
    for r in results:
        fd = {"wire_type": r.wire_type}
        if r.wire_type == "varint": fd["data"] = r.data
        elif r.wire_type in ("string","bytes"): fd["data"] = r.data
        elif r.wire_type == "length_delimited":
            if hasattr(r.data, "results"): fd["data"] = _parse_results_sync(r.data.results)
            elif isinstance(r.data, list): fd["data"] = _parse_results_sync(r.data)
            else: fd["data"] = str(r.data)
        out[str(r.field)] = fd
    return out

def decode_protobuf_dict(data: bytes) -> dict:
    try:
        parsed = Parser().parse(data)
        return _parse_results_sync(parsed)
    except Exception: return {}

async def decode_protobuf_async(data):
    try:
        parsed = Parser().parse(data)
        return json.dumps(_parse_results_sync(parsed))
    except Exception: return "{}"

# ==================== ZIGZAG / ULEB ====================
def zigzag_encode(n: int) -> bytes:
    z = (n << 1) if n >= 0 else ((-n) << 1) - 1
    return encode_varint(z)

def uleb_encode(n: int) -> bytes: return encode_varint(n)

def create_packet(Pk, N, K, V):
    if isinstance(K, str): K = bytes.fromhex(K) if len(K)==32 else K.encode()
    if isinstance(V, str): V = bytes.fromhex(V) if len(V)==32 else V.encode()
    PkEnc = AES.new(K, AES.MODE_CBC, V).encrypt(pad(bytes.fromhex(Pk),16)).hex()
    L = len(PkEnc)//2
    hexlen = hex(L)[2:]
    if len(hexlen)%2 != 0: hexlen = '0'+hexlen
    total_pad = 12 - len(N) - len(hexlen)
    if total_pad < 0: total_pad = 0
    return bytes.fromhex(N + ('0'*total_pad) + hexlen + PkEnc)

# ==================== TEAM PACKETS ====================
def create_team(key, iv, game_version="1.132.9", mode=15):
    fields = {1: 1, 2: {2: bytes.fromhex("01"), 3: mode, 4:3, 5:"en",
        8: {1:"IDC3",2:123,3:"BD"}, 9:1,
        10: bytes.fromhex("01090a0b1219202729"), 11:2, 13:1,
        14: {1:"08FBA33B4BABE2790205390333330000009700050092005F72697EB2134DCBB2467625142201040e38e848dc0e748c3f6aa04d81000000ff1113090dcacfa16d",
             2:478, 3:"7e585d55", 4:"y[Z]", 6:12, 7:"15686677735a7506101c",
             8:str(game_version), 9:3, 10:1, 11:"03626253513637754174"},
        19: 329, 21: bytes.fromhex("374f521955"), 24:{1:21},
        27:"a_6534489873065906362"}}
    return create_packet(create_proto(fields).hex(), "0514", key, iv)

def team_fresh(account_id, key, iv):
    return create_packet(create_proto({1:72, 2:{1:int(account_id)}}).hex(), "0514", key, iv)

def invite_player_in_team(target_uid, key, iv):
    return create_packet(create_proto({1:2, 2:{1:int(target_uid),2:"BD",4:1}}).hex(), "0514", key, iv)

def accept_team_invite(target_uid, group_id, key, iv):
    fields = {1:4, 2:{1:int(target_uid), 3:int(target_uid),
        4: bytes.fromhex("0107090a0b120f19202729"), 8:1,
        9: {1:"08FBA33B0522052002041B0222220007000C00010004000547E265AE1080779546762514110104076fa2e8770e748c3f6a68ed75000000ff08080500cacfa16d",
            2:235, 3:{14:80,11:86}, 4:"{Y\\R", 6:13, 7:{2:4},
            8:"1.132.9", 9:2, 10:1, 11:"0362625351"},
        10: str(group_id),
        11: {"1":"IDC3","2":107,"3":"BD"}, 13:"en", 16:"374f5219",
        20:{1:21}, 23:"a_6534489873065906362",
        24:"https://dl-sg-production.freefiremobile.com/",
        27:{1:2, 2:4}}}
    return create_packet(create_proto(fields).hex(), "0514", key, iv)

def start_match_team(account_id, key, iv, region="BD", mode=15):
    fields = {1: 9, 2: {1: int(account_id), 3: mode, 7: {1: "IDC3", 2: 410, 3: region}}}
    return create_packet(create_proto(fields).hex(), "0514", key, iv)

def ready_for_game(uid, key, iv):
    fields = {1: 15, 2: {1: uid, 2: 1}}
    return create_packet(create_proto(fields).hex(), "0514", key, iv)

# ==================== KEY EXTRACT ====================
def _extract_key_iv(res_json):
    if "__RAW_HEX__" in res_json and "__OFFSET__" in res_json:
        try:
            raw = bytes.fromhex(res_json["__RAW_HEX__"])
            off = int(res_json["__OFFSET__"])
            rf = extract_raw_fields(raw[off:])
            for kf, vf in [(22,23),(24,25),(6,7)]:
                k = rf.get(kf); v = rf.get(vf)
                if isinstance(k,(bytes,bytearray)) and len(k)==16 and \
                   isinstance(v,(bytes,bytearray)) and len(v)==16:
                    return bytes(k), bytes(v)
        except Exception: pass
    found = {}
    for k, v in res_json.items():
        if str(k).startswith("__"): continue
        if not isinstance(v, dict): continue
        data = v.get("data")
        if data is None: continue
        raw = None
        if isinstance(data, (bytes,bytearray)) and len(data)==16: raw = bytes(data)
        elif isinstance(data, str) and len(data)==32:
            try:
                c = bytes.fromhex(data)
                if len(c)==16: raw = c
            except Exception: pass
        if raw and len(raw)==16:
            try: found[int(k)] = raw
            except Exception: pass
    if len(found) < 2: return None, None
    for kf, vf in [(22,23),(24,25),(6,7)]:
        if kf in found and vf in found: return found[kf], found[vf]
    sk = sorted(found.keys())
    return found[sk[0]], found[sk[1]]

async def aes_encrypt(payload, key, iv):
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(payload, AES.block_size))

# ==================== VERSION / LOGIN ====================
def get_app_version():
    try: return play_scraper('com.dts.freefireth').get('version')
    except Exception: return "1.132.9"

async def version_config(region="BD"):
    app_version = get_app_version()
    lang = REGION_LANG.get(region.upper(), "en")
    url = (f"https://version.ggwhitehawk.com/live/ver.php?version={app_version}"
           f"&lang={lang}&device=android&channel=android&appstore=googleplay"
           f"&region={region.upper()}&whitelist_version=1.3.0&whitelist_sp_version=1.0.0")
    try:
        r = await client.get(url); j = r.json()
        server_url = j.get("server_url")
        remote_version = j.get("remote_version")
        latest_release_version = j.get("latest_release_version")
        gops = [u.strip() for u in j.get("gop_url","").split(";") if u.strip()]
        gop_1 = gops[0] if gops else "https://ffmconnect.ppmainecoonghj.com"
        if not server_url: return None
        return latest_release_version, remote_version, server_url, gop_1, app_version
    except Exception as e:
        print_error(f"[VERCONFIG] {e}"); return None

async def get_access_token(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {"Host":"100067.connect.garena.com",
        "User-Agent":"Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B)",
        "Content-Type":"application/x-www-form-urlencoded",
        "Accept-Encoding":"gzip, deflate, br","Connection":"close"}
    data = {"uid":str(uid),"password":password,"response_type":"token","client_type":"2",
        "client_secret":HEX_KEY,"client_id":"100067"}
    for _ in range(4):
        try:
            r = await client.post(url, headers=hdrs, data=data)
            if r.status_code == 200:
                j = r.json()
                oid = j.get("open_id"); at = j.get("access_token"); pf = j.get("platform",4)
                if oid and at: return oid, at, pf
        except Exception: pass
        await asyncio.sleep(0.7)
    return None

def generate_signature(payload_str):
    return hmac.new(API_KEY, payload_str.encode(), hashlib.sha256).hexdigest()

async def register_account(password, gop_url, app_version):
    connector = aiohttp.TCPConnector(resolver=aiohttp.ThreadedResolver())
    rp = {"app_id":100067,"client_type":2,"password":password,"source":2}
    payload = json.dumps(rp, separators=(',',':'))
    sig = generate_signature(payload)
    headers = {"User-Agent": f"GarenaMSDK/4.0.44(SM-E135F ;Android 14;en;GB;app {app_version} 2019118525;)",
        "Authorization": f"Signature {sig}", "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8"}
    try:
        async with aiohttp.ClientSession(connector=connector) as s:
            async with s.post(f"{gop_url}/api/v2/oauth/guest:register",
                              headers=headers, data=payload,
                              timeout=aiohttp.ClientTimeout(total=15)) as resp:
                data = json.loads(await resp.text())
                if data.get("code") == 0: return data["data"]["uid"]
    except Exception as e:
        print_error(f"[REGISTER] {e}")
    return None

async def grant_token(uid, password, gop_url, app_version):
    result = await get_access_token(uid, password)
    if not result: return None
    oid, at, pf = result
    return {"open_id": oid, "access_token": at, "platform": pf}

async def get_payload(access_token, open_id, platform, version, lang_code="en"):
    device_id = f"Google|{uuid.uuid4()}"
    major_login = {
        "3": str(datetime.now())[:-7], "4": "free fire", "5": 1,
        "7": f"{version}", "8": "Android OS 14 / API-34 (UP1A.231005.007/E135FXXSEEZE2)",
        "9": "Handheld", "11": "CarrierDataNetwork",
        "12": 1672, "13": 750, "14": "338", "15": "ARMv7 VFPv3 NEON | 2002 | 8",
        "16": 3702, "17": "Mali-G52",
        "18": "OpenGL ES 3.2 v1.r38p1-01bet0-mbs2v41_0.6d20ec041e51b2f2d25dfc265586ebe8",
        "19": device_id, "20": "104.28.197.151", "21": lang_code,
        "22": f"{open_id}", "23": f"{platform}", "24": "Handheld",
        "25": "samsung SM-E135F", "26": "BD",
        "29": f"{access_token}", "30": 1, "42": "Cellular",
        "57": "7428b253defc164018c604a1ebbfebdf",
        "60": 52037, "61": 5355, "62": 3723, "63": 3,
        "64": 5483, "65": 52037, "66": 5483, "67": 52037, "73": 2,
        "74": "/data/app/~~yACsV8QOk9OexgajWQP30A==/com.dts.freefireth-Bi_wPVrrhYM2nYncc29q7Q==/lib/arm",
        "76": 1, "77": "b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~yACsV8QOk9OexgajWQP30A==/com.dts.freefireth-Bi_wPVrrhYM2nYncc29q7Q==/base.apk",
        "78": 3, "79": 1, "81": "32", "83": "2019121229",
        "86": "OpenGLES2", "87": 8191, "88": int(platform),
        "92": 16091, "93": "android",
        "94": "KqsHT3Yeqo3RLRl8efNiL3aL/1SHwlSrtK0DwNAqdkNBQz70TeVy+icaIwuR3UK4b65Uf3IG5xBFEv0uu+jQZI+rOYCmNCsXjJT4QcZaYgoaaUGG",
        "95": 111107, "96": "{\"cur_rate\":null,\"support_etc2\":false}",
        "97": 1, "98": 1, "99": f"{platform}", "100": f"{platform}",
        "102": "4503454457550c0766", "104": 53792, "105": 1,
        "106": "https://dl-bs.ggpolarbear.com/live/ABHotUpdates/|https://core-bs.ggpolarbear.com/live/ABHotUpdates/|6b2078db9d22dd98f8e9386a39af8462",
        "107": "c8e41b7a93f02d56e1a94c7b8203f5d1"}
    get_login_data = dict(major_login)
    get_login_data["90"] = "Khulna"; get_login_data["91"] = "D"
    get_login_data["99"] = "0"; get_login_data["103"] = 1
    proto1 = create_proto(major_login).hex()
    proto2 = create_proto(get_login_data).hex()
    return bytes.fromhex(encrypt_aes(proto1)), bytes.fromhex(encrypt_aes(proto2))

async def major_login(payload, login_url, release_version):
    url = f"{login_url.rstrip('/')}/MajorLogin"
    req_headers = {"Accept": "*/*", "Authorization": "Bearer ",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_version}",
        "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "X-GA": "v1 1", "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1"}
    try:
        ssl_context = ssl.create_default_context()
        ssl_context.check_hostname = False
        ssl_context.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
            async with session.post(url, headers=req_headers, data=payload, ssl=ssl_context) as response:
                response_content = await response.read()
                print_info(f"[MAJOR-LOGIN] status={response.status} len={len(response_content)}")
                if response.status != 200: return None
                if len(response_content) < 200: return None
                best = None; best_score = -1; best_off = 0
                for offset in [64,0,48,32,80,16,128,8,96,60,56,40,24,20,12,4]:
                    if offset >= len(response_content): continue
                    cb = response_content[offset:]
                    cand = None
                    try: cand = decode_protobuf_dict(cb)
                    except Exception: cand = None
                    if not cand:
                        try:
                            c2 = decode_protobuf_2(cb)
                            if c2: cand = {str(k): {"data": v} for k, v in c2.items()}
                        except Exception: cand = None
                    if not cand: continue
                    keys = set(cand.keys())
                    has_jwt = ("8" in keys) or (8 in keys)
                    has_url = ("10" in keys) or (10 in keys)
                    score = len(cand) + (100 if has_jwt else 0) + (50 if has_url else 0)
                    if score > best_score:
                        best = cand; best_score = score; best_off = offset
                    if has_jwt and has_url: break
                if not best: return None
                if ("8" not in best) and (8 not in best): return None
                best["__RAW_HEX__"] = response_content.hex()
                best["__OFFSET__"] = best_off
                return best
    except Exception as e:
        print_error(f"[MAJOR-LOGIN] {e}"); return None

async def get_login_data(payload, jwt_token, server_url, release_version):
    url = f"{server_url.rstrip('/')}/GetLoginData"
    hdrs = {"Accept":"*/*","Authorization":f"Bearer {jwt_token}",
        "Content-Type":"application/x-www-form-urlencoded",
        "ReleaseVersion":f"{release_version}",
        "User-Agent":"UnityPlayer/2018.4.12f1","X-GA":"v1 1",
        "X-GA-SV":str(int(time.time())),"X-Unity-Version":"2018.4.12f1"}
    try:
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                if r.status != 200: return None
                content = await r.read()
                for off in [0,64,48,32,80,16,128,8,96]:
                    if off >= len(content): continue
                    try:
                        c = decode_protobuf_dict(content[off:])
                        if c and len(c) >= 3: return c
                    except Exception: pass
                for off in [0,64,48,32,80]:
                    if off >= len(content): continue
                    c = decode_protobuf_2(content[off:])
                    if c and len(c) >= 3: return {str(k):{"data":v} for k,v in c.items()}
        return None
    except Exception: return None

async def get_player_personal_show(target_uid, jwt_token, server_url, release_version):
    url = f"{server_url}/GetPlayerPersonalShow"
    payload = bytes.fromhex(encrypt_aes(create_proto({"1":int(target_uid)}).hex()))
    hdrs = {"authorization":f"Bearer {jwt_token}",
        "host":server_url.replace("https://","").split("/")[0],
        "x-ga":"v1 1","content-type":"application/x-www-form-urlencoded",
        "releaseversion":f"{release_version}",
        "user-agent":"UnityPlayer/2022.3.47f1","accept":"*/*",
        "x-unity-version":"2022.3.47f1"}
    try:
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                if r.status != 200: return None
                return decode_protobuf_2(await r.read())
    except Exception: return None

# ==================== BIO ====================
def _build_bio_proto(bio_text: str) -> bytes:
    pb = b"\x10\x07" + b"\x2a\x00" + b"\x32\x00"
    b = bio_text.encode("utf-8")[:AUTO_BIO_MAX_LEN]
    pb += b"\x42" + bytes([len(b)]) + b
    pb += b"\x48\x01" + b"\x5a\x00" + b"\x62\x00"
    return pb

def _decode_bio_proto(d: bytes) -> list:
    i, out = 0, []
    while i < len(d):
        try:
            t, i = decode_varint(d, i)
            if t is None: break
            f, w = t >> 3, t & 0x7
            e = {"field": f}
            if w == 0: e["val"], i = decode_varint(d, i)
            elif w == 2:
                ln, i = decode_varint(d, i)
                if ln is None: break
                p = d[i:i + ln]; i += ln
                if not p: e["val"] = []
                elif all(32 <= c < 127 for c in p): e["str"] = p.decode("ascii")
                else:
                    sub = _decode_bio_proto(p)
                    if sub: e["val"] = sub
                    else:
                        try: e["str"] = p.decode("utf-8")
                        except Exception: e["hex"] = p.hex()
            elif w == 5: e["val"] = int.from_bytes(d[i:i + 4], "little"); i += 4
            elif w == 1: e["val"] = int.from_bytes(d[i:i + 8], "little"); i += 8
            else: break
            out.append(e)
        except Exception: break
    return out

def _parse_bio_response(data: bytes, sent_bio: str) -> Dict[str, Any]:
    out = {"account_id": None, "status": None, "echoed_bio": None, "applied": False}
    for e in _decode_bio_proto(data):
        if e.get("field") == 1 and isinstance(e.get("val"), list):
            for s in e["val"]:
                if not isinstance(s, dict): continue
                f = s.get("field")
                if f == 1: out["account_id"] = s.get("val")
                if f == 3: out["status"] = s.get("val")
                if f == 9: out["echoed_bio"] = s.get("str")
                if f == 10: out["applied"] = (s.get("val") == 1)
    out["success"] = (out.get("echoed_bio") == sent_bio) and bool(out.get("applied"))
    return out

async def update_bio_auto(jwt_token: str, bio_text: str = AUTO_BIO_TEXT,
                          release_version: str = None,
                          server_url: str = None) -> Optional[Dict]:
    if not AUTO_BIO_ENABLED or not jwt_token: return None
    bio_text = (bio_text or "").strip()[:AUTO_BIO_MAX_LEN]
    if not bio_text: return None
    release_version = release_version or AUTO_BIO_RELEASE_VER
    proto = _build_bio_proto(bio_text)
    payload = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(proto, 16))
    url = AUTO_BIO_URL; host = "clientbp.ggpolarbear.com"
    if server_url:
        try:
            base = server_url.rstrip("/")
            if base:
                url = f"{base}/UpdateSocialBasicInfo"
                host = base.replace("https://", "").replace("http://", "").split("/")[0]
        except Exception: pass
    hdrs = {"User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "Accept": "*/*", "X-GA-SV": str(int(time.time())),
        "Authorization": f"Bearer {jwt_token}", "X-GA": "v1 1",
        "ReleaseVersion": f"{release_version}",
        "Content-Type": "application/x-www-form-urlencoded",
        "X-Unity-Version": "2018.4.12f1", "Host": host}
    try:
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                body = await r.read()
                if r.status != 200: return None
                return _parse_bio_response(body, bio_text)
    except Exception as e:
        print_warning(f"[BIO] {type(e).__name__}: {e}")
    return None

# ==================== CLAN JOIN ====================
def _get_region_from_jwt(jwt_token):
    try:
        p = jwt_token.split('.')[1]; p += '=' * (-len(p) % 4)
        d = json.loads(base64.urlsafe_b64decode(p))
        return (d.get('lock_region') or d.get('noti_region') or 'BD').upper()
    except Exception: return "BD"

def _get_region_url(region):
    region = region.upper()
    if region == "IND": return "https://client.ind.freefiremobile.com"
    if region in ["BR","US","NA"]: return "https://client.us.freefiremobile.com"
    return "https://clientbp.ggpolarbear.com"

def _create_clan_payload(clan_id):
    if not _CLAN_PB_AVAILABLE: return None
    try:
        msg = reqClan_pb2.MyMessage(); msg.field_1 = int(clan_id)
        raw = msg.SerializeToString()
        return AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(raw, AES.block_size))
    except Exception: return None

async def join_clan(jwt_token, clan_id):
    if not _CLAN_PB_AVAILABLE: return False
    try:
        region = _get_region_from_jwt(jwt_token)
        base_url = _get_region_url(region)
        url = base_url.rstrip("/") + "/RequestJoinClan"
        host = base_url.replace("https://","")
        payload = _create_clan_payload(clan_id)
        if not payload: return False
        hdrs = {"Authorization":f"Bearer {jwt_token}",
            "X-Unity-Version":"2018.4.11f1","X-GA":"v1 1","ReleaseVersion":"OB55",
            "Content-Type":"application/octet-stream","Host":host,
            "Connection":"Keep-Alive","Accept-Encoding":"gzip"}
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                return r.status == 200
    except Exception: return False

# ==================== TCP ====================
async def build_tcp_startup_packet(account_id, token, server_time, key, iv, region="BD", typ='OnLine'):
    uid_hex = f"{int(account_id):016x}"
    ts_hex = f"{int(server_time):08x}"
    enc = (await aes_encrypt(token.encode(), key, iv)).hex()
    enc_len = f"{len(enc)//2:08x}"
    reg = str(region).upper() if region else "BD"
    if typ == 'OnLine':
        pfx = '7219' if reg == 'BD' else ('7214' if reg == 'IND' else '7215')
        return f"{pfx}{uid_hex}{ts_hex}00000000{enc_len}{enc}"
    pfx = '8119' if reg == 'BD' else ('8114' if reg == 'IND' else '8115')
    return f"{pfx}{uid_hex}{ts_hex}{enc_len}{enc}"

async def send_keep_alive(region="BD"):
    reg = str(region).upper() if region else "BD"
    return bytes.fromhex("0219" if reg == "BD" else ("0214" if reg == "IND" else "0215"))

async def start_game_battle_royale(region, client_version, writer, key, iv):
    raw_proto_hex = (
        "080112960b0a0101100f3a0a0a04494443311a0242443a0a0a04494443321a0242443a0a0a044944"
        "43331a02424440014a0901090a0b1219202729580162a70a0a800130384642413333423433323244"
        "43323230323033323030313232323130303031303038453030303330303841303032344235383634"
        "39423431333032443742343436373632353134303030313034303765306130643834383065373438"
        "633366366161303439643430303030303066663038306130353031636163666131366410c6011ab9"
        "037e585c541303054d51000b5c545102560057050309525a0852070853030057550101545600000b"
        "051204014f7d5c4045491a051d04191009034c01567c77025a6842627e7a63494477675b79770e77"
        "08647b007c7c081302447b5d635174567c4f7f677f76565074744c5a7b515c5a5b51506345081253"
        "5f5d4c1e63791d754541044c646a6640014346504b594564134b7849470b6c7e7d5b466a1e46090d"
        "11040249085950785761007e7e45067e410f5e0066567e427f520502734b000c130a494502601c53"
        "62621e6a0b71426f5a405343795a49197b1a5a4840790c13034c197349517642174051597f5c6f43"
        "42435e5a030008644a05435c790e1b084c606973791e40646217505d687b484c7f707a1852690579"
        "43400005081302004d0700640a007370405d714943584261057a6655016c70797c6a7f7c0c16034f"
        "701a015563610475431b015e0558670553401a5a037413771b66000f160549564a7f50477b697304"
        "606c0541696876046346561e464a047f74750c1300054d447705135059437e5579435e65674a4345"
        "00074a7b0240597c4f700d12054e5a4746597b5e5f5b704250405c1e64745041537b61451a08616a"
        "440522047b5f5d5d300c3a1a1101404b4202020201041511647b7163746e7c5b57725d5550534207"
        "312e3133322e39480650015ab105036262535136334c707a475133416456324b796f566c6646484e"
        "4861775a57523441737574496d41506233706a4666667465554a722b7a58592b466f2f432f58304b"
        "526636765a7631747943545a6e77314f7a307a7a554532636561556f61552b41483563492b424a6d"
        "4234556d654b54776f4c34656569657a5345536c79332b6a627163486b4f4156456a4b2b634c4776"
        "3141652b68773749586f4e785137344d55716f544b4450557a4971564e584c463533764177563670"
        "6f684c47345738387a5132627739466773496a564a4b6a48397538796e55354f51305746632f434b"
        "764c2b6b31617a2b6977576e34397044386c4b775253453846714b6d6c5061395963474e456b646d"
        "55562f55446d643045334d74516c353230567a332b4c55754765344b5136653148336f69466f5647"
        "615058417a4a75474c6b62734a48412b537676504d4144416842676a502b364f6f49362b31445a59"
        "4664644371736a67546762436c5674555a466156726a3130617377584b7936744365503735353967"
        "57444b65586c6170745369495a73636d3376667051467165436252316c552f686639495163313634"
        "594d373553695a6765346979516c36514933434571556e754a4b426e635855523739303635654951"
        "624674377773546b6f6737384552786e6f4c484756392b59336662656d50316e4a3650385252394f"
        "673532587746706f3759646265556a6854666c4c4c6a415a782b4a696375694a2f685234652f676c"
        "7674553533585849374a373462543770677761377054766a66514b696530516a79654b466f72794b"
        "6255354f46386771616a3334644359616269335454704339435838326f36653462742f704a4a4458"
        "643855796a6757393075692b695a56434c703944775261737a6e7a567858654f3734617464413871"
        "4956477943524239467145575a77384b755a536339593da20105080310e802a201050804108703a2"
        "01050805109c01a20105081d10cc01a2010408161076a20105080e108b01a201020815")
    reg = str(region).upper() if region else "BD"
    pkt_prefix = '0319' if reg == 'BD' else ('0314' if reg == 'IND' else '0315')
    packet_bytes = bytes.fromhex(raw_proto_hex)
    encrypted_packet = (await aes_encrypt(packet_bytes, key, iv)).hex()
    packet_length = len(encrypted_packet) // 2
    final = bytes.fromhex(pkt_prefix + f"{packet_length:08x}" + encrypted_packet)
    writer.write(final); await writer.drain()

# ==================== MATCH COUNTERS ====================
_match_counters: Dict[str, int] = {}
_match_counter_lock = asyncio.Lock()

async def _inc_match(uid):
    async with _match_counter_lock:
        _match_counters[uid] = _match_counters.get(uid, 0) + 1
        return _match_counters[uid]

async def _dec_match(uid):
    async with _match_counter_lock:
        if uid in _match_counters and _match_counters[uid] > 0:
            _match_counters[uid] -= 1
        return _match_counters.get(uid, 0)

# ==================== TOKEN CACHE ====================
_token_cache_memo: Dict[str, Any] = {}
_token_cache_memo_time: float = 0.0
_TOKEN_CACHE_MEMO_TTL = 5.0

def _json_serializer(obj):
    if isinstance(obj, (bytes, bytearray)): return {"__bytes_hex__": bytes(obj).hex()}
    raise TypeError(f"Type {type(obj)} not serializable")

def _json_deserializer(obj):
    if isinstance(obj, dict):
        if "__bytes_hex__" in obj and len(obj) == 1:
            try: return bytes.fromhex(obj["__bytes_hex__"])
            except Exception: return b""
        return {k: _json_deserializer(v) for k, v in obj.items()}
    if isinstance(obj, list): return [_json_deserializer(x) for x in obj]
    return obj

def _load_token_cache() -> Dict[str, Any]:
    global _token_cache_memo, _token_cache_memo_time
    now = time.time()
    if _token_cache_memo and (now - _token_cache_memo_time) < _TOKEN_CACHE_MEMO_TTL:
        return _token_cache_memo
    if not os.path.exists(TOKEN_CACHE_FILE): return {}
    try:
        with open(TOKEN_CACHE_FILE,"r",encoding="utf-8") as f: content = f.read().strip()
        if not content: return {}
        data = json.loads(content); parsed = _json_deserializer(data)
        _token_cache_memo = parsed; _token_cache_memo_time = now
        return parsed
    except Exception:
        try: os.remove(TOKEN_CACHE_FILE)
        except Exception: pass
        return {}

def _save_token_cache(cache: Dict[str, Any]):
    global _token_cache_memo, _token_cache_memo_time
    try:
        tmp_file = TOKEN_CACHE_FILE + ".tmp"
        with open(tmp_file,"w",encoding="utf-8") as f:
            json.dump(cache, f, indent=2, default=_json_serializer)
        os.replace(tmp_file, TOKEN_CACHE_FILE)
        _token_cache_memo = cache; _token_cache_memo_time = time.time()
    except Exception as e:
        print_error(f"Token cache save error: {e}")

def cache_get(uid: str) -> Optional[Dict]:
    cache = _load_token_cache()
    entry = cache.get(str(uid))
    if not entry: return None
    if time.time() - entry.get("cached_at",0) > TOKEN_CACHE_TTL:
        cache_invalidate(uid); return None
    if str(entry.get("account_id","")).isdigit():
        entry["account_id"] = int(entry["account_id"])
    if not isinstance(entry.get("login_payload_data"), (bytes, bytearray)):
        cache_invalidate(uid); return None
    return entry

def cache_set(uid: str, data: Dict):
    try:
        cache = _load_token_cache(); entry = dict(data)
        entry["cached_at"] = time.time()
        cache[str(uid)] = entry
        _save_token_cache(cache)
    except Exception as e:
        print_error(f"cache_set error: {type(e).__name__}: {e}")

def cache_invalidate(uid: str):
    cache = _load_token_cache()
    if str(uid) in cache:
        del cache[str(uid)]; _save_token_cache(cache)

# ==================== PLAY ====================
async def play_game(server_ip_port, udp_jwt, udp_key, match_code,
                    account_id, player_region, client_version,
                    tcp_key, tcp_iv, match_index,
                    game_mode=1, map_id=1, match_mode=1, sleep_ms=0,
                    match_id=0, verbose=True):
    uid_str = str(account_id); completed_cleanly = False
    try:
        if ":" not in server_ip_port: return
        ip, port_s = server_ip_port.split(":", 1); port = int(port_s)
        print_success(f"[MATCH #{match_index}] → toolsudp {ip}:{port}")
        try: _toolsudp.set_base_url("https://clientbp.ppmainecoonghj.com")
        except Exception: pass
        loop = asyncio.get_running_loop()
        def _run():
            return _toolsudp.run_match(ip, port, int(account_id), udp_key, udp_jwt,
                match_code, "0", int(game_mode), int(map_id), int(match_mode),
                int(sleep_ms), 3.0, None, int(match_id), bool(verbose))
        try: await loop.run_in_executor(None, _run)
        except Exception as exc:
            print_error(f"[MATCH #{match_index}] {exc}"); traceback.print_exc()
        else:
            completed_cleanly = True
            print_success(f"[★] Match #{match_index} Finished")
    except Exception as e:
        print_error(f"[MATCH #{match_index}] {e}")
    finally:
        if completed_cleanly:
            try:
                bot_state.increment_match(uid_str)
                async def _post_exp(uid):
                    try:
                        for wait in (5.0, 8.0, 12.0):
                            await asyncio.sleep(wait); await refresh_account_profile(uid)
                    except Exception: pass
                asyncio.create_task(_post_exp(uid_str))
            except Exception: pass
        remaining = await _dec_match(uid_str)
        try:
            bot_state.update_status(uid_str, "ONLINE" if remaining == 0 else "IN_MATCH", remaining)
        except Exception: pass

# ==================== FUNCTIONAL LONE WOLF (PER-MATCH LOOP) ====================
async def functional_lone_wolf(addrs, starter_packet, account_region, client_version,
                                key, iv, account_id="", account_data=None,
                                max_reconnects=10, group_id: str = "default"):
    reconnects = 0
    ip, port = addrs.split(":")
    play_matches: List[asyncio.Task] = []
    no_response_count = 0
    search_attempts = 0
    last_start_time = 0.0
    uid_str = str(account_id)
    _match_cycle_count = 0

    current_token = starter_packet
    current_key = key
    current_iv = iv
    current_account_data = account_data
    _writer_ref = {"w": None}
    _team_active = {"flag": True}
    _match_played = {"flag": False}
    _should_reform = {"flag": False}

    _team_state = get_team_state(group_id)

    async def _process_social_packet(raw_bytes, tag="MAIN"):
        try:
            hex_data = raw_bytes.hex(); candidates = []
            if len(raw_bytes) >= 6:
                plen = raw_bytes[4]
                if 0 < plen <= (len(raw_bytes) - 5):
                    try:
                        inner = bytes(raw_bytes[5:5 + plen])
                        d0 = decode_protobuf_dict(inner)
                        if not d0:
                            a0 = decode_protobuf_2(inner)
                            if a0: d0 = {str(k): {"data": v} for k, v in a0.items()}
                        if d0: candidates.append((5, d0))
                    except Exception: pass
            for off in [5,6,10,8,12,14,4,16,0]:
                if off >= len(hex_data): continue
                try: inner_bytes = bytes.fromhex(hex_data[off:])
                except Exception: continue
                decoded = None
                try:
                    d1 = decode_protobuf_dict(inner_bytes)
                    if d1: decoded = d1
                except Exception: pass
                if not decoded:
                    try:
                        d2 = decode_protobuf_2(inner_bytes)
                        if d2: decoded = {str(k): {"data": v} for k, v in d2.items()}
                    except Exception: pass
                if decoded: candidates.append((off, decoded))
            if not candidates: return
            def _score(item):
                _off, d = item; s = len(d)
                if "0" in d or 0 in d: s -= 100
                if "5" in d: s += 6
                if "1" in d: s += 4
                if "2" in d: s += 2
                return s
            candidates.sort(key=_score, reverse=True)
            best_off, decoded = candidates[0]
            def _val(c, k):
                if not isinstance(c, dict): return None
                v = c.get(k) if k in c else c.get(str(k))
                if isinstance(v, dict) and "data" in v: return v["data"]
                return v
            f5wrap = decoded.get("5") or decoded.get(5)
            f5 = None
            if isinstance(f5wrap, dict) and "data" in f5wrap: f5 = f5wrap["data"]
            elif isinstance(f5wrap, dict): f5 = f5wrap
            target_uid = None
            if isinstance(f5, dict):
                for fk in [1,2,3,4,6]:
                    cand = _val(f5, fk)
                    if cand and str(cand).isdigit() and 6 <= len(str(cand)) <= 15:
                        target_uid = str(cand); break
            if not target_uid:
                for fk in [1,2,3]:
                    cand = _val(decoded, fk)
                    if cand and str(cand).isdigit() and 6 <= len(str(cand)) <= 15:
                        target_uid = str(cand); break
            if not target_uid: return
            own_acc = str(current_account_data.get('account_id', '')) if current_account_data else None
            if own_acc and target_uid == own_acc: return
            if not _accept_friend_request or not current_account_data: return
            jwt_l = current_account_data.get('token'); srv_l = current_account_data.get('server_url')
            rel_l = current_account_data.get('release_version'); own_id = current_account_data.get('account_id')
            if not (jwt_l and srv_l and rel_l and own_id): return
            url = f"{srv_l.rstrip('/')}/ConfirmFriendRequest"
            fields = {"1": int(target_uid), "2": int(own_id)}
            try:
                payload = bytes.fromhex(encrypt_aes(create_proto(fields).hex()))
                hdrs = {"authorization": f"Bearer {jwt_l}",
                    "host": srv_l.replace("https://", "").replace("http://", "").split("/")[0],
                    "x-ga": "v1 1", "content-type": "application/x-www-form-urlencoded",
                    "accept-encoding": "deflate, gzip", "releaseversion": f"{rel_l}",
                    "user-agent": "UnityPlayer/2022.3.47f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
                    "accept": "*/*", "x-unity-version": "2022.3.47f1"}
                ssl_ctx = ssl.create_default_context()
                ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
                async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8)) as s:
                    async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                        if r.status == 200:
                            print_success(f"[FRIEND-{tag}] ✅ Accepted {target_uid}")
            except Exception: pass
        except Exception: pass

    async def _team_coordinator():
        try:
            while True:
                async with _team_state["lock"]:
                    n = len(_team_state["peers"])
                if n >= TEAM_SIZE: break
                if bot_state.is_paused(uid_str): return
                await asyncio.sleep(0.5)
            await asyncio.sleep(TEAM_READY_DELAY)
            async with _team_state["lock"]:
                is_leader = (_team_state["leader_uid"] == uid_str)
                peers_snapshot = dict(_team_state["peers"])
            if not is_leader: return
            async with _team_state["lock"]:
                _team_state["team_code"] = None
            own_id_num = current_account_data.get('account_id') if current_account_data else 0
            if not own_id_num:
                try: own_id_num = int(uid_str)
                except Exception: own_id_num = 0
            try:
                pkt = create_team(current_key, current_iv, client_version, mode=15)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
            except Exception: pass
            await asyncio.sleep(1.5)
            try:
                pkt = team_fresh(int(own_id_num), current_key, current_iv)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
            except Exception: pass
            await asyncio.sleep(1.0)
            for peer_uid, peer_info in peers_snapshot.items():
                if peer_uid == uid_str: continue
                peer_acc_id = peer_info.get("data", {}).get("account_id") or peer_uid
                for _ in range(2):
                    try:
                        inv = invite_player_in_team(int(peer_acc_id), current_key, current_iv)
                        if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                            _writer_ref["w"].write(inv); await _writer_ref["w"].drain()
                    except Exception: pass
                    await asyncio.sleep(0.6)
            await asyncio.sleep(TEAM_INVITE_WAIT + 3.0)
            try:
                pkt = team_fresh(int(own_id_num), current_key, current_iv)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
            except Exception: pass
            await asyncio.sleep(1.0)
            print_success(f"[TEAM] 🚀 {uid_str} loop: ready → 1s → start (every 5s)")
            while _team_active["flag"] and not _match_played["flag"]:
                try:
                    if bot_state.is_paused(uid_str): break
                    async with _team_state["lock"]:
                        if _team_state["leader_uid"] != uid_str: break
                    own_id = current_account_data.get('account_id', own_id_num) if current_account_data else own_id_num
                    try:
                        rdy = ready_for_game(int(own_id), current_key, current_iv)
                        if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                            _writer_ref["w"].write(rdy); await _writer_ref["w"].drain()
                    except Exception: pass
                    await asyncio.sleep(1.0)
                    sm = start_match_team(int(own_id), current_key, current_iv, region=account_region, mode=15)
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        _writer_ref["w"].write(sm); await _writer_ref["w"].drain()
                except Exception: pass
                try: await asyncio.wait_for(asyncio.sleep(5.0), timeout=5.5)
                except asyncio.TimeoutError: pass
        except asyncio.CancelledError: raise
        except Exception as e:
            print_error(f"[TEAM] coordinator error: {e}")

    async def _member_match_trigger():
        try:
            await asyncio.sleep(TEAM_READY_DELAY + 18.0)
            async with _team_state["lock"]:
                if _team_state["leader_uid"] == uid_str: return
            print_success(f"[TEAM] 🚀 Member {uid_str} loop")
            my_id = current_account_data.get('account_id', uid_str) if current_account_data else uid_str
            while _team_active["flag"] and not _match_played["flag"]:
                try:
                    if bot_state.is_paused(uid_str): break
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        try:
                            rdy = ready_for_game(int(my_id), current_key, current_iv)
                            _writer_ref["w"].write(rdy); await _writer_ref["w"].drain()
                        except Exception: pass
                        await asyncio.sleep(1.0)
                        sm = start_match_team(int(my_id), current_key, current_iv, region=account_region, mode=15)
                        _writer_ref["w"].write(sm); await _writer_ref["w"].drain()
                except Exception: pass
                try: await asyncio.wait_for(asyncio.sleep(5.0), timeout=5.5)
                except asyncio.TimeoutError: pass
        except asyncio.CancelledError: raise
        except Exception: pass

    try:
        while True:
            while bot_state.is_paused(uid_str):
                bot_state.update_status(uid_str, "PAUSED", 0)
                await asyncio.sleep(1.0)
            writer = None; gateway_ping_task = None
            team_coord_task = None; member_trigger_task = None
            try:
                if current_account_data:
                    fresh = None
                    if current_account_data.get('auth_type') == 'guest' and current_account_data.get('auth_uid'):
                        fresh = cache_get(str(current_account_data['auth_uid']))
                    elif current_account_data.get('auth_type') == 'token' and current_account_data.get('auth_token'):
                        fresh = cache_get(f"tok_{current_account_data['auth_token'][:20]}")
                    if fresh:
                        current_account_data = fresh
                        current_key = fresh['aes_ak']; current_iv = fresh['iv_i']
                        current_token = await build_tcp_startup_packet(
                            fresh['account_id'], fresh['token'], fresh['server_time'],
                            current_key, current_iv, region=fresh.get('region', account_region), typ='OnLine')
                    else: raise ConnectionError("Cache expired")
                resolved_ip = await resolve_host_cloudflare(ip)
                reader, writer = await asyncio.open_connection(resolved_ip, int(port))
                bot_state.register_writer(uid_str, writer)
                _writer_ref["w"] = writer
                raw_sock = writer.get_extra_info('socket')
                if raw_sock: optimize_tcp_socket(raw_sock)
                writer.write(bytes.fromhex(current_token)); await writer.drain()
                try:
                    init_ka = await send_keep_alive(account_region)
                    if init_ka and not writer.is_closing():
                        writer.write(init_ka); await asyncio.wait_for(writer.drain(), timeout=3)
                except Exception: pass
                async def func_gateway_keepalive():
                    ka_bytes = await send_keep_alive(account_region)
                    while True:
                        await asyncio.sleep(5)
                        try:
                            if writer and not writer.is_closing():
                                writer.write(ka_bytes); await writer.drain()
                        except Exception: break
                gateway_ping_task = asyncio.create_task(func_gateway_keepalive())
                print_success(f"[✓] TCP Gateway Connected | UID: {uid_str}")
                reconnects = 0
                async with _team_state["lock"]:
                    _team_state["peers"][uid_str] = {"writer": writer, "data": current_account_data,
                        "key": current_key, "iv": current_iv}
                    _team_state["match_total_uids"].add(uid_str)
                    if _team_state["leader_uid"] is None:
                        _team_state["leader_uid"] = uid_str
                if not _match_played["flag"] and TEAM_MODE:
                    team_coord_task = asyncio.create_task(_team_coordinator())
                    member_trigger_task = asyncio.create_task(_member_match_trigger())
                while True:
                    play_matches[:] = [m for m in play_matches if not m.done()]
                    if bot_state.is_paused(uid_str): break
                    if _match_played["flag"]:
                        # Idle during match — drain packets
                        try: data = await asyncio.wait_for(reader.read(8192), timeout=1.0)
                        except asyncio.TimeoutError: continue
                        if not data: raise ConnectionError("Connection closed")
                        if len(data) > 20 and data.hex().startswith("0600"):
                            await _process_social_packet(data, tag="IDLE")
                        continue
                    try: data = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                    except asyncio.TimeoutError:
                        no_response_count += 1; continue
                    if not data: raise ConnectionError("Connection closed")
                    hex_data = data.hex(); packet_length = len(data)
                    no_response_count = 0
                    if hex_data.startswith("0600") and packet_length > 20:
                        await _process_social_packet(data, tag="MAIN"); continue
                    if hex_data.startswith("0500") and packet_length > 10:
                        try:
                            inner = bytes.fromhex(hex_data[10:])
                            dec = decode_protobuf_dict(inner)
                            if not dec:
                                alt = decode_protobuf_2(inner)
                                if alt: dec = {str(k): {"data": v} for k, v in alt.items()}
                            f5w = dec.get("5") or dec.get(5)
                            f5 = f5w.get("data") if isinstance(f5w, dict) and "data" in f5w else f5w
                            if not isinstance(f5, dict): f5 = dec
                            def _f5g(key):
                                if not isinstance(f5, dict): return None
                                v = f5.get(key) if key in f5 else f5.get(str(key))
                                if isinstance(v, dict) and "data" in v: return v["data"]
                                return v
                            group_id_pkt = _f5g(8)
                            if group_id_pkt and isinstance(group_id_pkt, str) and 20 <= len(group_id_pkt) <= 40:
                                pass
                            else: group_id_pkt = None
                            own_acc = str(current_account_data.get('account_id')) if current_account_data else None
                            inviter = None
                            for fk in [1,2,3,4,6,7,13,15,20]:
                                cand = _f5g(fk)
                                if cand and str(cand).isdigit() and 6 <= len(str(cand)) <= 15:
                                    if str(cand) != uid_str and str(cand) != own_acc:
                                        inviter = cand; break
                            if inviter and group_id_pkt and _team_state["leader_uid"] != uid_str:
                                print_success(f"[TEAM] 📨 Invite from {inviter} → accepting...")
                                for _ in range(2):
                                    try:
                                        acc = accept_team_invite(int(inviter), group_id_pkt, current_key, current_iv)
                                        if writer and not writer.is_closing():
                                            writer.write(acc); await writer.drain()
                                    except Exception: pass
                                    await asyncio.sleep(0.4)
                        except Exception: pass
                        continue
                    if hex_data.startswith("0300") and 10 < packet_length < 30: continue
                    if hex_data.startswith("0300") and packet_length >= 300:
                        print_success(f"[⚔] Match Found | UID: {uid_str}")
                        for tk in (team_coord_task, member_trigger_task):
                            if tk and not tk.done(): tk.cancel()
                        team_coord_task = None; member_trigger_task = None
                        _team_active["flag"] = False
                        try:
                            res = json.loads(await decode_protobuf_async(hex_data[10:]))
                            token = udp_key = match_code = server_ip_port = None
                            match_account_id = None; match_game_mode = 1
                            match_map_id = 1; match_match_mode = 1; match_sleep_ms = 0; match_id = 0
                            if '42' in res and 'data' in res['42']: match_code = res['42']['data']
                            if '5' in res and 'data' in res['5']:
                                rf5 = res['5']['data']
                                server_ip_port = rf5.get('2', {}).get('data')
                                udp_key = rf5.get('3', {}).get('data')
                                token = rf5.get('4', {}).get('data')
                                if '42' in rf5: match_code = rf5['42']['data']
                                try: match_id = int(rf5.get('1', {}).get('data') or 0)
                                except Exception: pass
                                try: match_map_id = int(rf5.get('6', {}).get('data') or 1)
                                except Exception: pass
                                try: match_game_mode = int(rf5.get('7', {}).get('data') or 1)
                                except Exception: pass
                                try: match_match_mode = int(rf5.get('8', {}).get('data') or 1)
                                except Exception: pass
                                try: match_sleep_ms = int(rf5.get('5', {}).get('data') or 0)
                                except Exception: pass
                            if '1' in res and 'data' in res['1']: match_account_id = res['1']['data']
                            effective_acc_id = match_account_id or account_id or "BD_BOT"
                            if token and udp_key and match_code and server_ip_port:
                                match_index = await _inc_match(uid_str)
                                bot_state.increment_match_started()
                                bot_state.update_status(uid_str, "IN_MATCH", 1)
                                new_match = asyncio.create_task(play_game(
                                    server_ip_port, token, udp_key, match_code,
                                    effective_acc_id, "BD", client_version,
                                    current_key, current_iv, match_index,
                                    game_mode=match_game_mode, map_id=match_map_id,
                                    match_mode=match_match_mode, sleep_ms=match_sleep_ms,
                                    match_id=match_id, verbose=True))
                                play_matches.append(new_match)
                                try: await new_match
                                except Exception as e: print_error(f"[MATCH #{match_index}] {e}")
                                play_matches[:] = [m for m in play_matches if not m.done()]
                                _match_played["flag"] = True

                                # ══════════════════════════════════════════════
                                # PER-MATCH LOOP: mark done, prepare reform, do NOT exit
                                # ══════════════════════════════════════════════
                                async with _team_state["lock"]:
                                    _team_state["match_finished_uids"].add(uid_str)
                                    total = _team_state["match_total_uids"]
                                    finished = _team_state["match_finished_uids"]
                                    all_done = bool(total) and finished >= total

                                if all_done:
                                    print_success(f"[LOOP] ✅ All {len(total)} bots finished — group {group_id} reforms")
                                    async with _team_state["lock"]:
                                        _team_state["match_finished_uids"] = set()
                                else:
                                    remaining = len(total) - len(finished)
                                    print_info(f"[LOOP] {uid_str} done — waiting {remaining} more bot(s)")

                                # Reset flags for next cycle WITHOUT exiting
                                _match_played["flag"] = False
                                _team_active["flag"] = True
                                _match_cycle_count += 1

                                # If this bot was the leader, allow leadership to rotate
                                async with _team_state["lock"]:
                                    if _team_state["leader_uid"] == uid_str:
                                        _team_state["leader_uid"] = None
                                    _team_state["team_code"] = None

                                # Give a small window for peers to catch up
                                reform_start = time.time()
                                while time.time() - reform_start < MATCH_REFORM_WAIT:
                                    if bot_state.is_paused(uid_str): break
                                    async with _team_state["lock"]:
                                        peers_now = len(_team_state["peers"])
                                        leader_now = _team_state["leader_uid"]
                                    if peers_now >= TEAM_SIZE and leader_now is not None:
                                        break
                                    await asyncio.sleep(0.5)

                                # Small cooldown before re-search
                                await asyncio.sleep(MATCH_CYCLE_DELAY)

                                # Decide whether to become leader
                                async with _team_state["lock"]:
                                    if _team_state["leader_uid"] is None:
                                        _team_state["leader_uid"] = uid_str
                                        is_leader_now = True
                                    else:
                                        is_leader_now = (_team_state["leader_uid"] == uid_str)

                                if TEAM_MODE:
                                    if team_coord_task and not team_coord_task.done():
                                        team_coord_task.cancel()
                                    if member_trigger_task and not member_trigger_task.done():
                                        member_trigger_task.cancel()
                                    if is_leader_now:
                                        print_success(f"[LOOP #{_match_cycle_count}] 👑 {uid_str} → reform team + search")
                                        team_coord_task = asyncio.create_task(_team_coordinator())
                                        member_trigger_task = asyncio.create_task(_member_match_trigger())
                                    else:
                                        print_info(f"[LOOP #{_match_cycle_count}] {uid_str} → wait as member")
                                        member_trigger_task = asyncio.create_task(_member_match_trigger())

                                print_success(f"[LOOP #{_match_cycle_count}] {uid_str} → back in READ loop")
                                continue   # stay in same TCP session
                        except Exception as e:
                            print_warning(f"[MATCH] {e}"); continue
                    if 30 <= packet_length <= 40: continue
            except asyncio.CancelledError: raise
            except Exception as e:
                if "Cache expired" in str(e):
                    print_warning(f"[!] Token expired {uid_str}"); break
                reconnects += 1
                if reconnects > max_reconnects:
                    if current_account_data:
                        try:
                            if current_account_data.get('auth_uid'):
                                cache_invalidate(str(current_account_data['auth_uid']))
                        except Exception: pass
                    reconnects = 0; break
                await asyncio.sleep(min(reconnects * 0.5, 2.0))
            finally:
                _team_active["flag"] = False
                async with _team_state["lock"]:
                    _team_state["peers"].pop(uid_str, None)
                    if _team_state["leader_uid"] == uid_str:
                        _team_state["leader_uid"] = None
                        _team_state["team_code"] = None
                for tk in (team_coord_task, member_trigger_task):
                    if tk and not tk.done():
                        tk.cancel()
                        try: await tk
                        except asyncio.CancelledError: pass
                if gateway_ping_task: gateway_ping_task.cancel()
                if writer:
                    bot_state.unregister_writer(uid_str, writer)
                    await safe_close_writer(writer)
                _match_played["flag"] = False
                _team_active["flag"] = True
    except asyncio.CancelledError: raise
    finally:
        for m in play_matches:
            if not m.done(): m.cancel()

# ==================== INFORMATIONAL ====================
async def informational(addrs, starter_packet, key, iv, region="BD",
                        account_id="", max_reconnects=3, account_data=None):
    uid_str = str(account_id); reconnects = 0
    ip, port = addrs.split(":")
    while True:
        while uid_str and bot_state.is_paused(uid_str): await asyncio.sleep(1.0)
        writer = None; ping_task = None
        try:
            resolved_ip = await resolve_host_cloudflare(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, int(port))
            if uid_str: bot_state.register_writer(uid_str, writer)
            raw_sock = writer.get_extra_info('socket')
            if raw_sock: optimize_tcp_socket(raw_sock)
            writer.write(bytes.fromhex(starter_packet)); await writer.drain()
            reconnects = 0
            try:
                init_ka = await send_keep_alive(region)
                if init_ka and not writer.is_closing():
                    writer.write(init_ka); await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception: pass
            async def info_ka():
                ka = await send_keep_alive(region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka); await writer.drain()
                    except Exception: break
            ping_task = asyncio.create_task(info_ka())
            while True:
                if uid_str and bot_state.is_paused(uid_str):
                    if ping_task: ping_task.cancel()
                    if uid_str: bot_state.unregister_writer(uid_str, writer)
                    await safe_close_writer(writer); writer = None
                    while bot_state.is_paused(uid_str): await asyncio.sleep(1.0)
                    break
                try: data = await asyncio.wait_for(reader.read(8192), timeout=1.0)
                except asyncio.TimeoutError: continue
                if not data: raise ConnectionError("closed")
        except asyncio.CancelledError:
            if ping_task: ping_task.cancel()
            if uid_str: bot_state.unregister_writer(uid_str, writer)
            await safe_close_writer(writer); raise
        except Exception:
            if ping_task: ping_task.cancel()
            if uid_str: bot_state.unregister_writer(uid_str, writer)
            await safe_close_writer(writer)
            reconnects += 1
            if reconnects > max_reconnects:
                await asyncio.sleep(3); reconnects = 0
            else: await asyncio.sleep(1)

# ==================== ACCOUNT HELPERS ====================
def _register_credentials(ad):
    try:
        bot_state.account_credentials[str(ad['account_id'])] = ad
        if ad.get('auth_uid'): bot_state.account_credentials[str(ad['auth_uid'])] = ad
    except Exception: pass

async def refresh_account_profile(ad_or_uid):
    try:
        if isinstance(ad_or_uid, str):
            uid = str(ad_or_uid); ad = bot_state.account_credentials.get(uid)
        else:
            ad = ad_or_uid; uid = str(ad.get('account_id'))
        if not ad: return
        token = ad.get('token'); acc_id = ad.get('account_id')
        srv = ad.get('server_url'); rel = ad.get('release_version')
        if not (token and acc_id and srv and rel): return
        data = await get_player_personal_show(int(acc_id), token, srv, rel)
        if not data: return
        pd = data.get(1, {}) if isinstance(data.get(1), dict) else {}
        nickname = pd.get(3); lvl = pd.get(6); exp = pd.get(7)
        if exp is None: return
        try: exp = int(exp); lvl = int(lvl) if lvl else 1
        except Exception: return
        aid = str(acc_id)
        if aid not in bot_state.accounts:
            bot_state.register_account(aid, nickname or f"Player_{aid}",
                region=ad.get('region','BD'), level=lvl, exp=exp,
                auth_uid=ad.get('auth_uid'))
            return
        old = bot_state.accounts[aid].get("current_exp", 0)
        bot_state.update_exp(aid, exp, lvl)
        if nickname: bot_state.accounts[aid]["nickname"] = nickname
        if exp > old: print_success(f"[★] +{exp-old:,} EXP | {aid}")
    except Exception: pass

async def process_account_uid_pass(uid, password, region_override=None):
    cached = cache_get(uid)
    if cached:
        aid = str(cached['account_id'])
        nick = cached.get('nickname', f"Player_{aid}")
        lvl = cached.get('level', 1); expv = cached.get('exp', 0)
        bot_state.register_account(aid, nick, cached.get('region','BD'), lvl, expv,
            cached.get('likes',0), auth_uid=str(uid))
        _register_credentials(cached); return cached
    try:
        async with _LOGIN_SEMAPHORE:
            vc = await version_config(region_override or "BD")
            if not vc: return None
            release_version, client_version, server_url, gop_1, app_version = vc
            tg = await get_access_token(uid, password)
            if not tg: return None
            open_id, access_token, platform = tg
            major_payload, login_payload = await get_payload(access_token, open_id, platform, client_version)
            res_json = await major_login(major_payload, server_url, release_version)
            if not res_json: return None
            def _gd(k):
                v = res_json.get(str(k))
                if isinstance(v, dict) and "data" in v: return v["data"]
                if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                if isinstance(v, dict): return v.get("data")
                return None
            acc_id_raw = _gd(1); region_raw = _gd(2) or "BD"
            jwt_token = _gd(8); server_url_raw = _gd(10); server_time = _gd(21)
            aes_ak, iv_i = _extract_key_iv(res_json)
            if not jwt_token or not server_url_raw or not aes_ak: return None
            getlogin_json = await get_login_data(login_payload, jwt_token, server_url_raw, release_version)
            if not getlogin_json: return None
        def _gf(f, d=None):
            v = getlogin_json.get(str(f), {}).get("data")
            return v if v is not None else d
        level = int(_gf(6,1) or 1); exp = int(_gf(7,0) or 0); likes = int(_gf(8,0) or 0)
        nickname = _gf(4, f"Player_{acc_id_raw}") or f"Player_{acc_id_raw}"
        region = region_raw or _gf(3,"BD") or "BD"; acc_id = str(acc_id_raw)
        bot_state.register_account(acc_id, nickname, region, level, exp, likes, auth_uid=str(uid))
        if AUTO_BIO_ENABLED and AUTO_BIO_ON_LOGIN:
            try: await update_bio_auto(jwt_token, AUTO_BIO_TEXT, release_version, server_url_raw)
            except Exception: pass
        ad = {'account_id':acc_id_raw,'nickname':nickname,'region':region,
            'level':level,'exp':exp,'likes':likes,'open_id':open_id,
            'access_token':access_token,'platform':str(platform),
            'token':jwt_token,'server_time':server_time,
            'aes_ak':aes_ak,'iv_i':iv_i,
            'functional_addrs':_gf(14),'informational_addrs':_gf(32),
            'release_version':release_version,'client_version':client_version,
            'server_url':server_url_raw,'login_payload_data':login_payload,
            'auth_type':'guest','auth_uid':uid,'auth_password':password}
        _register_credentials(ad); cache_set(uid, ad); return ad
    except Exception as e:
        print_error(f"login err: {e}"); return None

async def run_account_worker(ad, label, region_override=None, clan_override=None,
                             group_id: str = "default"):
    acc_id = str(ad['account_id'])
    info_task = None; exp_task = None; bio_task = None
    try:
        reg = region_override or ad.get('region','BD')
        tcp_online = await build_tcp_startup_packet(ad['account_id'], ad['token'], ad['server_time'],
            ad['aes_ak'], ad['iv_i'], region=reg, typ='OnLine')
        tcp_chat = await build_tcp_startup_packet(ad['account_id'], ad['token'], ad['server_time'],
            ad['aes_ak'], ad['iv_i'], region=reg, typ='ChaT')
        if clan_override:
            try:
                await asyncio.sleep(1.0); await join_clan(ad['token'], clan_override)
            except Exception: pass
        info_task = asyncio.create_task(informational(
            ad['informational_addrs'], tcp_chat, ad['aes_ak'], ad['iv_i'],
            region=reg, account_id=acc_id, account_data=ad))
        async def exp_refresher():
            while True:
                await asyncio.sleep(90 + random.uniform(-10,10))
                fresh = bot_state.account_credentials.get(acc_id)
                if fresh: await refresh_account_profile(fresh)
        exp_task = asyncio.create_task(exp_refresher())
        if AUTO_BIO_ENABLED:
            async def bio_refresher():
                await asyncio.sleep(30)
                while True:
                    try:
                        fresh = bot_state.account_credentials.get(acc_id)
                        if fresh and fresh.get('token'):
                            await update_bio_auto(fresh['token'], AUTO_BIO_TEXT,
                                fresh.get('release_version', AUTO_BIO_RELEASE_VER),
                                fresh.get('server_url'))
                    except Exception: pass
                    await asyncio.sleep(AUTO_BIO_REFRESH_SEC)
            bio_task = asyncio.create_task(bio_refresher())
        await functional_lone_wolf(ad['functional_addrs'], tcp_online, reg, ad['client_version'],
            ad['aes_ak'], ad['iv_i'], account_id=acc_id, account_data=ad, group_id=group_id)
    except asyncio.CancelledError: raise
    except Exception as e:
        print_error(f"worker err {label}: {e}")
    finally:
        for t in (info_task, exp_task, bio_task):
            if t and not t.done(): t.cancel()
        for t in (info_task, exp_task, bio_task):
            if t:
                try: await t
                except Exception: pass

async def account_loop_guest(uid, password, region_override=None, clan_override=None,
                              group_id: str = "default"):
    uid_str = str(uid)
    bot_state.account_workers[uid_str] = asyncio.current_task()
    acc_id = None
    while True:
        try:
            cache_invalidate(uid_str)
            bot_state.update_status(uid_str, "CONNECTING")
            ad = await process_account_uid_pass(uid_str, password, region_override)
            if not ad:
                await asyncio.sleep(15); continue
            acc_id = str(ad['account_id'])
            bot_state.account_workers[acc_id] = asyncio.current_task()
            bot_state.auth_to_game_id[uid_str] = acc_id
            bot_state.game_to_auth_id[acc_id] = uid_str
            await run_account_worker(ad, uid_str, region_override, clan_override, group_id=group_id)
            await asyncio.sleep(3)
        except asyncio.CancelledError:
            try:
                bot_state.update_status(uid_str, "OFFLINE")
                if acc_id: bot_state.update_status(acc_id, "OFFLINE")
            except Exception: pass
            break
        except Exception as e:
            print_error(f"err {uid_str}: {e}"); await asyncio.sleep(10)

# ==================== CREATE ACCOUNTS ====================
def _gf_field(ld, key, default=None):
    if not ld: return default
    v = ld.get(str(key), {})
    if isinstance(v, dict): return v.get("data", default)
    return v if v is not None else default

def generate_password() -> str:
    return hashlib.sha256((str(uuid.uuid4()) + str(time.time())).encode()).hexdigest().upper()

async def get_newbie_roles(jwt_token: str, server_url: str, release_version: str):
    try:
        url = f"{server_url}/GiveAccountNewbieRoles"
        payload = bytes.fromhex(encrypt_aes(create_proto({"1": 1}).hex()))
        headers = {"authorization": f"Bearer {jwt_token}",
            "host": server_url.replace("https://", "").replace("http://", "").split("/")[0],
            "x-ga": "v1 1", "content-type": "application/x-www-form-urlencoded",
            "accept-encoding": "deflate, gzip", "releaseversion": f"{release_version}",
            "user-agent": "UnityPlayer/2022.3.47f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
            "accept": "*/*", "x-unity-version": "2022.3.47f1"}
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=5)) as session:
            async with session.post(url, headers=headers, data=payload) as response:
                return response.status == 200
    except Exception: return None

async def set_newbie_roles(jwt_token: str, server_url: str, release_version: str):
    try:
        url = f"{server_url}/SelectPresetLoadout"
        fields = {"1": {"1": 102000037},
            "2": {"1": 102000037, "2": 50462976, "3": 414929892933512066, "4": 0},
            "6": {"1": {"1": 1, "2": 102000037, "3": {"1": 3, "2": 706},
                        "6": "PRESET 1", "7": 1}},
            "11": 1}
        payload = bytes.fromhex(encrypt_aes(create_proto(fields).hex()))
        headers = {"authorization": f"Bearer {jwt_token}",
            "host": server_url.replace("https://", "").replace("http://", "").split("/")[0],
            "x-ga": "v1 1", "content-type": "application/x-www-form-urlencoded",
            "accept-encoding": "deflate, gzip", "releaseversion": f"{release_version}",
            "user-agent": "UnityPlayer/2022.3.47f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
            "accept": "*/*", "x-unity-version": "2022.3.47f1"}
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=5)) as session:
            async with session.post(url, headers=headers, data=payload) as response:
                return response.status == 200
    except Exception: return None

async def choose_region(region, jwt_token, login_url, release_version):
    url = f"{login_url.rstrip('/')}/ChooseRegion"
    payload = bytes.fromhex(encrypt_aes(create_proto({1: region.upper()}).hex()))
    hdrs = {"Accept-Encoding": "gzip", "Authorization": f"Bearer {jwt_token}",
        "Connection": "Keep-Alive", "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_version}",
        "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "X-GA": "v1 1", "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1"}
    try:
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, data=payload, headers=hdrs, ssl=ssl_ctx) as r:
                return r.status
    except Exception: return None

async def create_four_accounts(region: str, clan_id: str, count: int = 4):
    bot_state.creating = True; bot_state.create_progress = []
    def _prog(s):
        try: print(f"[CREATE] {s}"); bot_state.log(s, "info")
        except Exception: pass
        bot_state.create_progress.append(s)
    try:
        vc = await version_config(region)
        if not vc:
            _prog("❌ version config failed"); return []
        release_v, remote_v, login_url, gop_1, app_version = vc
        if not login_url.endswith("/"): login_url += "/"
        lang = REGION_LANG.get(region.upper(), "en")
        game_version = remote_v or app_version
        created = []
        for i in range(count):
            _prog(f"⌛ Creating bot {i+1}/{count}...")
            password = generate_password()
            try:
                uid = await register_account(password, gop_1, app_version)
                if not uid:
                    _prog(f"❌ bot {i+1}: register failed"); continue
                await asyncio.sleep(1.0)
                tok = await grant_token(uid, password, gop_1, app_version)
                if not tok:
                    _prog(f"❌ bot {i+1}: grant failed"); continue
                open_id = tok["open_id"]; access_token = tok["access_token"]
                platform = tok.get("platform", 4)
                major_payload, login_payload = await get_payload(access_token, open_id, platform, game_version, lang)
                if not major_payload or not login_payload:
                    _prog(f"❌ bot {i+1}: payload build failed"); continue
                _prefix = "Zesty__" if i < (count // 2) else "Bashant__"
nickname_final = f"{_prefix}{''.join(random.choices(string.ascii_letters + string.digits, k=5))}"
                mr = await major_register(release_v, access_token, open_id, nickname_final,
                                          game_version, login_url, lang)
                if not mr:
                    _prog(f"❌ bot {i+1}: MajorRegister failed"); continue
                await asyncio.sleep(3.0)
                res_json = None
                for attempt in range(3):
                    mp, lp = await get_payload(access_token, open_id, platform, game_version, lang)
                    res_json = await major_login(mp, login_url, release_v)
                    if res_json and (("8" in res_json) or (8 in res_json)):
                        login_payload = lp; break
                    res_json = None; await asyncio.sleep(2.0)
                if not res_json:
                    _prog(f"❌ bot {i+1}: MajorLogin #1 failed"); continue
                def _gd(k):
                    v = res_json.get(str(k))
                    if isinstance(v, dict) and "data" in v: return v["data"]
                    if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                    if isinstance(v, dict): return v.get("data")
                    return None
                jwt_token = _gd(8); server_url_raw = _gd(10)
                server_time = _gd(21); acc_id_raw = _gd(1)
                if not jwt_token:
                    _prog(f"❌ bot {i+1}: no JWT"); continue
                if not server_url_raw:
                    cr_status = await choose_region(region, jwt_token, login_url, release_v)
                    if cr_status != 200:
                        _prog(f"❌ bot {i+1}: ChooseRegion failed"); continue
                    await asyncio.sleep(2.0)
                    for attempt in range(3):
                        mp2, lp2 = await get_payload(access_token, open_id, platform, game_version, lang)
                        res_json2 = await major_login(mp2, login_url, release_v)
                        if res_json2 and (("10" in res_json2) or (10 in res_json2)):
                            res_json = res_json2; login_payload = lp2; break
                        res_json2 = None; await asyncio.sleep(2.0)
                    if not res_json2:
                        _prog(f"❌ bot {i+1}: MajorLogin #2 failed"); continue
                    def _gd2(k):
                        v = res_json.get(str(k))
                        if isinstance(v, dict) and "data" in v: return v["data"]
                        if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                        if isinstance(v, dict): return v.get("data")
                        return None
                    jwt_token = _gd2(8); server_url_raw = _gd2(10)
                    server_time = _gd2(21); acc_id_raw = _gd2(1)
                aes_ak, iv_i = _extract_key_iv(res_json)
                if not aes_ak or not iv_i:
                    _prog(f"❌ bot {i+1}: AES key/IV fail"); continue
                ld = await get_login_data(login_payload, jwt_token, server_url_raw, release_v)
                level = 1; exp = 0; likes = 0
                if ld:
                    def _gf(f, d=None):
                        v = ld.get(str(f), {}).get("data")
                        return v if v is not None else d
                    level = int(_gf(6, 1) or 1); exp = int(_gf(7, 0) or 0)
                    likes = int(_gf(8, 0) or 0)
                    nickname_final = _gf(4, nickname_final) or nickname_final
                await get_newbie_roles(jwt_token, server_url_raw, release_v)
                await asyncio.sleep(0.5)
                await set_newbie_roles(jwt_token, server_url_raw, release_v)
                if AUTO_BIO_ENABLED:
                    try: await update_bio_auto(jwt_token, AUTO_BIO_TEXT, release_v, server_url_raw)
                    except Exception: pass
                ad = {'account_id': acc_id_raw, 'nickname': nickname_final,
                    'region': region, 'level': level, 'exp': exp, 'likes': likes,
                    'open_id': open_id, 'access_token': access_token,
                    'platform': str(platform), 'token': jwt_token,
                    'server_time': server_time, 'aes_ak': aes_ak, 'iv_i': iv_i,
                    'functional_addrs': _gf_field(ld, 14),
                    'informational_addrs': _gf_field(ld, 32),
                    'release_version': release_v, 'client_version': game_version,
                    'server_url': server_url_raw, 'login_payload_data': login_payload,
                    'auth_type': 'guest', 'auth_uid': uid, 'auth_password': password}
                _register_credentials(ad); cache_set(uid, ad); created.append(ad)
                _prog(f"✅ bot {i+1}: {nickname_final} | UID {acc_id_raw} | Lvl {level}")
                await asyncio.sleep(0.6)
            except Exception as e:
                _prog(f"❌ bot {i+1}: {e}"); traceback.print_exc()
        if not created:
            _prog("❌ No accounts created."); return []
        group_id = None
        try:
            team_accounts = [{"uid": str(a['auth_uid']), "password": str(a['auth_password']),
                "account_id": str(a.get('account_id','')), "nickname": str(a.get('nickname',''))}
                for a in created]
            group_id = save_team_file(clan_id, region, team_accounts)
        except Exception as e: _prog(f"⚠️ save group file failed: {e}")
        for i, a in enumerate(created):
            try:
                task = asyncio.create_task(account_loop_guest(
                    str(a['auth_uid']), a['auth_password'],
                    region_override=region, clan_override=clan_id,
                    group_id=group_id))
                bot_state.account_workers[str(a['auth_uid'])] = task
                await asyncio.sleep(0.35)
            except Exception as e: _prog(f"   ❌ worker {i+1} failed: {e}")
        _prog(f"✅ All {len(created)} bots launched. group_id={group_id}")
        return created
    except Exception as e:
        _prog(f"❌ create_four_accounts error: {e}"); traceback.print_exc(); return []
    finally: bot_state.creating = False

# ==================== AUTO-FARM HELPERS ====================
async def _wait_for_squad_ready(group_id: str, region: str, timeout: float) -> Optional[str]:
    if not group_id: return None
    start = time.time()
    while time.time() - start < timeout:
        try:
            teams = load_all_team_files()
            team = next((t for t in teams if t.get("group_id") == group_id), None)
            if team:
                for acc in team["accounts"]:
                    auth_uid = str(acc["uid"])
                    game_uid = bot_state.auth_to_game_id.get(auth_uid, auth_uid)
                    creds = (bot_state.account_credentials.get(game_uid) or
                             bot_state.account_credentials.get(auth_uid))
                    if creds and creds.get("token"):
                        if bot_state.writers.get(str(game_uid)) or bot_state.writers.get(auth_uid):
                            return creds["token"]
        except Exception: pass
        await asyncio.sleep(1.0)
    return None

async def _wait_for_guild_fetch(group_id: str, guild_id: str, timeout: float) -> Optional[Dict]:
    if not group_id: return None
    start = time.time()
    while time.time() - start < timeout:
        try:
            teams = load_all_team_files()
            team = next((t for t in teams if t.get("group_id") == group_id), None)
            if team:
                for acc in team["accounts"]:
                    auth_uid = str(acc["uid"])
                    game_uid = bot_state.auth_to_game_id.get(auth_uid, auth_uid)
                    creds = (bot_state.account_credentials.get(game_uid) or
                             bot_state.account_credentials.get(auth_uid))
                    if creds and creds.get("token"):
                        info = await get_clan_info(creds["token"], guild_id)
                        if info and info.get("clan_id"):
                            return info
        except Exception: pass
        await asyncio.sleep(3.0)
    return None

# ==================== API ====================
@aiohttp.web.middleware
async def _req_logger(request, handler):
    print(f"\033[90m[REQ] {request.method} {request.path}\033[0m")
    try:
        resp = await handler(request)
        print(f"\033[90m[RES] {request.method} {request.path} → {resp.status}\033[0m")
        return resp
    except aiohttp.web.HTTPException as e:
        if request.path.startswith("/api/") or request.path.startswith("/glory"):
            return aiohttp.web.json_response({"ok": False, "error": e.reason or str(e)}, status=e.status)
        raise
    except Exception as e:
        traceback.print_exc()
        if request.path.startswith("/api/") or request.path.startswith("/glory"):
            return aiohttp.web.json_response({"ok": False, "error": str(e)}, status=500)
        raise

async def serve_index(request):
    for path in (INDEX_HTML_PATH, "index.html"):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return aiohttp.web.Response(text=f.read(), content_type="text/html")
        except Exception: continue
    return aiohttp.web.Response(text="<h1>bg</h1>", content_type="text/html")

async def api_ping(request):
    return aiohttp.web.json_response({"pong": True, "app": "bg", "version": "2.1"})

async def api_stats(request):
    try:
        accs = list(bot_state.accounts.values())
        online = sum(1 for a in accs if a.get("status") in ("ONLINE","IN_MATCH","SEARCHING"))
        active_matches = sum(a.get("active_matches", 0) for a in accs)
        uptime = max(1, int(time.time() - bot_state.start_time))
        uptime_h = max(0.016, uptime / 3600.0)
        data = {"accounts": accs, "logs": bot_state.logs[-200:],
            "total_accounts": len(accs), "total_online": online,
            "total_matches": bot_state.total_matches,
            "total_matches_started": bot_state.matches_started,
            "total_active_matches": active_matches,
            "total_gained_exp": bot_state.total_exp_gained,
            "uptime": uptime,
            "exp_per_hour": int(bot_state.total_exp_gained / uptime_h),
            "matches_per_hour": int(bot_state.matches_started / uptime_h),
            "creating": bool(bot_state.creating),
            "create_progress": bot_state.create_progress[-40:],
            "team_code": {gid: ts.get("team_code") for gid, ts in _team_states.items()},
            "leader_uid": {gid: ts.get("leader_uid") for gid, ts in _team_states.items()},
            "team_size": sum(len(ts["peers"]) for ts in _team_states.values()),
            "auto_bio_enabled": AUTO_BIO_ENABLED,
            "auto_bio_text": AUTO_BIO_TEXT,
            "auto_farm_squads_count": len(bot_state.auto_farm_squads),
            "auto_farm_total_requests": bot_state.auto_farm_counter,
            "per_match_loop": {"cycle_delay": MATCH_CYCLE_DELAY,
                "reform_wait": MATCH_REFORM_WAIT,
                "cycle_count_total": sum(t.get("cycle_count", 0) for t in _team_states.values())}}
        return aiohttp.web.Response(text=json.dumps(data, default=str, ensure_ascii=False),
                                    content_type="application/json", charset="utf-8")
    except Exception as e:
        return aiohttp.web.json_response({"error": str(e)}, status=500)

async def api_state(request):
    return aiohttp.web.Response(text=json.dumps({
        "creating": bool(bot_state.creating),
        "create_progress": bot_state.create_progress[-40:],
        "accounts": list(bot_state.accounts.values()),
        "team_size": sum(len(ts["peers"]) for ts in _team_states.values()),
        "team_groups": list(_team_states.keys()),
        "auto_farm_squads": bot_state.auto_farm_squads,
    }, default=str, ensure_ascii=False), content_type="application/json", charset="utf-8")

async def api_progress(request):
    return aiohttp.web.json_response({"creating": bot_state.creating,
        "create_progress": bot_state.create_progress[-60:]})

async def api_create_team(request):
    try:
        body = await request.json()
        region = str(body.get("region", "BD")).upper()
        clan_id = str(body.get("clan_id", "")).strip()
        count = int(body.get("count", 4))
        if not clan_id:
            return aiohttp.web.json_response({"ok": False, "error": "clan_id required"})
        if bot_state.creating:
            return aiohttp.web.json_response({"ok": False, "error": "already creating"})
        asyncio.create_task(create_four_accounts(region, clan_id, max(1, min(4, count))))
        return aiohttp.web.json_response({"ok": True, "msg": f"creating bots for {region}"})
    except Exception as e:
        return aiohttp.web.json_response({"ok": False, "error": str(e)})

async def api_account_add(request):
    try:
        body = await request.json()
        if body.get("token"):
            asyncio.create_task(account_loop_token(str(body["token"]).strip()))
            return aiohttp.web.json_response({"status": "ok"})
        uid = str(body.get("uid", "")).strip()
        password = str(body.get("password", "")).strip()
        if not uid or not password:
            return aiohttp.web.json_response({"status": "error", "error": "uid+password required"})
        asyncio.create_task(account_loop_guest(uid, password))
        return aiohttp.web.json_response({"status": "ok"})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_delete(request):
    try:
        body = await request.json()
        targets = {str(body.get("uid", "")).strip(), str(body.get("auth_uid", "")).strip()} - {""}
        for u in targets:
            if u in bot_state.account_workers:
                try: bot_state.account_workers[u].cancel()
                except Exception: pass
                bot_state.account_workers.pop(u, None)
            if u in bot_state.accounts: del bot_state.accounts[u]
            cache_invalidate(u); bot_state.toggle_pause(u, False)
        return aiohttp.web.json_response({"status": "ok"})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_refresh(request):
    try:
        body = await request.json()
        asyncio.create_task(refresh_account_profile(str(body.get("uid", "")).strip()))
        return aiohttp.web.json_response({"status": "ok"})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_restart(request):
    try:
        body = await request.json()
        uid = str(body.get("uid", "")).strip()
        resolved = {uid}
        if uid in bot_state.game_to_auth_id: resolved.add(str(bot_state.game_to_auth_id[uid]))
        if uid in bot_state.auth_to_game_id: resolved.add(str(bot_state.auth_to_game_id[uid]))
        for u in resolved:
            if u in bot_state.account_workers:
                try: bot_state.account_workers[u].cancel()
                except Exception: pass
                bot_state.account_workers.pop(u, None)
        for team in load_all_team_files():
            for a in team["accounts"]:
                if str(a["uid"]) in resolved and a.get("password"):
                    t = asyncio.create_task(account_loop_guest(str(a["uid"]), a["password"],
                        region_override=team["region"], clan_override=team["clan_id"],
                        group_id=team.get("group_id", "default")))
                    bot_state.account_workers[str(a["uid"])] = t
                    break
        return aiohttp.web.json_response({"status": "ok"})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_pause(request):
    try:
        body = await request.json()
        uid = str(body.get("uid", "")).strip()
        new_state = not bot_state.is_paused(uid)
        bot_state.toggle_pause(uid, new_state)
        if new_state: bot_state.close_writers_for_account(uid)
        return aiohttp.web.json_response({"status": "ok", "is_paused": new_state})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_pause_all(request):
    try:
        accs = list(bot_state.accounts.keys())
        if not accs: return aiohttp.web.json_response({"status": "ok", "all_paused": False})
        all_paused = all(bot_state.is_paused(u) for u in accs)
        new_state = not all_paused
        for u in accs:
            bot_state.toggle_pause(u, new_state)
            if new_state: bot_state.close_writers_for_account(u)
        return aiohttp.web.json_response({"status": "ok", "all_paused": new_state})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_logs_clear(request):
    bot_state.logs = []
    return aiohttp.web.json_response({"status": "ok"})

async def api_account_bio(request):
    try:
        body = await request.json()
        uid = str(body.get("uid", "")).strip()
        acc_id = str(body.get("account_id", "")).strip()
        bio_text = str(body.get("bio", AUTO_BIO_TEXT)).strip()[:AUTO_BIO_MAX_LEN]
        targets = {uid, acc_id} - {""}
        if not targets: return aiohttp.web.json_response({"ok": False, "error": "uid required"})
        if not bio_text: return aiohttp.web.json_response({"ok": False, "error": "bio empty"})
        creds = None
        for u in targets:
            creds = (bot_state.account_credentials.get(u) or
                     bot_state.account_credentials.get(str(bot_state.auth_to_game_id.get(u, u))))
            if creds: break
        if not creds or not creds.get('token'):
            return aiohttp.web.json_response({"ok": False, "error": "no token"})
        res = await update_bio_auto(creds['token'], bio_text,
            creds.get('release_version', AUTO_BIO_RELEASE_VER), creds.get('server_url'))
        if not res:
            return aiohttp.web.json_response({"ok": False, "error": "update failed"})
        return aiohttp.web.json_response({"ok": True, **res})
    except Exception as e:
        return aiohttp.web.json_response({"ok": False, "error": str(e)})

async def account_loop_token(token):
    try:
        vc = await version_config("BD")
        if not vc: return
        release_version, client_version, server_url, gop_1, app_version = vc
        r = await client.get(f"https://100067.connect.garena.com/oauth/token/inspect?token={token}",
                             headers={"User-Agent":"GarenaMSDK/4.0.19P4(G011A ;Android 9;en;US;)"})
        if r.status_code != 200: return
        data = r.json()
        if 'error' in data: return
        open_id = data.get('open_id'); platform = data.get('platform', 4)
        if not open_id: return
        major_payload, login_payload = await get_payload(token, open_id, platform, client_version)
        res_json = await major_login(major_payload, server_url, release_version)
        if not res_json: return
        def _gd(k):
            v = res_json.get(str(k))
            if isinstance(v, dict) and "data" in v: return v["data"]
            return v
        acc_id_raw = _gd(1); jwt_token = _gd(8)
        server_url_raw = _gd(10); server_time = _gd(21)
        region_raw = _gd(2) or "BD"
        aes_ak, iv_i = _extract_key_iv(res_json)
        if not (jwt_token and server_url_raw and aes_ak): return
        ld = await get_login_data(login_payload, jwt_token, server_url_raw, release_version)
        def _gf(f, d=None):
            v = (ld or {}).get(str(f), {}).get("data")
            return v if v is not None else d
        ad = {'account_id':acc_id_raw,'nickname':_gf(4, f"Player_{acc_id_raw}"),
            'region':region_raw,'level':int(_gf(6,1) or 1),'exp':int(_gf(7,0) or 0),
            'likes':int(_gf(8,0) or 0),'open_id':open_id,'access_token':token,
            'platform':str(platform),'token':jwt_token,'server_time':server_time,
            'aes_ak':aes_ak,'iv_i':iv_i,
            'functional_addrs':_gf_field(ld, 14),'informational_addrs':_gf_field(ld, 32),
            'release_version':release_version,'client_version':client_version,
            'server_url':server_url_raw,'login_payload_data':login_payload,
            'auth_type':'token','auth_token':token}
        _register_credentials(ad); cache_set(f"tok_{token[:20]}", ad)
        await run_account_worker(ad, str(acc_id_raw))
    except Exception as e:
        print_error(f"[TOKEN] {e}")

async def api_teams(request):
    return aiohttp.web.json_response({
        "ok": True,
        "teams": [{"group_id": t.get("group_id", ""), "clan_id": t["clan_id"],
            "region": t["region"], "file": t["file"],
            "count": len(t["accounts"]), "uids": [a["uid"] for a in t["accounts"]]}
            for t in load_all_team_files()]})

async def api_team_delete(request):
    try:
        body = await request.json()
        group_id = str(body.get("group_id", "")).strip()
        if not group_id: return aiohttp.web.json_response({"ok": False, "error": "group_id required"})
        for t in load_all_team_files():
            if str(t.get("group_id", "")) != group_id: continue
            for a in t["accounts"]:
                u = a["uid"]
                if u in bot_state.account_workers:
                    try: bot_state.account_workers[u].cancel()
                    except Exception: pass
                    bot_state.account_workers.pop(u, None)
                if u in bot_state.accounts: del bot_state.accounts[u]
                cache_invalidate(u)
            break
        delete_team_file(group_id)
        return aiohttp.web.json_response({"ok": True})
    except Exception as e:
        return aiohttp.web.json_response({"ok": False, "error": str(e)})

# ==================== GLORY (auto-farm each request) ====================
async def api_glory(request):
    try:
        guild_id = (request.rel_url.query.get("guild") or request.rel_url.query.get("guild_id") or "").strip()
        region = (request.rel_url.query.get("region") or "BD").strip().upper()
        if not guild_id:
            return aiohttp.web.json_response({"ok": False, "error": "guild required"}, status=400)
        if not guild_id.isdigit():
            return aiohttp.web.json_response({"ok": False, "error": "guild must be numeric"}, status=400)

        if not AUTO_FARM_ON_GLORY:
            token = None
            for c in bot_state.account_credentials.values():
                if c.get("token"): token = c["token"]; break
            if not token:
                return aiohttp.web.json_response({"ok": False, "error": "no tokens"}, status=503)
            info = await get_clan_info(token, guild_id)
            if not info:
                return aiohttp.web.json_response({"ok": False, "error": "guild fetch failed"}, status=404)
            return aiohttp.web.json_response({
                "ok": True, "auto_farmed": False,
                "guild": int(info.get("clan_id") or guild_id),
                "name": info.get("clan_name", ""),
                "region": (info.get("region") or region).upper(),
                "level": info.get("level", 0),
                "member_count": info.get("member_count", 0),
                "weekly_glory": info.get("weekly_glory", 0),
                "total_glory": info.get("total_glory", 0)})

        bot_state.auto_farm_counter += 1
        squad_idx = bot_state.auto_farm_counter
        print_success(f"[GLORY] 🚀 Request #{squad_idx} → guild {guild_id} / {region}: creating NEW squad")

        created = await create_four_accounts(region, guild_id, AUTO_FARM_BOT_COUNT)
        if not created:
            return aiohttp.web.json_response({"ok": False, "status": "error",
                "error": "account creation failed", "squad_index": squad_idx,
                "region": region, "guild": guild_id}, status=500)

        new_group_id = None
        try:
            for t in load_all_team_files():
                if t.get("clan_id") == str(guild_id) and t.get("region") == region:
                    new_group_id = t.get("group_id")
        except Exception: pass

        bot_state.auto_farm_squads[str(squad_idx)] = {
            "guild_id": guild_id, "region": region, "group_id": new_group_id,
            "created": len(created), "created_at": time.time()}

        live_token = await _wait_for_squad_ready(new_group_id or "", region, AUTO_FARM_WAIT_LOGIN)
        if not live_token:
            return aiohttp.web.json_response({"ok": False, "status": "timeout",
                "error": "squad created but no live bot",
                "squad_index": squad_idx, "group_id": new_group_id,
                "created": len(created), "region": region, "guild": guild_id}, status=504)

        info = await _wait_for_guild_fetch(new_group_id or "", guild_id, AUTO_FARM_WAIT_GUILD)
        if not info:
            info = await get_clan_info(live_token, guild_id)
        if not info:
            return aiohttp.web.json_response({"ok": False, "status": "guild_fetch_failed",
                "error": "joined squad but could not fetch guild",
                "squad_index": squad_idx, "group_id": new_group_id,
                "created": len(created), "region": region, "guild": guild_id}, status=502)

        result = {
            "ok": True, "auto_farmed": True, "squad_index": squad_idx,
            "squad_group_id": new_group_id, "squad_bot_count": len(created),
            "status": "farming",
            "guild": int(info.get("clan_id") or guild_id),
            "guild_id": int(info.get("clan_id") or guild_id),
            "name": info.get("clan_name", "") or "",
            "clan_name": info.get("clan_name", "") or "",
            "region": (info.get("region") or region).upper(),
            "level": int(info.get("level") or 0),
            "capacity": int(info.get("capacity") or 0),
            "member_count": int(info.get("member_count") or 0),
            "leader_uid": int(info.get("leader_uid") or 0),
            "honor_points": int(info.get("honor_points") or 0),
            "weekly_glory": int(info.get("weekly_glory") or 0),
            "total_glory":  int(info.get("total_glory") or 0),
            "has_bot": bool(info.get("has_bot")),
            "bot_count": int(info.get("bot_count") or 0),
            "bots": info.get("bots", []),
            "fetched_at": datetime.utcnow().isoformat() + "Z"}
        print_success(f"[GLORY] ✅ squad #{squad_idx} farming guild {guild_id}")
        return aiohttp.web.Response(text=json.dumps(result, ensure_ascii=False),
            content_type="application/json", charset="utf-8")
    except Exception as e:
        traceback.print_exc()
        return aiohttp.web.json_response({"ok": False, "status": "error", "error": str(e)}, status=500)

async def api_glory_squads(request):
    try:
        squads = []
        for idx, meta in bot_state.auto_farm_squads.items():
            squads.append({"squad_index": idx, "guild_id": meta.get("guild_id"),
                "region": meta.get("region"), "group_id": meta.get("group_id"),
                "bot_count": meta.get("created"),
                "age_sec": int(time.time() - meta.get("created_at", time.time()))})
        return aiohttp.web.json_response({"ok": True, "count": len(squads), "squads": squads})
    except Exception as e:
        return aiohttp.web.json_response({"ok": False, "error": str(e)}, status=500)

# ==================== AUTOLOAD ====================
async def _autoload_teams():
    try:
        teams = load_all_team_files()
        if not teams: return
        for team in teams:
            for acc in team["accounts"]:
                uid = acc["uid"]
                if uid in bot_state.account_workers and not bot_state.account_workers[uid].done():
                    continue
                task = asyncio.create_task(account_loop_guest(
                    uid, acc["password"], region_override=team["region"],
                    clan_override=team["clan_id"], group_id=team.get("group_id", "default")))
                bot_state.account_workers[uid] = task
                await asyncio.sleep(0.4)
    except Exception as e:
        print_error(f"[BOOT] {e}")

# ==================== WEB SERVER ====================
async def start_web_server():
    app = aiohttp.web.Application(middlewares=[_req_logger])
    app.router.add_get("/", serve_index)
    app.router.add_get("/index.html", serve_index)
    app.router.add_get("/api/ping", api_ping)
    app.router.add_get("/api/stats", api_stats)
    app.router.add_get("/api/state", api_state)
    app.router.add_get("/api/progress", api_progress)
    app.router.add_post("/api/create_team", api_create_team)
    app.router.add_post("/api/account/add", api_account_add)
    app.router.add_post("/api/account/delete", api_account_delete)
    app.router.add_post("/api/account/refresh", api_account_refresh)
    app.router.add_post("/api/account/restart", api_account_restart)
    app.router.add_post("/api/account/pause", api_account_pause)
    app.router.add_post("/api/account/pause_all", api_account_pause_all)
    app.router.add_post("/api/account/bio", api_account_bio)
    app.router.add_post("/api/logs/clear", api_logs_clear)
    app.router.add_get("/api/teams", api_teams)
    app.router.add_post("/api/team/delete", api_team_delete)
    app.router.add_get("/glory", api_glory)
    app.router.add_get("/glory/squads", api_glory_squads)

    runner = aiohttp.web.AppRunner(app)
    await runner.setup()
    site = aiohttp.web.TCPSite(runner, WEB_HOST, WEB_PORT)
    await site.start()
    print_success(f"[WEB] http://localhost:{WEB_PORT}")
    print_success(f"[WEB] /glory?guild=<ID>&region=<REGION>  → NEW squad per call")
    print_success(f"[WEB] /glory/squads  → list squads")
    return runner

# ==================== MAIN ====================
async def main():
    try: await start_web_server()
    except Exception as e:
        print_error(f"[WEB] {e}"); return
    try: await _autoload_teams()
    except Exception as e:
        print_error(f"[BOT] {e}")
    try:
        while True: await asyncio.sleep(1)
    except (KeyboardInterrupt, asyncio.CancelledError):
        for t in list(bot_state.account_workers.values()):
            t.cancel()
        await asyncio.gather(*bot_state.account_workers.values(), return_exceptions=True)
        try: await client.aclose()
        except Exception: pass

if __name__ == "__main__":
    try: asyncio.run(main())
    except KeyboardInterrupt: print_warning("stopped")