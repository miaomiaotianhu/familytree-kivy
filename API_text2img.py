# -*- coding: utf-8 -*-
"""
家谱关系网络 · Kivy 本地程序 (自然关系版 + 账号密码保护)
==========================================
核心思路:
  - 录入极简: 只填 本人(姓名/性别/八字) + 配偶(姓名/性别/八字) + 子女列表(姓名/性别/八字)
  - 关系只存两种: 配偶(spouse_of) 与 生(parent_of)
  - 长子/次子/长女/次女/兄/弟/姐/妹/父/母 等称谓全部由程序自动推算, 无需手动填写
  - 展示: 搜索人名 -> 同名则选择 -> 以该人为中心, 关系线上标注称谓(父/母/配偶/长子/次女...)
          节点只显示 人名+性别; 点击节点弹出该人八字与家庭信息
  - 编辑: 「编辑」页(位于「录入数据」旁), 按主记录 ID 定位该人资料,
          可修改 姓名/八字(修正录入错误), 人际关系(配偶/父母/子女)不可编辑、保持不变;
          并可「删除此人」(连同其所有关系一并删除, 带确认)
  - 防重复: 保存关系前查重, 同一关系(配偶/父母/子女)不重复插入;
          程序启动时自动清理已存在的重复关系
  - 账号与安全(本版新增):
      * 注册: 自动生成账号ID, 用户自设密码(至少4位)
      * 登录: 每次打开程序必须先输入 账号ID+密码 才能进入界面读取数据
      * 数据隔离: 每个账号只看到自己的数据; 忘记密码只能重新注册, 新账号需重新录入,
                  无法读取旧账号信息
      * 防破解: 密码以加盐 PBKDF2 哈希存储(不存明文); 连续输错5次锁定5分钟;
                人名/八字以由密码派生的密钥加密后存储, 直接打开数据库文件也读不到明文

示例数据录入:
  张三(男) 配偶 李逵(女), 子女: 张思(男),张柳(女),张其(男),张聊(女)

运行:  python kivy_family_graph.py
打包:  见 buildozer.spec + build_android.sh (文件底部注释)

数据库路径 (本版修改):
  - 桌面 (Windows/Linux/macOS): 保持原行为, family.db 仍在 .py 同目录
  - Android: 自动改用 Kivy user_data_dir (= 应用私有内部存储
    /data/data/<包名>/files, 可写且持久), 避免写入 APK 解包目录
    (可能只读、且应用升级时被重建导致数据丢失)

字体(强制嵌入宋体, 安卓无系统宋体也能显示):
  - 把 simsun.ttc 放在本 .py 同目录(安卓打包随程序分发, 优先加载)
  - Windows 开发机固定路径: D:\\PythonProject\\simsun.ttc
"""
import os
import sqlite3
import math
import hashlib
import hmac
import base64
import time
from collections import defaultdict

from kivy.app import App
from kivy.core.window import Window
from kivy.core.text import LabelBase, DEFAULT_FONT
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.floatlayout import FloatLayout
from kivy.uix.tabbedpanel import TabbedPanel, TabbedPanelItem
from kivy.uix.scrollview import ScrollView
from kivy.uix.button import Button
from kivy.uix.label import Label
from kivy.uix.textinput import TextInput
from kivy.uix.spinner import Spinner, SpinnerOption
from kivy.uix.popup import Popup
from kivy.graphics import Color, Line, Rectangle, BorderImage
from kivy.clock import Clock

APP_DIR = os.path.dirname(os.path.abspath(__file__))


# ============================================================
# 数据库目录 (本版修改)
#   桌面: 保持原行为, family.db 仍在 .py 同目录(可写则用, 不可写自动回退)
#   安卓: 使用 Kivy user_data_dir (= getFilesDir() = /data/data/<包名>/files),
#         应用私有内部存储, 可写且持久, 不会被 APK 解包目录重建/只读所影响
# ============================================================
def _is_writable_dir(path):
    try:
        return os.access(path, os.W_OK)
    except Exception:
        return False


def _is_android():
    try:
        from kivy.utils import platform
        if str(platform) == "android":
            return True
    except Exception:
        pass
    return ("ANDROID_ARGUMENT" in os.environ
            or "ANDROID_PRIVATE" in os.environ
            or "ANDROID_APP_PATH" in os.environ)


def _app_data_dir():
    """返回可写且持久的应用数据目录。"""
    if _is_android():
        app = App.get_running_app()
        d = app.user_data_dir if app is not None else None
        if not d:
            # 极端情况(应用实例尚未就绪): 退回解包目录下的 app 子目录
            d = os.path.join(os.environ.get("ANDROID_ARGUMENT", APP_DIR), "app")
        try:
            os.makedirs(d, exist_ok=True)
        except Exception:
            pass
        return d
    if _is_writable_dir(APP_DIR):
        return APP_DIR
    app = App.get_running_app()
    if app is not None:
        d = app.user_data_dir
        try:
            os.makedirs(d, exist_ok=True)
        except Exception:
            pass
        return d
    return APP_DIR


def db_path():
    """family.db 的完整路径(每次调用实时解析, 首次建库前也能正确落位)"""
    return os.path.join(_app_data_dir(), "family.db")


# ============================================================
# 宋体加载 (强制嵌入: 优先程序同目录 simsun.ttc, 其次固定 Windows 路径)
# ============================================================
FONT_NAME = "simsun.ttc"


def find_chinese_font():
    candidates = [
        os.path.join(APP_DIR, FONT_NAME),     # 安卓打包: 字体随程序一起分发(强制嵌入)
        r"D:\PythonProject\simsun.ttc",       # Windows 开发环境固定路径
        r"C:\Windows\Fonts\simsun.ttc",
        r"C:\Windows\Fonts\msyh.ttc", r"C:\Windows\Fonts\msyhbd.ttc",
        r"C:\Windows\Fonts\simhei.ttf",
        r"C:\Windows\Fonts\simkai.ttf",
        "/System/Library/Fonts/PingFang.ttc",
        "/System/Library/Fonts/STHeiti Light.ttc",
        "/System/Library/Fonts/Hiragino Sans GB.ttc",
        "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
        "/usr/share/fonts/truetype/wqy/wqy-microhei.ttc",
        "/system/fonts/NotoSansCJK-Regular.ttc",
        "/system/fonts/NotoSansCJK.ttc", "/system/fonts/DroidSansFallback.ttf",
    ]
    for p in candidates:
        if os.path.exists(p):
            return p
    return None


def setup_chinese_font():
    path = find_chinese_font()
    if not path:
        print("[字体] 未找到宋体 simsun.ttc, 界面中文可能显示为方块")
        print("[字体] 请将 simsun.ttc 放到程序同目录, 或 D:\\PythonProject\\simsun.ttc")
        return
    try:
        LabelBase.register(name=DEFAULT_FONT,
                           fn_regular=path, fn_bold=path,
                           fn_italic=path, fn_bolditalic=path)
        print("[字体] 已加载宋体:", path)
    except Exception as e:
        print("[字体] 宋体加载失败:", e)


# ============================================================
# 会话状态与加密 (仅登录后有效)
# ============================================================
CURRENT_OWNER = None      # 当前登录的 account_id
CURRENT_KEY = None        # 由密码派生的数据密钥(bytes), 只在内存中, 不落盘

PBKDF2_ITERS = 150000     # 密钥派生迭代次数(越高越难暴力破解)
MAX_ATTEMPTS = 5          # 连续输错上限
LOCK_SECONDS = 300        # 锁定秒数(5分钟)


def _rand_salt():
    return os.urandom(16).hex()


def _hash_password(password, salt_hex):
    """密码 -> 加盐 PBKDF2 哈希(用于校验, 不存明文)"""
    return hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), bytes.fromhex(salt_hex),
        PBKDF2_ITERS, dklen=32).hex()


def _derive_data_key(password, salt_key_hex):
    """密码 -> 数据加密密钥(PBKDF2 派生, 仅在登录后存在于内存)"""
    return hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), bytes.fromhex(salt_key_hex),
        PBKDF2_ITERS, dklen=32)


def _keystream(key, nonce, length):
    """HMAC-SHA256 密钥流, 与明文异或得到密文(每字段独立 nonce)"""
    out = b""
    i = 0
    while len(out) < length:
        out += hmac.new(key, nonce + i.to_bytes(4, "big"), "sha256").digest()
        i += 1
    return out[:length]


def enc_field(key, nonce_hex, text):
    if text is None:
        text = ""
    data = text.encode("utf-8")
    ks = _keystream(key, bytes.fromhex(nonce_hex), len(data))
    return base64.b64encode(bytes(a ^ b for a, b in zip(data, ks))).decode("ascii")


def dec_field(key, nonce_hex, b64text):
    if not b64text:
        return ""
    ct = base64.b64decode(b64text)
    ks = _keystream(key, bytes.fromhex(nonce_hex), len(ct))
    return bytes(a ^ b for a, b in zip(ct, ks)).decode("utf-8")


def begin_session(account_id, key):
    global CURRENT_OWNER, CURRENT_KEY
    CURRENT_OWNER = account_id
    CURRENT_KEY = key


def _owner():
    if CURRENT_OWNER is None or CURRENT_KEY is None:
        raise RuntimeError("未登录")
    return CURRENT_OWNER


# 数据层 (SQLite)
# ============================================================
def init_db():
    """建表(含旧版数据无损备份)。账号表 + 按账号隔离、加密存储的人与关系表。"""
    c = sqlite3.connect(db_path())
    c.execute("CREATE TABLE IF NOT EXISTS accounts("
              "account_id INTEGER PRIMARY KEY AUTOINCREMENT, "
              "salt_hash TEXT, salt_key TEXT, pass_hash TEXT, "
              "fail_count INTEGER DEFAULT 0, lock_until INTEGER DEFAULT 0, "
              "created_at INTEGER)")
    # 旧版无 owner_id 的表 -> 备份为 persons_legacy/relations_legacy(不删除, 旧数据保留)
    cols = [r[1] for r in c.execute("PRAGMA table_info(persons)")]
    if cols and "owner_id" not in cols:
        if not c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='persons_legacy'").fetchone():
            c.execute("ALTER TABLE persons RENAME TO persons_legacy")
        else:
            c.execute("DROP TABLE IF EXISTS persons")
        rcols = [r[1] for r in c.execute("PRAGMA table_info(relations)")]
        if rcols and "owner_id" not in rcols:
            if not c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='relations_legacy'").fetchone():
                c.execute("ALTER TABLE relations RENAME TO relations_legacy")
            else:
                c.execute("DROP TABLE IF EXISTS relations")
    c.execute("CREATE TABLE IF NOT EXISTS persons("
              "person_id INTEGER PRIMARY KEY AUTOINCREMENT, "
              "owner_id INTEGER, name_enc TEXT, gender TEXT, "
              "birth_bazi_enc TEXT, nonce TEXT)")
    c.execute("CREATE TABLE IF NOT EXISTS relations("
              "relation_id INTEGER PRIMARY KEY AUTOINCREMENT, "
              "owner_id INTEGER, person_a_id INTEGER, person_b_id INTEGER, "
              "relation_type TEXT)")
    c.commit()
    c.close()
    _dedupe_relations()   # 启动即清理历史重复关系


def _dedupe_relations():
    """清理当前账号关系表里的重复记录, 同一对(A,B)与同类型只保留第一条。
       spouse_of 中 (A,B) 与 (B,A) 视为同一条。仅删多余, 不碰任何唯一关系。"""
    try:
        c = sqlite3.connect(db_path())
        rows = c.execute(
            "SELECT relation_id,owner_id,person_a_id,person_b_id,relation_type "
            "FROM relations").fetchall()
        seen = set()
        dels = []
        for rid, ow, a, b, t in rows:
            key = (ow, min(a, b), max(a, b), t) if t == "spouse_of" else (ow, a, b, t)
            if key in seen:
                dels.append(rid)
            else:
                seen.add(key)
        for rid in dels:
            c.execute("DELETE FROM relations WHERE relation_id=?", (rid,))
        if dels:
            c.commit()
            print("[数据] 已自动清理 %d 条重复关系" % len(dels))
        c.close()
    except Exception as e:
        print("[数据] 清理重复关系时出错(不影响使用):", e)


# ---- 账号 ----
def register_account(password):
    """注册新账号, 返回 (account_id, salt_key)。账号ID由程序自动生成。"""
    if not password or len(password) < 4:
        raise ValueError("密码至少需要 4 位")
    salt_hash = _rand_salt()
    salt_key = _rand_salt()
    c = sqlite3.connect(db_path())
    cur = c.execute(
        "INSERT INTO accounts(salt_hash,salt_key,pass_hash,fail_count,lock_until,created_at) "
        "VALUES(?,?,?,0,0,?)",
        (salt_hash, salt_key, _hash_password(password, salt_hash), int(time.time())))
    c.commit()
    aid = cur.lastrowid
    c.close()
    return aid, salt_key


def check_login(account_id, password):
    """校验登录。返回 (ok, account_id, data_key, message)。
       连续输错 MAX_ATTEMPTS 次后锁定 LOCK_SECONDS 秒(持久化, 重启不重置)。"""
    c = sqlite3.connect(db_path())
    row = c.execute(
        "SELECT account_id,salt_hash,salt_key,pass_hash,fail_count,lock_until "
        "FROM accounts WHERE account_id=?", (account_id,)).fetchone()
    c.close()
    if not row:
        _hash_password(password, _rand_salt())   # 等时化, 防止探测账号是否存在
        return (False, None, None, "账号或密码错误")
    aid, sh, sk, ph, fc, lock = row
    now = int(time.time())
    if lock > now:
        return (False, None, None, "失败次数过多, 请 %d 秒后再试" % (lock - now))
    if hmac.compare_digest(_hash_password(password, sh), ph):
        c = sqlite3.connect(db_path())
        c.execute("UPDATE accounts SET fail_count=0, lock_until=0 WHERE account_id=?", (aid,))
        c.commit()
        c.close()
        key = _derive_data_key(password, sk)
        return (True, aid, key, "登录成功")
    fc += 1
    if fc >= MAX_ATTEMPTS:
        lock = now + LOCK_SECONDS
        fc = 0
        msg = "连续失败 %d 次, 账号已锁定 %d 秒" % (MAX_ATTEMPTS, LOCK_SECONDS)
    else:
        msg = "账号或密码错误 (还可尝试 %d 次)" % (MAX_ATTEMPTS - fc)
    c = sqlite3.connect(db_path())
    c.execute("UPDATE accounts SET fail_count=?, lock_until=? WHERE account_id=?", (fc, lock, aid))
    c.commit()
    c.close()
    return (False, None, None, msg)


# ---- 人员(加密存储) ----
def find_by_name(name):
    c = sqlite3.connect(db_path())
    rows = c.execute(
        "SELECT person_id,name_enc,gender,birth_bazi_enc,nonce FROM persons "
        "WHERE owner_id=?", (_owner(),)).fetchall()
    c.close()
    out = []
    for pid, ne, g, be, nonce in rows:
        nm = dec_field(CURRENT_KEY, nonce, ne)
        if nm == name:
            out.append((pid, nm, g, dec_field(CURRENT_KEY, nonce, be)))
    return out


def insert_person(name, gender, bazi):
    nonce = os.urandom(16).hex()
    c = sqlite3.connect(db_path())
    cur = c.execute(
        "INSERT INTO persons(owner_id,name_enc,gender,birth_bazi_enc,nonce) "
        "VALUES(?,?,?,?,?)",
        (_owner(), enc_field(CURRENT_KEY, nonce, name), gender,
         enc_field(CURRENT_KEY, nonce, bazi), nonce))
    c.commit()
    pid = cur.lastrowid
    c.close()
    return pid


def get_person(pid):
    c = sqlite3.connect(db_path())
    r = c.execute(
        "SELECT person_id,name_enc,gender,birth_bazi_enc,nonce FROM persons "
        "WHERE person_id=? AND owner_id=?", (pid, _owner())).fetchone()
    c.close()
    if not r:
        return None
    return (r[0], dec_field(CURRENT_KEY, r[4], r[1]), r[2],
            dec_field(CURRENT_KEY, r[4], r[3]))


def update_person(pid, name, bazi):
    """编辑页: 仅更新姓名与八字, 不触碰关系。返回是否成功。"""
    c = sqlite3.connect(db_path())
    r = c.execute("SELECT nonce FROM persons WHERE person_id=? AND owner_id=?",
                  (pid, _owner())).fetchone()
    if not r:
        c.close()
        return False
    nonce = r[0]
    c.execute(
        "UPDATE persons SET name_enc=?, birth_bazi_enc=? "
        "WHERE person_id=? AND owner_id=?",
        (enc_field(CURRENT_KEY, nonce, name), enc_field(CURRENT_KEY, nonce, bazi),
         pid, _owner()))
    c.commit()
    c.close()
    return True


def delete_person(pid):
    """删除此人及其所有关系(配偶/父母/子女), 不可恢复。"""
    c = sqlite3.connect(db_path())
    c.execute("DELETE FROM persons WHERE person_id=? AND owner_id=?", (pid, _owner()))
    c.execute("DELETE FROM relations WHERE owner_id=? AND (person_a_id=? OR person_b_id=?)",
              (_owner(), pid, pid))
    c.commit()
    c.close()


# ---- 关系 ----
def insert_relation(a, b, t):
    """新增关系, 保存前查重: 已存在同一条则跳过。spouse_of 中 (A,B) 与 (B,A) 视为同一条。"""
    c = sqlite3.connect(db_path())
    if t == "spouse_of":
        hit = c.execute(
            "SELECT 1 FROM relations WHERE owner_id=? AND relation_type='spouse_of' "
            "AND ((person_a_id=? AND person_b_id=?) OR (person_a_id=? AND person_b_id=?))",
            (_owner(), a, b, b, a)).fetchone()
    else:
        hit = c.execute(
            "SELECT 1 FROM relations WHERE owner_id=? AND relation_type=? "
            "AND person_a_id=? AND person_b_id=?",
            (_owner(), t, a, b)).fetchone()
    if not hit:
        c.execute(
            "INSERT INTO relations(owner_id,person_a_id,person_b_id,relation_type) "
            "VALUES(?,?,?,?)", (_owner(), a, b, t))
        c.commit()
    c.close()


def load_all():
    """加载当前账号全部数据, 返回 (meta, adj, edges, spouse, children, parents)"""
    meta = {}
    adj = defaultdict(list)
    edges = []
    spouse = set()
    children = defaultdict(list)
    parents = defaultdict(list)
    c = sqlite3.connect(db_path())
    for pid, ne, g, be, nonce in c.execute(
            "SELECT person_id,name_enc,gender,birth_bazi_enc,nonce FROM persons "
            "WHERE owner_id=?", (_owner(),)):
        meta[pid] = (pid, dec_field(CURRENT_KEY, nonce, ne), g,
                     dec_field(CURRENT_KEY, nonce, be))
    for a, b, t in c.execute(
            "SELECT person_a_id,person_b_id,relation_type FROM relations "
            "WHERE owner_id=?", (_owner(),)):
        if b not in adj[a]:
            adj[a].append(b)
        if a not in adj[b]:
            adj[b].append(a)
        if (a, b) not in edges:
            edges.append((a, b))
        if t == "spouse_of":
            spouse.add((a, b))
            spouse.add((b, a))
        elif t == "parent_of":
            children[a].append(b)
            parents[b].append(a)
    c.close()
    return meta, adj, edges, spouse, children, parents


# ============================================================
# 称谓自动推算 (纯函数, 便于测试)
# ============================================================
MAN_TITLES = ["长子", "次子", "三子", "四子", "五子", "六子", "七子", "八子", "九子"]
WOMAN_TITLES = ["长女", "次女", "三女", "四女", "五女", "六女", "七女", "八女", "九女"]


def child_title(parent, child, children, meta):
    """child 相对 parent 的称谓: 长子/次子/长女/次女...(同父同性别排行, 按 person_id 近似长幼)"""
    g = meta.get(child, (None, None, "未知", ""))[2]
    if g not in ("男", "女"):
        return "子女"
    sib = sorted(children.get(parent, []))
    same = [x for x in sib if meta.get(x, (0, "", "未知", ""))[2] == g]
    try:
        i = same.index(child)
    except ValueError:
        return "子女"
    titles = MAN_TITLES if g == "男" else WOMAN_TITLES
    if i < len(titles):
        return titles[i]
    return "第%d%s" % (i + 1, "子" if g == "男" else "女")


def sibling_title(me, other, parents, meta):
    """other 相对 me 的称谓(有共同父母): 兄/弟/姐/妹"""
    me_p = set(parents.get(me, []))
    other_p = set(parents.get(other, []))
    if not (me_p & other_p):
        return ""
    other_g = meta.get(other, (None, None, "未知", ""))[2]
    me_id = meta.get(me, (other,))[0]
    other_id = meta.get(other, (me,))[0]
    if other_id < me_id:
        return "兄" if other_g == "男" else "姐"
    return "弟" if other_g == "男" else "妹"


def rel_of(me, other, spouse, children, parents, meta):
    """other 相对 me 的称谓"""
    if (me, other) in spouse or (other, me) in spouse:
        return "配偶"
    if other in children.get(me, []):
        return child_title(me, other, children, meta)
    if me in children.get(other, []):
        return "父" if meta.get(other, (None, None, "男", ""))[2] == "男" else "母"
    if set(parents.get(me, [])) & set(parents.get(other, [])):
        return sibling_title(me, other, parents, meta)
    return ""


# ============================================================
# 布局算法: BFS + 力导向 (纯 Python)
# ============================================================
def compute_layout(adj, edges, center, radius=3, spouse=None,
                   children_map=None, parents_map=None):
    """分层树枝布局(家谱树): 按"代"分行, 父母在上/子女在下, 夫妻并排, 子女居中。
       以 center 所在代居中。返回 {pid:(x,y)} 归一化坐标 与 子图边列表。"""
    spouse = spouse or set()
    children_map = children_map or defaultdict(list)
    parents_map = parents_map or defaultdict(list)

    nodes = set()
    nodes.add(center)
    dist = {center: 0}
    frontier = [center]
    while frontier:
        nf = []
        for u in frontier:
            if dist[u] >= radius:
                continue
            for v in adj.get(u, []):
                if v not in nodes:
                    nodes.add(v)
                    dist[v] = dist[u] + 1
                    nf.append(v)
        frontier = nf
    sub_edges = [(a, b) for a, b in edges if a in nodes and b in nodes]

    gen = {center: 0}
    for _ in range(len(nodes) + 1):
        changed = False
        for v in list(nodes):
            if v not in gen:
                continue
            for sp in adj.get(v, []):
                if (sp in nodes and sp not in gen and
                        ((v, sp) in spouse or (sp, v) in spouse)):
                    gen[sp] = gen[v]
                    changed = True
            for c in children_map.get(v, []):
                if c in nodes and c not in gen:
                    gen[c] = gen[v] + 1
                    changed = True
            for p in parents_map.get(v, []):
                if p in nodes and p not in gen:
                    gen[p] = gen[v] - 1
                    changed = True
        if not changed:
            break
    for v in nodes:
        if v not in gen:
            gen[v] = 0

    levels = sorted(set(gen.values()))
    rows = {g: [v for v in nodes if gen[v] == g] for g in levels}
    min_g = levels[0]
    span = max(levels[-1] - min_g, 1)

    unit_of = {}
    units = {}
    for g in levels:
        rlist = list(rows[g])
        used = set()
        us = []
        for v in rlist:
            if v in used:
                continue
            sp = None
            for nb in adj.get(v, []):
                if (nb in rows[g] and nb not in used and
                        ((v, nb) in spouse or (nb, v) in spouse)):
                    sp = nb
                    break
            if sp is not None:
                us.append([v, sp])
                used.add(v)
                used.add(sp)
            else:
                us.append([v])
                used.add(v)
        units[g] = us
        for i, u in enumerate(us):
            for v in u:
                unit_of[v] = (g, i)
    for _ in range(6):
        for g in levels:
            us = units[g]
            def bary(u):
                tot = 0
                cnt = 0
                for v in u:
                    for nb in adj.get(v, []):
                        if nb in unit_of:
                            ng, ni = unit_of[nb]
                            if abs(ng - g) == 1:
                                tot += ni
                                cnt += 1
                return tot / cnt if cnt else len(us)
            us.sort(key=bary)
            for i, u in enumerate(us):
                for v in u:
                    unit_of[v] = (g, i)

    pos = {}
    for g in levels:
        us = units[g]
        n = len(us)
        for i, u in enumerate(us):
            cx = (i + 1) / (n + 1)
            for j, v in enumerate(u):
                off = (j - 0.5) * 0.05 if len(u) == 2 else 0.0
                y = 0.86 - (g - min_g) / span * 0.72
                pos[v] = (max(0.03, min(0.97, cx + off)), y)
    return pos, sub_edges


# ============================================================
# 中轴血统树布局
# ============================================================
def compute_spine_layout(meta, adj, spouse, children_map, parents_map, center):
    """中轴血统树 -> 每代一行结构。
       spine 中轴: 中心人 -> 其父 -> 祖父... 一直向上追溯(父系男性链; 中心可为女性, 其余为男)。
       返回 (levels, spine):
         levels = [ {node, spouse, spouse_parents, kids}, ... ], 下标0=最老祖辈, 末位=中心
         kids 已排除中轴上的子女(中轴上的子单独成下一行, 不在此行右侧重复)
    """
    spine = [center]
    seen = {center}
    cur = center
    while True:
        f = None
        for p in parents_map.get(cur, []):
            if meta.get(p, (None, None, "男", ""))[2] == "男":
                f = p
                break
        if f is None or f in seen:
            break
        spine.append(f)
        seen.add(f)
        cur = f
    spine = spine[::-1]
    spine_set = set(spine)

    levels = []
    for node in spine:
        sps = [x for x in adj.get(node, [])
               if (node, x) in spouse or (x, node) in spouse]
        sp = sps[0] if sps else None
        spp = list(parents_map.get(sp, []))[:2] if sp is not None else []
        kids = sorted(children_map.get(node, []))
        kids = [c for c in kids if c not in spine_set]
        levels.append({"node": node, "spouse": sp,
                       "spouse_parents": spp, "kids": kids})
    return levels, spine


# ============================================================
# UI 配色 (统一规范)
#  全部 RGBA, 0~1。
#  按钮:      平时 #6686b2 / 按下(选中) #7ca1d5
#  危险按钮:  平时 #8a3535 / 按下 #a04545
#  顶部Tab:   平时 #cccccc / 选中 #6686b2
#  文本框:    边框 #e5e5e5 / 内部底色 #f6f6f6
# ============================================================
C_BG      = (0.985, 0.985, 0.99, 1)   # 页面背景 近白
C_PANEL   = (1, 1, 1, 1)              # 面板 纯白
C_PAPER   = (0.99, 0.985, 0.98, 1)    # 画布 暖白(关系图区域)
C_BAR     = (0.97, 0.97, 0.975, 1)    # 工具栏 浅灰

C_BTN_NORMAL = (0x66 / 255, 0x86 / 255, 0xb2 / 255, 1)   # 按钮平时 #6686b2
C_BTN_DOWN   = (0x7c / 255, 0xa1 / 255, 0xd5 / 255, 1)   # 按钮按下/选中 #7ca1d5
C_BTN_DANGER    = (0x8a / 255, 0x35 / 255, 0x35 / 255, 1)  # 危险按钮 #8a3535
C_BTN_DANGER_DN = (0xa0 / 255, 0x45 / 255, 0x45 / 255, 1)  # 危险按钮按下 #a04545
C_TAB_NORMAL = (0xcc / 255, 0xcc / 255, 0xcc / 255, 1)   # Tab 平时 #cccccc
C_TAB_DOWN   = C_BTN_NORMAL                              # Tab 选中 #6686b2
C_BTN_WHITE  = (1, 1, 1, 1)             # 按钮文字 白色

C_TEXT    = (0.25, 0.27, 0.30, 1)     # 主文字 深灰
C_LINE    = (0.60, 0.63, 0.66, 1)     # 连线 中性灰

N_MALE_BG  = (0.91, 0.93, 0.95, 1)    # 男节点 浅灰蓝
N_MALE_FG  = (0.30, 0.37, 0.44, 1)    # 男节点 深灰蓝字
N_FEM_BG   = (0.96, 0.94, 0.94, 1)    # 女节点 浅藕灰
N_FEM_FG   = (0.50, 0.41, 0.43, 1)    # 女节点 深灰玫字
N_CENTER_BG= (0.62, 0.50, 0.37, 1)    # 中心节点 低饱和焦糖
N_CENTER_FG= (1, 1, 1, 1)             # 中心节点 白字

C_POP_TEXT  = (0.07, 0.09, 0.11, 1)     # 弹窗文字 近黑(清晰)
C_INPUT_BG  = (0xf6 / 255, 0xf6 / 255, 0xf6 / 255, 1)   # 文本框内底 #f6f6f6
C_INPUT_BORDER = (0xe5 / 255, 0xe5 / 255, 0xe5 / 255, 1)  # 文本框边框 #e5e5e5

GAP = 8


def L(text, **kw):
    """白底深色文字标签"""
    kw.setdefault("color", C_TEXT)
    return Label(text=text, **kw)


def _solid_bg(w, color):
    with w.canvas.before:
        c = Color(*color)
        r = Rectangle(pos=w.pos, size=w.size)
    w.bind(pos=lambda *a: setattr(r, "pos", w.pos),
           size=lambda *a: setattr(r, "size", w.size))
    return c


def _flat(b, bg, fg=(1, 1, 1, 1)):
    b.background_normal = ""
    b.background_down = ""
    b.background_color = (1, 1, 1, 0)
    b.color = fg
    _solid_bg(b, bg)
    return b


def _btn(b):
    b.background_normal = ""
    b.background_down = ""
    b.background_disabled_normal = ""
    b.background_disabled_down = ""
    b.background_color = (1, 1, 1, 0)
    b.color = C_BTN_WHITE
    fill = _solid_bg(b, C_BTN_NORMAL)

    def _on_state(inst, state):
        fill.rgba = C_BTN_DOWN if state == "down" else C_BTN_NORMAL

    b.bind(state=_on_state)
    return b


def _btn_danger(b):
    """危险按钮(删除等): 平时 #8a3535, 按下 #a04545, 白字"""
    b.background_normal = ""
    b.background_down = ""
    b.background_disabled_normal = ""
    b.background_disabled_down = ""
    b.background_color = (1, 1, 1, 0)
    b.color = C_BTN_WHITE
    fill = _solid_bg(b, C_BTN_DANGER)

    def _on_state(inst, state):
        fill.rgba = C_BTN_DANGER_DN if state == "down" else C_BTN_DANGER

    b.bind(state=_on_state)
    return b


def _style_tab(tab):
    tab.background_normal = ""
    tab.background_down = ""
    tab.background_disabled_normal = ""
    tab.background_disabled_down = ""
    tab.background_color = (1, 1, 1, 0)
    tab.color = C_TEXT
    fill = _solid_bg(tab, C_TAB_NORMAL)

    def _on_state(inst, state):
        if state == "down":
            fill.rgba = C_TAB_DOWN
            inst.color = C_BTN_WHITE
        else:
            fill.rgba = C_TAB_NORMAL
            inst.color = C_TEXT

    tab.bind(state=_on_state)
    return tab


class StyledSpinnerOption(SpinnerOption):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        _btn(self)


def _spn(s):
    s.background_normal = ""
    s.background_down = ""
    s.background_disabled_normal = ""
    s.background_disabled_down = ""
    s.background_color = (1, 1, 1, 0)
    s.color = C_BTN_WHITE
    fill = _solid_bg(s, C_BTN_NORMAL)

    def _on_state(inst, state):
        fill.rgba = C_BTN_DOWN if state == "down" else C_BTN_NORMAL

    s.bind(state=_on_state)
    s.option_cls = StyledSpinnerOption

    def _on_open(inst, *_):
        if inst.is_open:
            dd = getattr(inst, "_dropdown", None)
            cont = getattr(dd, "container", None)
            if cont is not None:
                cont.spacing = GAP
                cont.padding = (GAP, GAP)

    s.bind(is_open=_on_open)
    return s


def _bg(w, color):
    _solid_bg(w, color)
    return w


def _set_bg(w, color):
    w.canvas.clear()
    with w.canvas:
        Color(*color)
        r = Rectangle(pos=w.pos, size=w.size)
    w.bind(pos=lambda *a: setattr(r, "pos", w.pos),
           size=lambda *a: setattr(r, "size", w.size))
    return w


def _txt(w):
    w.background_normal = ""
    w.background_active = ""
    w.background_disabled_normal = ""
    w.background_color = (0, 0, 0, 0)
    w.color = C_TEXT
    w.padding = (8, 6)

    def _strip_bg(*_):
        for instr in w.canvas.before.children:
            if isinstance(instr, BorderImage):
                instr.source = ""

    w.bind(focus=_strip_bg, disabled=_strip_bg)
    _strip_bg()
    return w


def _frame_input(ti, size_hint_x=1.0, size_hint_y=1.0):
    _txt(ti)
    ti.size_hint = (1, 1)
    inner = _bg(BoxLayout(size_hint=(1, 1)), C_INPUT_BG)
    inner.add_widget(ti)
    frame = BoxLayout(size_hint_x=size_hint_x, size_hint_y=size_hint_y,
                      padding=1)
    _bg(frame, C_INPUT_BORDER)
    frame.add_widget(inner)
    return frame, ti


def _style_popup(pop):
    try:
        pop.title_color = (1, 1, 1, 1)
        pop.separator_color = (0.55, 0.55, 0.58, 1)
    except Exception:
        pass
    return pop


def _wrap_label(text, font_size=15):
    lab = L(text=text, color=C_POP_TEXT, font_size=font_size,
            halign="left", valign="top", size_hint=(1, None))

    def _on_width(*_):
        lab.text_size = (lab.width, None)

    lab.bind(width=_on_width)
    lab.text_size = (lab.width, None)

    def _on_tex(*_):
        lab.height = lab.texture_size[1]

    lab.bind(texture_size=_on_tex)
    lab.height = lab.texture_size[1]
    return lab


def _scrollable_text(text, font_size=15):
    sv = ScrollView(do_scroll_x=False, do_scroll_y=True)
    sv.add_widget(_wrap_label(text, font_size=font_size))
    return sv


def msg_popup(text, title="提示", height=0.4):
    box = BoxLayout(orientation="vertical", spacing=GAP, padding=(GAP, GAP))
    _bg(box, C_PANEL)
    box.add_widget(_scrollable_text(text))
    b = _btn(Button(text="确定", size_hint_y=None, height=44))
    pop = _style_popup(Popup(title=title, content=box, size_hint=(0.8, height)))
    b.bind(on_release=lambda x: pop.dismiss())
    box.add_widget(b)
    pop.open()
    return pop


# 图渲染 (Kivy Canvas 自绘)  + 捏合缩放/平移查看
# ============================================================
class GraphView(BoxLayout):
    """中轴血统树渲染: ScrollView 上下滑动 + 缩放按钮, 避免 Scatter 触摸劫持"""
    def __init__(self, info_label, **kw):
        super().__init__(orientation="vertical", **kw)
        self.info = info_label
        self.reload()
        self.node_widgets = {}
        self.edge_labels = []
        self.center_id = None
        self.scale = 1.0
        self._Wc = 620
        self._Hc = 640
        self._levels = []
        self._spine = set()
        self._pad_x = 0
        self._pad_y = 0
        self._bw = 620
        self._cw = 620
        self._ch = 640

        bar = _bg(BoxLayout(size_hint_y=None, height=40, spacing=GAP,
                            padding=(GAP, 4)), C_BAR)
        b_minus = _btn(Button(text="缩小 −", size_hint_x=0.25))
        b_fit = _btn(Button(text="适应", size_hint_x=0.25))
        b_plus = _btn(Button(text="放大 ＋", size_hint_x=0.25))
        tip = L(text="", size_hint_x=0.01)
        b_minus.bind(on_release=lambda x: self.zoom(0.8))
        b_fit.bind(on_release=lambda x: self.fit())
        b_plus.bind(on_release=lambda x: self.zoom(1.25))
        bar.add_widget(b_minus)
        bar.add_widget(b_fit)
        bar.add_widget(b_plus)
        bar.add_widget(tip)
        self.zoom_bar = bar

        self.scroll = ScrollView(do_scroll_x=True, do_scroll_y=True)
        self.content = FloatLayout(size_hint=(None, None), size=(self._Wc, self._Hc))
        self.scroll.add_widget(self.content)
        _bg(self.scroll, C_PAPER)
        self.add_widget(self.scroll)
        self.add_widget(self.zoom_bar)

    def reload(self):
        self.meta, self.adj, self.edges, self.spouse, self.children_map, self.parents = load_all()

    def set_center(self, pid):
        self.reload()
        self.center_id = pid
        levels, spine = compute_spine_layout(self.meta, self.adj, self.spouse,
                                             self.children_map, self.parents, pid)
        self._levels = levels
        self._spine = set(spine)
        self._Wc = 620
        self._Hc = max(600, len(levels) * 150 + 120)
        self.fit()

    def fit(self):
        vw = max(self.scroll.width, self.width, 100)
        vh = max(self.scroll.height, self.height - 40, 100)
        self.scale = max(0.2, min(vw / self._Wc, vh / self._Hc))
        self._rebuild()
        cy = 0.5 if len(self._levels) <= 1 else self._yof(len(self._levels) - 1)
        Clock.schedule_once(lambda dt: self._refit_ready(cy), 0)

    def _refit_ready(self, cy):
        vw = max(self.scroll.width, 1)
        vh = max(self.scroll.height, 1)
        if vw < 20 or vh < 20:
            return
        self.scale = max(0.2, min(vw / self._Wc, vh / self._Hc))
        self._rebuild()
        self._center_on(0.5, cy)

    def zoom(self, factor):
        if not self._levels:
            return
        lx, ly = self._viewport_center()
        self.scale = max(0.2, min(4.0, self.scale * factor))
        self._rebuild()
        Clock.schedule_once(lambda dt: self._center_on(lx, ly), 0)

    def _viewport_center(self):
        vw = max(self.scroll.width, 1)
        vh = max(self.scroll.height, 1)
        bw, ch = self._bw, self._ch
        span_x = self._cw + 2 * self._pad_x - vw
        span_y = ch + 2 * self._pad_y - vh
        cx = self.scroll.scroll_x * span_x + vw / 2 - self._pad_x
        cy = self.scroll.scroll_y * span_y + vh / 2 - self._pad_y
        return (cx / bw if bw else 0.5), (cy / ch if ch else 0.5)

    def _center_on(self, lx, ly):
        vw = max(self.scroll.width, 1)
        vh = max(self.scroll.height, 1)
        bw, ch = self._bw, self._ch
        if self._cw + 2 * self._pad_x > vw:
            off = self._pad_x + lx * bw - vw / 2
            self.scroll.scroll_x = max(0.0, min(1.0, off / (self._cw + 2 * self._pad_x - vw)))
        if ch + 2 * self._pad_y > vh:
            off = self._pad_y + ly * ch - vh / 2
            self.scroll.scroll_y = max(0.0, min(1.0, off / (ch + 2 * self._pad_y - vh)))

    def _yof(self, i):
        n = len(self._levels)
        if n <= 1:
            return 0.5
        return 0.84 - i * (0.68 / max(n - 1, 1))

    _D = 0.19
    BASE_W = 620

    def _col_x(self, kind, k=0):
        if kind == "spouse":
            return 0.5 - self._D
        if kind == "spp":
            return 0.5 - 2 * self._D
        if kind == "kid":
            return 0.5 + self._D + k * self._D
        return 0.5

    def _rebuild(self):
        self.content.clear_widgets()
        self.content.canvas.before.clear()
        self.node_widgets = {}
        self.edge_labels = []
        s = self.scale

        maxr = 0.5
        for lv in self._levels:
            n = len(lv["kids"])
            if n > 0:
                maxr = max(maxr, self._col_x("kid", n - 1))
        self._Wc = max(620, int((maxr + 0.10) * self.BASE_W))
        self._Hc = max(600, len(self._levels) * 150 + 120)
        cw, ch = self._Wc * s, self._Hc * s
        self._bw = self.BASE_W * s
        vw = max(self.scroll.width, 1)
        vh = max(self.scroll.height, 1)
        self._pad_x, self._pad_y = vw, vh
        self._cw, self._ch = cw, ch
        self.content.size = (cw + 2 * vw, ch + 2 * vh)

        for i, lv in enumerate(self._levels):
            y = self._yof(i)
            self._add_node(lv["node"], self._col_x("spine"), y, "")
            sp = lv["spouse"]
            if sp is not None:
                self._add_node(sp, self._col_x("spouse"), y, "配偶")
                spp = lv["spouse_parents"]
                for k, pp in enumerate(spp):
                    py = y + (0.05 if k == 0 else -0.05) if len(spp) == 2 else y
                    g = self.meta.get(pp, (None, None, "男", ""))[2]
                    self._add_node(pp, self._col_x("spp"), py,
                                   "父" if g == "男" else "母")
            kids = lv["kids"]
            for k, c in enumerate(kids):
                t = child_title(lv["node"], c, self.children_map, self.meta)
                self._add_node(c, self._col_x("kid", k), y, t)

        self._draw_token = (getattr(self, "_draw_token", 0) or 0) + 1
        self._draw(self._draw_token)

    def _add_node(self, pid, x, y, prefix=""):
        p = self.meta.get(pid)
        if not p:
            return
        s = self.scale
        bw, ch = self._bw, self._ch
        text = ("%s·" % prefix if prefix else "") + "%s·%s" % (p[1], p[2])
        g = p[2]
        if pid == self.center_id:
            bg, fg, bold = N_CENTER_BG, N_CENTER_FG, True
        elif g == "男":
            bg, fg, bold = N_MALE_BG, N_MALE_FG, False
        else:
            bg, fg, bold = N_FEM_BG, N_FEM_FG, False
        w = _flat(Button(text=text, size_hint=(None, None),
                         size=(112 * s, 44 * s),
                         font_size=max(10, 13 * s)), bg, fg)
        w.pos = (self._pad_x + x * bw - 56 * s, self._pad_y + y * ch - 22 * s)
        if bold:
            w.bold = True
        w.pid = pid
        w.bind(on_release=lambda btn: self.show_info(btn.pid))
        self.content.add_widget(w)
        self.node_widgets[pid] = w

    def _draw(self, token):
        if token != getattr(self, "_draw_token", None):
            return
        self.content.canvas.before.clear()
        bw, ch = self._bw, self._ch
        pad_x, pad_y = self._pad_x, self._pad_y
        def px(x):
            return pad_x + x * bw
        def py(y):
            return pad_y + y * ch
        with self.content.canvas.before:
            Color(*C_LINE)
            for i, lv in enumerate(self._levels):
                y = self._yof(i)
                cy = py(y)
                if i > 0:
                    Line(points=[px(self._col_x("spine")), py(self._yof(i - 1)),
                                 px(self._col_x("spine")), cy], width=2)
                if lv["spouse"] is not None:
                    Line(points=[px(self._col_x("spine")), cy,
                                 px(self._col_x("spouse")), cy], width=1.5)
                    spp = lv["spouse_parents"]
                    for k, pp in enumerate(spp):
                        pyy = y + (0.05 if k == 0 else -0.05) if len(spp) == 2 else y
                        Line(points=[px(self._col_x("spouse")), cy,
                                     px(self._col_x("spp")), py(pyy)], width=1.5)
                kids = lv["kids"]
                for k, c in enumerate(kids):
                    Line(points=[px(self._col_x("spine")), cy,
                                 px(self._col_x("kid", k)), cy], width=1.5)

    def show_info(self, pid):
        p = self.meta.get(pid)
        if not p:
            return
        lines = ["主记录ID: %s" % pid,
                 "姓名: %s" % p[1], "性别: %s" % p[2],
                 "八字: %s" % (p[3] or "未记录"), " "]
        sp = sorted(set(x for x in self.adj.get(pid, [])
                        if (pid, x) in self.spouse or (x, pid) in self.spouse))
        if sp:
            lines.append("配偶: " + "、".join(self.meta[s][1] for s in sp))
        ps = self.parents.get(pid, [])
        if ps:
            lines.append("父母: " + "、".join(
                (self.meta[x][1] + ("父" if self.meta[x][2] == "男" else "母"))
                for x in ps))
        cs = self.children_map.get(pid, [])
        if cs:
            cs_sorted = sorted(set(cs))
            lines.append("子女: " + "、".join(
                self.child_lab(pid, c) + self.meta[c][1] for c in cs_sorted))
        box = BoxLayout(orientation="vertical", spacing=GAP, padding=(GAP, GAP))
        _bg(box, C_PANEL)
        box.add_widget(_scrollable_text("\n".join(lines)))
        b = _btn(Button(text="关闭", size_hint_y=None, height=44))
        pop = _style_popup(Popup(title=p[1], content=box, size_hint=(0.8, 0.55)))
        b.bind(on_release=lambda x: pop.dismiss())
        box.add_widget(b)
        pop.open()

    def child_lab(self, parent, child):
        return child_title(parent, child, self.children_map, self.meta)


class ChildRow(BoxLayout):
    def __init__(self, on_remove, **kw):
        super().__init__(orientation="horizontal", size_hint_y=None, height=46,
                         spacing=GAP, **kw)
        f_name, self.name_in = _frame_input(TextInput(hint_text="子女姓名"), 0.5)
        self.gender = _spn(Spinner(text="男", values=["男", "女"], size_hint_x=0.16))
        f_bazi, self.bazi = _frame_input(TextInput(hint_text="八字"), 0.6)
        del_btn = _btn(Button(text="×", size_hint_x=0.1))
        del_btn.bind(on_release=lambda x: on_remove(self))
        self.add_widget(f_name)
        self.add_widget(self.gender)
        self.add_widget(f_bazi)
        self.add_widget(del_btn)


class EntryTab(BoxLayout):
    def __init__(self, **kw):
        super().__init__(orientation="vertical", spacing=GAP,
                         padding=(GAP, GAP), **kw)
        _bg(self, C_PANEL)

        self.add_widget(L(text="—— 本人 ——", size_hint_y=None, height=26))
        row1 = BoxLayout(size_hint_y=None, height=46, spacing=GAP)
        row1.add_widget(L(text="姓名", size_hint_x=0.18))
        f_name, self.name_in = _frame_input(TextInput(hint_text="必填"), 0.56)
        self.gender = _spn(Spinner(text="男", values=["男", "女"], size_hint_x=0.12))
        row1.add_widget(f_name)
        row1.add_widget(self.gender)
        self.add_widget(row1)
        row2 = BoxLayout(size_hint_y=None, height=46, spacing=GAP)
        row2.add_widget(L(text="八字", size_hint_x=0.18))
        f_bazi, self.bazi = _frame_input(
            TextInput(hint_text="如: 庚午 戊子 甲寅 丙寅"), 0.68)
        row2.add_widget(f_bazi)
        self.add_widget(row2)

        self.add_widget(L(text="—— 配偶 (可留空) ——", size_hint_y=None, height=26))
        srow = BoxLayout(size_hint_y=None, height=46, spacing=GAP)
        srow.add_widget(L(text="姓名", size_hint_x=0.18))
        f_sname, self.spouse_name = _frame_input(
            TextInput(hint_text="配偶姓名"), 0.56)
        self.spouse_gender = _spn(Spinner(text="女", values=["男", "女"], size_hint_x=0.12))
        srow.add_widget(f_sname)
        srow.add_widget(self.spouse_gender)
        self.add_widget(srow)
        srow2 = BoxLayout(size_hint_y=None, height=46, spacing=GAP)
        srow2.add_widget(L(text="八字", size_hint_x=0.18))
        f_sbazi, self.spouse_bazi = _frame_input(
            TextInput(hint_text="配偶八字"), 0.68)
        srow2.add_widget(f_sbazi)
        self.add_widget(srow2)

        self.add_widget(L(text="—— 子女 (按长幼顺序依次添加) ——", size_hint_y=None, height=26))
        add_btn = _btn(Button(text="＋ 添加子女", size_hint_y=None, height=42))
        add_btn.bind(on_release=lambda x: self.add_child())
        self.add_widget(add_btn)
        self.rows = BoxLayout(orientation="vertical", size_hint_y=None, spacing=GAP)
        self.rows.bind(minimum_height=self.rows.setter("height"))
        scroll = ScrollView(size_hint=(1, 1))
        scroll.add_widget(self.rows)
        self.add_widget(scroll)

        save_btn = _btn(Button(text="保存到数据库", size_hint_y=None, height=52))
        save_btn.bind(on_release=lambda x: self.do_save())
        self.add_widget(save_btn)

    def add_child(self):
        def remove(row):
            self.rows.remove_widget(row)
        self.rows.add_widget(ChildRow(on_remove=remove))

    def do_save(self):
        name = self.name_in.text.strip()
        if not name:
            self.msg("请先填写本人姓名")
            return
        items = [(name, self.gender.text, self.bazi.text.strip())]
        self.spouse_idx = None
        if self.spouse_name.text.strip():
            self.spouse_idx = len(items)
            items.append((self.spouse_name.text.strip(),
                          self.spouse_gender.text, self.spouse_bazi.text.strip()))
        self.child_idxs = []
        for row in reversed(self.rows.children):
            n = row.name_in.text.strip()
            if n:
                self.child_idxs.append(len(items))
                items.append((n, row.gender.text, row.bazi.text.strip()))

        self.pending = [(None, *it) for it in items]
        self.cur_idx = -1
        self.result = {}
        self._resolve_next()

    def _resolve_next(self):
        if not self.pending:
            self._commit()
            return
        self.cur_idx += 1
        _t, name, gender, bazi = self.pending.pop(0)
        self.dup_name, self.dup_gender, self.dup_bazi = name, gender, bazi
        rows = find_by_name(name)
        if rows:
            self._ask_duplicate(rows, name)
        else:
            self.result[self.cur_idx] = insert_person(name, gender, bazi)
            self._resolve_next()

    def _ask_duplicate(self, rows, name):
        box = BoxLayout(orientation="vertical", spacing=GAP, padding=(GAP, GAP))
        _bg(box, C_PANEL)
        box.add_widget(L(text="已存在同名「%s」, 请选择:" % name, size_hint_y=None, height=34, color=C_POP_TEXT))
        for r in rows:
            b = _btn(Button(text="关联已有 #%s · %s · 八字:%s" % (r[0], r[2], r[3] or "空"),
                            size_hint_y=None, height=42))
            pid = r[0]
            b.bind(on_release=lambda x, p=pid: self._pick_exist(p))
            box.add_widget(b)
        nb = _btn(Button(text="作为新的人新增(同名不同ID)", size_hint_y=None, height=42))
        nb.bind(on_release=lambda x: self._pick_new())
        box.add_widget(nb)
        self.dup_pop = _style_popup(Popup(title="名字查重: %s" % name, content=box,
                                        size_hint=(0.9, 0.62)))
        self.dup_pop.open()

    def _pick_exist(self, pid):
        self.dup_pop.dismiss()
        self.result[self.cur_idx] = pid
        self._resolve_next()

    def _pick_new(self):
        self.dup_pop.dismiss()
        self.result[self.cur_idx] = insert_person(self.dup_name, self.dup_gender,
                                                  self.dup_bazi)
        self._resolve_next()

    def _commit(self):
        main_id = self.result.get(0)
        if main_id is None:
            self.msg("保存失败: 本人未创建")
            return
        if self.spouse_idx is not None and self.spouse_idx in self.result:
            insert_relation(main_id, self.result[self.spouse_idx], "spouse_of")
            sp_id = self.result[self.spouse_idx]
        else:
            sp_id = None
        for ci in self.child_idxs:
            cid = self.result.get(ci)
            if cid is None:
                continue
            insert_relation(main_id, cid, "parent_of")
            if sp_id is not None:
                insert_relation(sp_id, cid, "parent_of")
        self.name_in.text = ""
        self.bazi.text = ""
        self.spouse_name.text = ""
        self.spouse_bazi.text = ""
        self.rows.clear_widgets()
        self.msg("保存成功! 主记录 ID=%s" % main_id)

    def msg(self, text):
        msg_popup(text, title="提示")


# ============================================================
# 查询页
# ============================================================
class QueryTab(BoxLayout):
    def __init__(self, **kw):
        super().__init__(orientation="vertical", spacing=GAP, padding=(GAP, GAP), **kw)
        _bg(self, C_PANEL)
        f_search, self.search = _frame_input(
            TextInput(hint_text="输入人名搜索"), 0.8)
        search_btn = _btn(Button(text="搜索", size_hint_x=0.2))
        search_btn.bind(on_release=lambda x: self.on_search())
        srow = BoxLayout(size_hint_y=None, height=46, spacing=GAP)
        srow.add_widget(f_search)
        srow.add_widget(search_btn)

        self.graph = GraphView(None)
        self.add_widget(self.graph)

        self.add_widget(srow)

    def on_search(self):
        name = self.search.text.strip()
        if not name:
            return
        rows = find_by_name(name)
        if not rows:
            if self.graph.info is not None:
                self.graph.info.text = "未找到: %s (请先到「录入数据」添加)" % name
            return
        if len(rows) == 1:
            self.graph.set_center(rows[0][0])
            return
        box = BoxLayout(orientation="vertical", spacing=GAP, padding=(GAP, GAP))
        _bg(box, C_PANEL)
        box.add_widget(L(text="找到 %d 个同名, 请选择:" % len(rows),
                             size_hint_y=None, height=34, color=C_POP_TEXT))
        for r in rows:
            b = _btn(Button(text="#%s · %s · %s · 八字:%s" % (r[0], r[1], r[2], r[3] or "空"),
                            size_hint_y=None, height=42))
            pid = r[0]
            b.bind(on_release=lambda x, p=pid: self._choose(p))
            box.add_widget(b)
        self.dup_pop = _style_popup(Popup(title="同名选择: %s" % name, content=box,
                                        size_hint=(0.9, 0.7)))
        self.dup_pop.open()

    def _choose(self, pid):
        self.dup_pop.dismiss()
        self.graph.set_center(pid)


# ============================================================
# 编辑页 (修正录入错误 + 删除)
# ============================================================
class EditTab(BoxLayout):
    def __init__(self, **kw):
        super().__init__(orientation="vertical", spacing=GAP,
                         padding=(GAP, GAP), **kw)
        _bg(self, C_PANEL)
        self.cur_id = None

        self.add_widget(L(text="—— 按主记录 ID 定位 (修正录入错误) ——",
                          size_hint_y=None, height=26))
        row_id = BoxLayout(size_hint_y=None, height=46, spacing=GAP)
        row_id.add_widget(L(text="主记录ID", size_hint_x=0.22))
        f_id, self.id_in = _frame_input(TextInput(hint_text="输入主记录 ID, 如: 1"), 0.5)
        find_btn = _btn(Button(text="查找", size_hint_x=0.2))
        find_btn.bind(on_release=lambda x: self.on_find())
        row_id.add_widget(f_id)
        row_id.add_widget(find_btn)
        self.add_widget(row_id)

        self.status = L(text="输入主记录 ID 后点「查找」", size_hint_y=None,
                        height=26, color=C_POP_TEXT)
        self.add_widget(self.status)

        self.add_widget(L(text="—— 可编辑字段 ——", size_hint_y=None, height=26))
        row_name = BoxLayout(size_hint_y=None, height=46, spacing=GAP)
        row_name.add_widget(L(text="姓名", size_hint_x=0.22))
        f_name, self.name_in = _frame_input(TextInput(hint_text="修正后的姓名"), 0.48)
        self.gender_lab = L(text="性别", size_hint_x=0.2)
        row_name.add_widget(f_name)
        row_name.add_widget(self.gender_lab)
        self.add_widget(row_name)

        row_bazi = BoxLayout(size_hint_y=None, height=46, spacing=GAP)
        row_bazi.add_widget(L(text="八字", size_hint_x=0.22))
        f_bazi, self.bazi_in = _frame_input(
            TextInput(hint_text="如: 庚午 戊子 甲寅 丙寅"), 0.68)
        row_bazi.add_widget(f_bazi)
        self.add_widget(row_bazi)

        self.add_widget(L(text="—— 人际关系 (配偶/父母/子女) ——", size_hint_y=None, height=26))
        self.rel_lab = L(text="不可编辑, 查找后此处自动显示(仅作确认)", size_hint_y=None,
                         height=26, color=C_POP_TEXT)
        self.add_widget(self.rel_lab)

        save_btn = _btn(Button(text="保存修改", size_hint_y=None, height=52))
        save_btn.bind(on_release=lambda x: self.on_save())
        self.add_widget(save_btn)

        self.del_btn = _btn_danger(Button(text="删除此人", size_hint_y=None, height=52))
        self.del_btn.bind(on_release=lambda x: self.confirm_delete())
        self.add_widget(self.del_btn)

        self.name_in.disabled = True
        self.bazi_in.disabled = True
        self.del_btn.disabled = True

    def on_find(self):
        raw = self.id_in.text.strip()
        try:
            pid = int(raw)
        except (ValueError, TypeError):
            self.status.text = "主记录 ID 必须是数字, 如: 1"
            self._reset_editing()
            return
        r = get_person(pid)
        if not r:
            self.status.text = "未找到主记录 ID=%s (请先到「录入数据」添加)" % pid
            self._reset_editing()
            return
        self.cur_id = pid
        self.name_in.text = r[1]
        self.bazi_in.text = r[3] or ""
        self.gender_lab.text = "性别: %s" % r[2]
        self.name_in.disabled = False
        self.bazi_in.disabled = False
        self.del_btn.disabled = False
        meta, adj, edges, spouse, children, parents = load_all()
        lines = []
        sp = sorted(set(x for x in adj.get(pid, [])
                        if (pid, x) in spouse or (x, pid) in spouse))
        if sp:
            lines.append("配偶: " + "、".join(meta[s][1] for s in sp))
        ps = parents.get(pid, [])
        if ps:
            lines.append("父母: " + "、".join(
                meta[x][1] + ("父" if meta[x][2] == "男" else "母") for x in ps))
        cs = sorted(set(children.get(pid, [])))
        if cs:
            lines.append("子女: " + "、".join(
                child_title(pid, c, children, meta) + meta[c][1] for c in cs))
        if not lines:
            lines.append("(无配偶/父母/子女记录)")
        self.rel_lab.text = "  ·  ".join(lines)
        self.status.text = "已定位: #%s · %s · 性别:%s · 八字:%s" % (
            r[0], r[1], r[2], r[3] or "空")

    def _reset_editing(self):
        self.cur_id = None
        self.name_in.text = ""
        self.bazi_in.text = ""
        self.name_in.disabled = True
        self.bazi_in.disabled = True
        self.del_btn.disabled = True
        self.gender_lab.text = "性别"
        self.rel_lab.text = "不可编辑, 查找后此处自动显示(仅作确认)"

    def on_save(self):
        if self.cur_id is None:
            self.msg("请先输入主记录 ID 并点击「查找」")
            return
        name = self.name_in.text.strip()
        if not name:
            self.msg("姓名不能为空")
            return
        bazi = self.bazi_in.text.strip()
        dups = [r for r in find_by_name(name) if r[0] != self.cur_id]
        warn = ""
        if dups:
            warn = ("\n注意: 已存在同名记录 #%s, 查询时会出现同名选择, 请确认姓名无误。"
                    % "、".join(str(d[0]) for d in dups))
        update_person(self.cur_id, name, bazi)
        self.status.text = "已保存: #%s · %s · 八字:%s" % (self.cur_id, name, bazi or "空")
        self.msg("保存成功!\n主记录 ID = %s\n姓名 = %s\n八字 = %s\n\n"
                 "人际关系(配偶/父母/子女)保持不变。%s" % (self.cur_id, name, bazi or "空", warn))

    def confirm_delete(self):
        if self.cur_id is None:
            return
        p = get_person(self.cur_id)
        name = p[1] if p else "?"
        box = BoxLayout(orientation="vertical", spacing=GAP, padding=(GAP, GAP))
        _bg(box, C_PANEL)
        box.add_widget(_scrollable_text(
            "确定要删除这条记录吗?\n\n主记录 ID = %s\n姓名 = %s\n\n"
            "将同时删除该人的所有关系 (配偶/父母/子女)。\n此操作不可恢复!" % (self.cur_id, name)))
        row = BoxLayout(size_hint_y=None, height=48, spacing=GAP)
        ok = _btn_danger(Button(text="确认删除", size_hint_x=0.5))
        no = _btn(Button(text="取消", size_hint_x=0.5))
        pop = _style_popup(Popup(title="确认删除", content=box, size_hint=(0.85, 0.5)))
        ok.bind(on_release=lambda x: self._do_delete(pop))
        no.bind(on_release=lambda x: pop.dismiss())
        row.add_widget(ok)
        row.add_widget(no)
        box.add_widget(row)
        pop.open()

    def _do_delete(self, pop):
        pid = self.cur_id
        delete_person(pid)
        pop.dismiss()
        self._reset_editing()
        self.msg("已删除主记录 ID=%s (其所有关系已一并删除)" % pid)

    def msg(self, text):
        msg_popup(text, title="提示")


# ============================================================
# 登录页 (每次打开必须先登录才能进入并读取数据)
# ============================================================
class LoginScreen(BoxLayout):
    def __init__(self, **kw):
        super().__init__(orientation="vertical", spacing=GAP * 2,
                         padding=(GAP * 3, GAP * 4), **kw)
        _bg(self, C_PANEL)
        self.add_widget(L(text="家谱关系网络", font_size=26, size_hint_y=None, height=64))
        self.add_widget(L(text="请输入账号ID和密码登录", size_hint_y=None, height=30,
                          color=C_POP_TEXT))
        self.add_widget(L(text="", size_hint_y=None, height=6))

        row1 = BoxLayout(size_hint_y=None, height=50, spacing=GAP)
        row1.add_widget(L(text="账号ID", size_hint_x=0.3))
        f_id, self.id_in = _frame_input(TextInput(hint_text="账号ID"), 0.7)
        row1.add_widget(f_id)
        self.add_widget(row1)

        row2 = BoxLayout(size_hint_y=None, height=50, spacing=GAP)
        row2.add_widget(L(text="密码", size_hint_x=0.3))
        f_pw, self.pw_in = _frame_input(TextInput(hint_text="密码", password=True), 0.7)
        row2.add_widget(f_pw)
        self.add_widget(row2)

        self.msg_lab = L(text="", size_hint_y=None, height=30, color=(0.72, 0.2, 0.2, 1))
        self.add_widget(self.msg_lab)

        login = _btn(Button(text="登 录", size_hint_y=None, height=52))
        login.bind(on_release=lambda x: self.do_login())
        self.add_widget(login)

        reg = _btn(Button(text="注册新账号", size_hint_y=None, height=52))
        reg.bind(on_release=lambda x: self.do_register())
        self.add_widget(reg)

        self.add_widget(L(text="提示: 请牢记账号ID与密码。密码忘记无法找回, "
                              "只能注册新账号并重新录入数据, 无法读取旧账号信息。",
                          font_size=13, size_hint_y=None, height=70, color=(0.5, 0.5, 0.5, 1)))
        self.pw_in.bind(on_text_validate=lambda *a: self.do_login())

    def do_login(self):
        raw = self.id_in.text.strip()
        pw = self.pw_in.text
        if not raw or not pw:
            self.msg_lab.text = "请输入账号ID和密码"
            return
        try:
            aid = int(raw)
        except (ValueError, TypeError):
            self.msg_lab.text = "账号ID必须为数字"
            return
        ok, _aid, key, msg = check_login(aid, pw)
        if ok:
            begin_session(_aid, key)
            App.get_running_app().enter_main()
        else:
            self.msg_lab.text = msg

    def do_register(self):
        box = BoxLayout(orientation="vertical", spacing=GAP, padding=(GAP, GAP))
        _bg(box, C_PANEL)
        box.add_widget(L(text="设置登录密码 (至少 4 位):", size_hint_y=None, height=28,
                         color=C_POP_TEXT))
        f1, self.reg_pw = _frame_input(TextInput(hint_text="密码", password=True, multiline=False), 1.0)
        box.add_widget(f1)
        box.add_widget(L(text="再次输入确认:", size_hint_y=None, height=28, color=C_POP_TEXT))
        f2, self.reg_pw2 = _frame_input(TextInput(hint_text="再次输入密码", password=True, multiline=False), 1.0)
        box.add_widget(f2)
        box.add_widget(L(text="账号ID将由程序自动生成, 注册成功后请务必牢记!", size_hint_y=None,
                         height=34, color=(0.5, 0.5, 0.5, 1)))
        err = L(text="", size_hint_y=None, height=26, color=(0.72, 0.2, 0.2, 1))
        box.add_widget(err)
        row = BoxLayout(size_hint_y=None, height=48, spacing=GAP)
        ok = _btn(Button(text="确认注册", size_hint_x=0.5))
        no = _btn(Button(text="取消", size_hint_x=0.5))
        pop = _style_popup(Popup(title="注册新账号", content=box, size_hint=(0.85, 0.62)))
        ok.bind(on_release=lambda x: self._register_submit(pop, err))
        no.bind(on_release=lambda x: pop.dismiss())
        row.add_widget(ok)
        row.add_widget(no)
        box.add_widget(row)
        pop.open()

    def _register_submit(self, pop, err):
        pw = self.reg_pw.text
        pw2 = self.reg_pw2.text
        if len(pw) < 4:
            err.text = "密码至少 4 位"
            return
        if pw != pw2:
            err.text = "两次输入的密码不一致"
            return
        try:
            aid, _ = register_account(pw)
        except ValueError as e:
            err.text = str(e)
            return
        ok, _aid, key, _ = check_login(aid, pw)
        begin_session(_aid, key)
        pop.dismiss()
        box = BoxLayout(orientation="vertical", spacing=GAP, padding=(GAP, GAP))
        _bg(box, C_PANEL)
        box.add_widget(_scrollable_text(
            "注册成功!\n\n你的账号ID:  %s\n\n请务必牢记账号ID和密码!\n"
            "(密码忘记无法找回, 只能重新注册, 新账号需重新录入数据)" % aid))
        b = _btn(Button(text="进入家谱", size_hint_y=None, height=48))
        pop2 = _style_popup(Popup(title="注册成功", content=box, size_hint=(0.85, 0.55)))
        b.bind(on_release=lambda x: (pop2.dismiss(), App.get_running_app().enter_main()))
        box.add_widget(b)
        pop2.open()


# ============================================================
# 应用入口
# ============================================================
def build_main_tabs():
    tp = TabbedPanel(do_default_tab=False, tab_height=44)
    _set_bg(tp, C_PANEL)
    try:
        _set_bg(tp._tab_strip, C_PANEL)
    except Exception:
        pass
    item1 = _style_tab(TabbedPanelItem(text="查询网络", content=QueryTab()))
    item2 = _style_tab(TabbedPanelItem(text="录入数据", content=EntryTab()))
    item3 = _style_tab(TabbedPanelItem(text="编辑", content=EditTab()))
    tp.add_widget(item1)
    tp.add_widget(item2)
    tp.add_widget(item3)
    Clock.schedule_once(lambda dt: tp.switch_to(item1), 0.05)
    return tp


class FamilyApp(App):
    def build(self):
        init_db()
        Window.clearcolor = C_BG
        Window.size = (420, 760)
        self.container = BoxLayout()
        self.login = LoginScreen()
        self.container.add_widget(self.login)
        return self.container

    def enter_main(self):
        self.container.clear_widgets()
        self.container.add_widget(build_main_tabs())


if __name__ == "__main__":
    setup_chinese_font()   # 必须在 App 启动前调用, 否则中文乱码
    FamilyApp().run()

# ============================================================
# 打包到安卓 (buildozer) —— 本项目已配好, 见同目录:
#   buildozer.spec   (权限留空=无 INTERNET; 中文字体 ttc/ttf 已包含;
#                     release 产物已设为 apk; release 签名字段)
#   build_android.sh (一键: 生成密钥库 -> 导出签名环境变量 -> release 打包 -> 校验)
# 手动命令(在 Linux 或 WSL 中, 本目录下):
#   1. pip install buildozer cython
#   2. 把 simsun.ttc 复制到本 .py 同目录(程序优先加载同目录字体)
#   3. 首次生成 release 签名密钥库(记住密码):
#        keytool -genkey -v -keystore release.keystore \
#               -alias familygraph -keyalg RSA -keysize 2048 -validity 10000
#   4. 导出签名环境变量(四个缺一不可, 否则产物是 release-unsigned 装不上):
#        export P4A_RELEASE_KEYSTORE="$PWD/release.keystore"
#        export P4A_RELEASE_KEYALIAS=familygraph
#        export P4A_RELEASE_KEYSTORE_PASSWD='你的密码'
#        export P4A_RELEASE_KEYALIAS_PASSWD='你的密码'
#   5. buildozer android release   -> 已签名 APK 在 bin/
# 校验: aapt dump permissions bin/*.apk  应无 android.permission.INTERNET
# ============================================================
