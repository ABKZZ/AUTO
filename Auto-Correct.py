#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Auto-Correct v3  (tick đáp án + cào bổ sung đề)

Thư viện gồm 2 lớp, đều nằm cạnh script/EXE:
  _cache_thuvien.json   bản tải về từ GitHub (tool cào lớn tạo ra)
  bo_sung.json          các câu cào thủ công bằng tool này (câu mới / câu đổi đáp án)
  _thuvien_meta.json    hash + ngày đăng của bản GitHub

Quy tắc "mới nhất thắng":
  - Mỗi lần mở tool: tải GitHub, lấy ngày commit của file thư viện.
  - Câu trong bo_sung có thời gian cào > ngày đăng thư viện  -> dùng bản bo_sung.
  - Câu trong bo_sung cũ hơn ngày đăng (tool lớn đã cập nhật) -> bỏ, dùng thư viện (và dọn khỏi bo_sung).
  - Đề đã cào thủ công chưa quá 24h (và mới hơn thư viện) -> không cào lại, dùng luôn.
Tool này KHÔNG đẩy gì lên GitHub.
"""

import hashlib
import json
import os
import random
import re
import subprocess
import sys
import threading
import time
import unicodedata
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path
import tkinter as tk
from tkinter import messagebox, scrolledtext, ttk

import requests
from selenium import webdriver
from selenium.common.exceptions import NoAlertPresentException, TimeoutException
from selenium.webdriver.common.by import By
from selenium.webdriver.edge.options import Options as EdgeOptions
from selenium.webdriver.edge.service import Service as EdgeService
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait

# ==================== CẤU HÌNH ====================
if getattr(sys, "frozen", False):
    BASE_DIR = Path(sys.executable).parent
else:
    BASE_DIR = Path(__file__).parent

CACHE_JSON = BASE_DIR / "_cache_thuvien.json"
META_JSON = BASE_DIR / "_thuvien_meta.json"
BO_SUNG_JSON = BASE_DIR / "bo_sung.json"

GITHUB_URLS = (
    "https://raw.githubusercontent.com/ABKZZ/TracNghiem-CDDS/main/tat_ca_bai_thi.json",
    "https://raw.githubusercontent.com/ABKZZ/TracNghiem-CDDS/refs/heads/main/tat_ca_bai_thi.json",
)
GITHUB_COMMITS_API = (
    "https://api.github.com/repos/ABKZZ/TracNghiem-CDDS/commits?path=tat_ca_bai_thi.json&per_page=1"
)
BASE_URL = "https://tracnghiem.caodangduongsat.edu.vn"
LIST_URL = f"{BASE_URL}/thi-thu.html"
MARK_SELECTOR = "img.tabpimpa, img[src*='pimpa_yes']"

# khớp khi tick
Q_MATCH_MIN = 0.70
OPT_MATCH_MIN = 0.75
MIN_Q_LEN = 8

# cào bổ sung
MAX_PARALLEL = 3            # số trình duyệt cào chạy cùng lúc
COVERAGE_TARGET = 0.98      # độ phủ ước lượng để dừng
ZERO_NEW_STOP = 4           # hoặc N lần liên tiếp không ra câu mới
MAX_ATTEMPTS = 30           # trần số lượt / đề
MAX_CONSEC_ERRORS = 4
PAGE_TIMEOUT = 20
DELAY_MIN, DELAY_MAX = 0.3, 0.9
WATCHDOG_SECONDS = 120      # 1 bước đứng im quá lâu -> đóng cưỡng bức trình duyệt đó
FRESH_SECONDS = 24 * 3600   # đề cào thủ công chưa quá 1 ngày thì dùng luôn
FRESH_MIN_COV = 0.9


# ==================== XỬ LÝ CHUỖI (đồng bộ với tool cào) ====================
_ZW = dict.fromkeys(map(ord, "\u200b\u200c\u200d\ufeff"), None)
_PUNCT_MAP = str.maketrans({"“": '"', "”": '"', "‘": "'", "’": "'", "–": "-", "—": "-"})
_PREFIX_RE = re.compile(r"^\s*câu\s*\d+\s*[:.\-–—)]?\s*", re.IGNORECASE)
_ANS_PREFIXES = ("✓", "✔", "Đáp án đúng:", "Đáp án:")
_TOKEN_RE = re.compile(r"[^\W_]+|[<>=+*/%^]")
OPS = set("<>=+*/%^")


def clean_question(text) -> str:
    """Bỏ 'Câu 12:' ở đầu, chuẩn hóa Unicode và khoảng trắng. GIỮ ký hiệu (< > = số...)."""
    if not text:
        return ""
    text = unicodedata.normalize("NFC", str(text)).translate(_ZW)
    text = " ".join(text.split())
    for _ in range(3):
        new = _PREFIX_RE.sub("", text)
        if new == text:
            break
        text = new
    return text.strip()


def clean_answer(text) -> str:
    text = unicodedata.normalize("NFC", str(text or "")).translate(_ZW)
    text = " ".join(text.split())
    changed = True
    while changed:
        changed = False
        for p in _ANS_PREFIXES:
            if text.startswith(p):
                text = text[len(p):].strip()
                changed = True
    return text


def q_key(text) -> str:
    return clean_question(text).translate(_PUNCT_MAP).casefold()


def a_key(text) -> str:
    return clean_answer(text).translate(_PUNCT_MAP).casefold()


def dedupe_answers(answers) -> list:
    if isinstance(answers, str):
        answers = [answers]
    out, seen = [], set()
    for a in answers or []:
        a = clean_answer(a)
        k = a_key(a)
        if a and k not in seen:
            seen.add(k)
            out.append(a)
    return out


def same_answers(a, b) -> bool:
    return {a_key(x) for x in a} == {a_key(x) for x in b}


def strip_option_letter(text: str) -> str:
    return re.sub(r"^\s*[A-Da-d][\.\)\:]\s+", "", text or "").strip()


def tokenize(text: str) -> list:
    return _TOKEN_RE.findall(unicodedata.normalize("NFC", text or "").lower())


def special_tokens(toks) -> set:
    return {t for t in toks if t in OPS or t[0].isdigit()}


def token_similarity(ta, tb) -> float:
    if not ta or not tb:
        return 0.0
    return len(ta & tb) / max(len(ta), len(tb))


def write_json_atomic(path: Path, obj):
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False)
    os.replace(tmp, path)


def fmt_dt(ts: float) -> str:
    try:
        return datetime.fromtimestamp(ts).strftime("%H:%M %d/%m/%Y")
    except Exception:
        return "?"


def fmt_ago(sec: float) -> str:
    if sec < 90:
        return "vừa xong"
    if sec < 3600:
        return f"{int(sec // 60)} phút trước"
    return f"{sec / 3600:.1f} giờ trước"


# ==================== ƯỚC LƯỢNG ĐỘ PHỦ (Chao, như tool cào) ====================
def chao_incidence(scrapes: list) -> tuple:
    T = len(scrapes)
    freq = Counter()
    for s in scrapes:
        freq.update(s)
    S = len(freq)
    if S == 0 or T < 2:
        return T, S, 0, 0, None, 0.0
    Q1 = sum(1 for v in freq.values() if v == 1)
    Q2 = sum(1 for v in freq.values() if v == 2)
    U = sum(freq.values())
    if Q1 == 0:
        cov = 1.0
    else:
        if Q2 > 0:
            a = (T - 1) * Q1 / ((T - 1) * Q1 + 2 * Q2)
        else:
            a = (T - 1) * (Q1 - 1) / ((T - 1) * (Q1 - 1) + 2)
        cov = max(0.0, 1.0 - (Q1 / U) * a)
    if Q2 > 0:
        s_est = S + ((T - 1) / T) * Q1 * Q1 / (2.0 * Q2)
    else:
        s_est = S + ((T - 1) / T) * Q1 * (Q1 - 1) / 2.0
    return T, S, Q1, Q2, s_est, cov


# ==================== THƯ VIỆN ====================
class Library:
    def __init__(self):
        self.items = {}       # q_key -> {"q": str, "a": [str], "c": bool(nghi ngờ)}
        self.entries = []     # [(key, tokens, special)]
        self.index = defaultdict(list)
        self.source = "none"  # github | cache | none
        self.date = 0.0       # ngày đăng file thư viện (epoch)
        self.date_ok = False  # ngày lấy được từ GitHub (đáng tin)
        self.loaded_at = 0.0
        self.bo_applied = 0

    @property
    def count(self):
        return len(self.items)

    def build_from_data(self, data) -> int:
        votes = defaultdict(dict)   # key -> {vk: [n, q, answers]}
        flagged = set()
        if not isinstance(data, list):
            return 0
        for exam in data:
            for it in exam.get("danh_sach_cau_hoi", []) or []:
                text = it.get("cau_hoi", "")
                key = q_key(text)
                ans = it.get("cac_dap_an_dung")
                if not ans:
                    raw = str(it.get("dap_an_dung", "") or "")
                    ans = raw.split(" | ") if " | " in raw else [raw]
                ans = dedupe_answers(ans)
                if not key or not ans:
                    continue
                vk = tuple(sorted(a_key(a) for a in ans))
                slot = votes[key].setdefault(vk, [0, clean_question(text), ans])
                slot[0] += 1
                if it.get("can_xac_minh"):
                    flagged.add(key)
        items = {}
        for key, sets in votes.items():
            n, q, ans = max(sets.values(), key=lambda s: (s[0], len(" ".join(s[2]))))
            items[key] = {"q": q, "a": ans, "c": key in flagged}
        self.items = items
        self.reindex()
        return len(items)

    def reindex(self):
        entries, index = [], defaultdict(list)
        for key in self.items:
            toks = frozenset(tokenize(key))
            idx = len(entries)
            entries.append((key, toks, special_tokens(toks)))
            for t in toks:
                index[t].append(idx)
        self.entries, self.index = entries, index

    def find(self, question_text: str):
        """Trả về (item, điểm). item=None nếu không đủ chắc."""
        q = clean_question(question_text)
        key = q_key(q)
        if len(key) < MIN_Q_LEN:
            return None, 0.0
        it = self.items.get(key)
        if it:
            return it, 1.0
        qt = frozenset(tokenize(q))
        if not qt:
            return None, 0.0
        qs = special_tokens(qt)
        limit = max(200, len(self.entries) // 4)
        cand = Counter()
        for t in qt:
            post = self.index.get(t)
            if post and len(post) <= limit:
                cand.update(post)
        best_score, best_key = 0.0, None
        for idx, _ in cand.most_common(40):
            k, kt, ks = self.entries[idx]
            score = token_similarity(qt, kt)
            if len(key) > 15 and len(k) > 15 and (key in k or k in key):
                if min(len(key), len(k)) / max(len(key), len(k)) >= 0.6:
                    score = max(score, 0.90)
            if qs != ks:          # khác số / ký hiệu (vd 3+5 và 3+6) -> không tin
                score *= 0.5
            if score > best_score:
                best_score, best_key = score, k
        if best_score >= Q_MATCH_MIN and best_key is not None:
            return self.items[best_key], best_score
        return None, best_score


LIB = Library()
BO = {"questions": {}, "exams": {}}
BO_LOCK = threading.RLock()


def load_bo():
    global BO
    try:
        d = json.loads(BO_SUNG_JSON.read_text(encoding="utf-8"))
        BO = {"questions": d.get("questions", {}), "exams": d.get("exams", {})}
    except Exception:
        BO = {"questions": {}, "exams": {}}


def save_bo():
    try:
        write_json_atomic(BO_SUNG_JSON, BO)
    except Exception as e:
        log(f"Lỗi lưu bo_sung.json: {e}")


def fetch_commit_date():
    try:
        r = requests.get(
            GITHUB_COMMITS_API, timeout=15,
            headers={"User-Agent": "auto-correct", "Accept": "application/vnd.github+json"},
        )
        if r.status_code == 200:
            arr = r.json()
            if arr:
                s = arr[0]["commit"]["committer"]["date"]
                return datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp()
    except Exception:
        pass
    return None


def read_meta() -> dict:
    try:
        return json.loads(META_JSON.read_text(encoding="utf-8"))
    except Exception:
        return {}


def load_library_full():
    """Tải GitHub (hoặc dùng bản đã tải), xác định ngày đăng, chồng bo_sung lên. Trả về Library hoặc None."""
    raw, data, source = None, None, "none"
    for url in GITHUB_URLS:
        try:
            r = requests.get(url, timeout=30, headers={"Cache-Control": "no-cache"})
            if r.status_code == 200:
                data = json.loads(r.content.decode("utf-8-sig"))
                raw = r.content
                source = "github"
                break
        except Exception:
            continue

    meta = read_meta()
    lib_date, date_ok = float(meta.get("date", 0.0) or 0.0), bool(meta.get("date_ok"))

    if raw is not None:
        h = hashlib.sha1(raw).hexdigest()
        try:
            tmp = CACHE_JSON.with_suffix(".tmp")
            tmp.write_bytes(raw)
            tmp.replace(CACHE_JSON)
        except Exception:
            pass
        if not (meta.get("hash") == h and meta.get("date_ok")):
            d = fetch_commit_date()
            if d:
                lib_date, date_ok = d, True
            else:
                lib_date, date_ok = time.time(), False  # không rõ ngày -> coi là mới, không dọn bo_sung
                log("⚠ Không đọc được ngày đăng của thư viện từ GitHub; tạm coi là mới nhất.")
            try:
                write_json_atomic(META_JSON, {"hash": h, "date": lib_date, "date_ok": date_ok})
            except Exception:
                pass
    elif CACHE_JSON.exists():
        try:
            data = json.loads(CACHE_JSON.read_text(encoding="utf-8-sig"))
            source = "cache"
        except Exception:
            data = None

    lib = Library()
    if data is None or lib.build_from_data(data) == 0:
        return None
    lib.source, lib.date, lib.date_ok, lib.loaded_at = source, lib_date, date_ok, time.time()

    # chồng bo_sung lên
    with BO_LOCK:
        load_bo()
        drop = []
        for key, rec in BO["questions"].items():
            ans = dedupe_answers(rec.get("a"))
            if not ans:
                drop.append(key)
                continue
            cur = lib.items.get(key)
            if cur is None or float(rec.get("t", 0)) > lib_date:
                lib.items[key] = {"q": rec.get("q", key), "a": ans, "c": False}
                lib.bo_applied += 1
            elif date_ok:
                drop.append(key)       # thư viện đã mới hơn -> bỏ bản cũ
        old_exams = [e for e, m in BO["exams"].items() if date_ok and float(m.get("t", 0)) <= lib_date]
        for key in drop:
            BO["questions"].pop(key, None)
        for e in old_exams:
            BO["exams"].pop(e, None)
        if drop or old_exams:
            save_bo()
    lib.reindex()
    return lib


# ==================== TRÌNH DUYỆT ====================
sessions = []  # cửa sổ tick: {"id", "name", "driver"}
_next_session_id = 1
sessions_lock = threading.Lock()
is_running = False        # đang tick
scrape_running = False    # đang trong luồng cào bổ sung
_driver_lock = threading.Lock()


def edge_and_driver_paths():
    edge_found = None
    for p in (
        r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
        r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
    ):
        if Path(p).exists():
            edge_found = p
            break
    if not edge_found:
        raise RuntimeError("Không tìm thấy msedge.exe. Hãy kiểm tra đã cài Microsoft Edge.")
    return edge_found, BASE_DIR / "msedgedriver.exe"


def start_edge(options):
    """Ưu tiên msedgedriver.exe cạnh tool; nếu thiếu hoặc lệch phiên bản Edge thì để Selenium Manager tự tải driver khớp."""
    edge, drv_path = edge_and_driver_paths()
    options.binary_location = edge
    reason = "chưa có msedgedriver.exe cạnh tool"
    if drv_path.exists():
        try:
            return webdriver.Edge(service=EdgeService(executable_path=str(drv_path)), options=options)
        except Exception as e:
            msg = str(e)
            if "session not created" not in msg.lower() and "only supports" not in msg:
                raise
            reason = "msedgedriver.exe không khớp phiên bản Edge (Edge tự cập nhật)"
    log(f"⚠ {reason} → thử tự tải driver phù hợp (cần Internet)…")
    try:
        return webdriver.Edge(options=options)  # Selenium Manager
    except Exception as e2:
        raise RuntimeError(
            f"Không khởi động được Edge: {reason}, và tự tải driver cũng thất bại.\n\n"
            "Cách sửa tay: tải Microsoft Edge WebDriver ĐÚNG số phiên bản Edge của bạn "
            "(edge://settings/help để xem) tại developer.microsoft.com/microsoft-edge/tools/webdriver, "
            f"rồi chép đè msedgedriver.exe vào:\n{BASE_DIR}\n\nChi tiết: {str(e2)[:300]}"
        )


def create_driver():
    """Cửa sổ InPrivate hiện hình, dùng để làm bài + tick."""
    options = EdgeOptions()
    options.add_argument("--inprivate")
    options.add_argument("--window-size=1400,1000")
    options.add_argument("--disable-blink-features=AutomationControlled")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_experimental_option("excludeSwitches", ["enable-automation"])
    options.add_experimental_option("useAutomationExtension", False)
    drv = start_edge(options)
    try:
        drv.execute_script("Object.defineProperty(navigator,'webdriver',{get:()=>undefined})")
    except Exception:
        pass
    return drv


def create_scraper_driver():
    """Trình duyệt ẩn riêng để cào đề (không đụng vào cửa sổ đang làm bài)."""
    options = EdgeOptions()
    options.add_argument("--headless=new")
    options.add_argument("--window-size=1280,900")
    options.add_argument("--disable-blink-features=AutomationControlled")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--disable-gpu")
    options.add_argument("--log-level=3")
    options.page_load_strategy = "eager"
    options.add_experimental_option("prefs", {"profile.managed_default_content_settings.images": 2})
    options.add_experimental_option("excludeSwitches", ["enable-automation", "enable-logging"])
    with _driver_lock:
        drv = start_edge(options)
    drv.set_page_load_timeout(PAGE_TIMEOUT * 2)
    drv.set_script_timeout(30)
    return drv


def kill_driver(drv, graceful=True):
    """Đóng trình duyệt; nếu quit() treo thì giết cả cây tiến trình."""
    if drv is None:
        return
    pid = None
    try:
        pid = drv.service.process.pid
    except Exception:
        pass

    def _quit():
        try:
            drv.quit()
        except Exception:
            pass

    th = threading.Thread(target=_quit, daemon=True)
    th.start()
    if graceful:
        th.join(8)
        if not th.is_alive():
            return
    if pid:
        try:
            if os.name == "nt":
                subprocess.run(["taskkill", "/F", "/T", "/PID", str(pid)], capture_output=True,
                               timeout=10, creationflags=0x08000000)
            else:
                os.kill(pid, 9)
        except Exception:
            pass


def driver_alive(drv) -> bool:
    try:
        _ = drv.window_handles
        return True
    except Exception:
        return False


def prune_dead_sessions():
    with sessions_lock:
        sessions[:] = [s for s in sessions if driver_alive(s["driver"])]


def is_session_dead(e: Exception) -> bool:
    s = str(e).lower()
    return any(x in s for x in ("invalid session", "disconnected", "not reachable", "no such window",
                                "target window already closed", "session deleted"))


# ==================== TICK ĐÁP ÁN ====================
JS_EXTRACT_TICK = r"""
const qsel = 'p.cauhoi, .cauhoi';
let blocks = [...document.querySelectorAll('li')].filter(li => li.querySelector(qsel));
blocks = blocks.filter(b => !blocks.some(o => o !== b && b.contains(o)));
const out = [];
blocks.forEach((b, i) => {
  const qEl = b.querySelector(qsel);
  const inputs = [...new Set(b.querySelectorAll("input.dapan, input[type='radio'], input[type='checkbox']"))];
  const opts = [];
  inputs.forEach((r, j) => {
    const lab = r.closest('label') || r.parentElement;
    const id = i + '-' + j;
    r.setAttribute('data-ac', id);
    opts.push({id: id, t: (lab ? lab.innerText : '').trim(), checked: r.checked, type: r.type});
  });
  out.push({q: qEl ? qEl.innerText.trim() : '', opts: opts});
});
return out;
"""

JS_CLICK = r"""
let n = 0;
for (const id of arguments[0]) {
  const el = document.querySelector('[data-ac="' + id + '"]');
  if (el) { if (!el.checked) el.click(); n++; }
}
return n;
"""


def match_option(options, answer):
    """(id phương án, điểm, trạng thái ok|ambiguous|low) cho MỘT đáp án."""
    ans_norm = " ".join(tokenize(strip_option_letter(clean_answer(answer))))
    scored = []
    for o in options:
        opt_norm = " ".join(tokenize(strip_option_letter(clean_answer(o["t"]))))
        if not opt_norm:
            continue
        if opt_norm == ans_norm:
            score = 1.0
        elif len(opt_norm) >= 6 and len(ans_norm) >= 6 and (ans_norm in opt_norm or opt_norm in ans_norm):
            score = 0.93
        else:
            score = token_similarity(frozenset(opt_norm.split()), frozenset(ans_norm.split()))
        scored.append((score, o["id"]))
    if not scored:
        return None, 0.0, "low"
    scored.sort(reverse=True)
    best, best_id = scored[0]
    if best < OPT_MATCH_MIN:
        return None, best, "low"
    if len(scored) > 1 and best < 1.0 and abs(scored[1][0] - best) < 0.001:
        return None, best, "ambiguous"
    return best_id, best, "ok"


def pick_options(options, answers):
    """(danh sách id cần tick, trạng thái, điểm). Hỗ trợ câu nhiều đáp án (checkbox)."""
    multi = any(o.get("type") == "checkbox" for o in options)
    picks = [match_option(options, a) for a in answers]
    ok = [p for p in picks if p[2] == "ok"]
    if not ok:
        st = "ambiguous" if any(p[2] == "ambiguous" for p in picks) else "low"
        return [], st, max((p[1] for p in picks), default=0.0)
    if multi:
        if len(ok) < len(answers):
            return [], "partial", min(p[1] for p in ok)
        return list(dict.fromkeys(p[0] for p in ok)), "ok", min(p[1] for p in ok)
    best = max(ok, key=lambda p: p[1])
    return [best[0]], "ok", best[1]


def fill_one_driver(drv, lib: Library):
    items = drv.execute_script(JS_EXTRACT_TICK) or []
    to_click, details = [], []
    filled = skipped = 0
    for it in items:
        q_text = clean_question(it.get("q", ""))
        opts = it.get("opts", [])
        short = (q_text[:70] + "…") if len(q_text) > 70 else q_text
        if len(q_text) < MIN_Q_LEN or len(opts) < 2:
            skipped += 1
            details.append(f"    ✗ không phải câu trắc nghiệm: {short}")
            continue
        item, q_score = lib.find(q_text)
        if not item:
            skipped += 1
            details.append(f"    ✗ không có trong thư viện ({q_score:.2f}): {short}")
            continue
        if item.get("c"):
            skipped += 1
            details.append(f"    ✗ đáp án đang bị nghi ngờ (cần xác minh): {short}")
            continue
        ids, status, score = pick_options(opts, item["a"])
        if status == "ok":
            to_click.extend(ids)
            filled += 1
        else:
            skipped += 1
            why = {"ambiguous": "phương án trùng điểm", "partial": "thiếu một phần đáp án"}.get(
                status, f"không khớp phương án ({score:.2f})")
            details.append(f"    ✗ {why}: {short}")
    if to_click:
        drv.execute_script(JS_CLICK, to_click)
    return filled, skipped, details


# ==================== CÀO BỔ SUNG ====================
JS_SCRAPE = r"""
const SEL = arguments[0];
const HDR = /^\s*[Cc][âÂ]u\s*\d+\s*[:.\-–—)]?\s*/;
const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_ELEMENT | NodeFilter.SHOW_TEXT);
const items = [];
let n, marks = 0;
while ((n = walker.nextNode())) {
  if (n.nodeType === 3) {
    const p = n.parentElement;
    if (!p || /^(SCRIPT|STYLE|NOSCRIPT|TEMPLATE)$/.test(p.tagName)) continue;
    const t = n.nodeValue.replace(/\s+/g, ' ').trim();
    if (t) items.push({k: 't', t: t});
  } else if (n.matches && n.matches(SEL)) {
    marks++;
    let p = n.parentElement;
    let txt = p ? (p.innerText || p.textContent || '') : '';
    if (txt.replace(/\s+/g, '').length < 3 && p && p.parentElement) txt = p.parentElement.innerText || p.parentElement.textContent || '';
    items.push({k: 'm', t: txt.replace(/\s+/g, ' ').trim()});
  }
}
const blocks = [];
let cur = null, orphans = 0;
for (let i = 0; i < items.length; i++) {
  const it = items[i];
  if (it.k === 't' && HDR.test(it.t)) {
    let rest = it.t.replace(HDR, '').trim();
    if (rest.length < 3) {
      const nx = items[i + 1];
      if (nx && nx.k === 't' && !HDR.test(nx.t)) rest = (rest + ' ' + nx.t).trim();
    }
    if (rest.length >= 3) { cur = {q: rest, correct: [], lines: []}; blocks.push(cur); }
    continue;
  }
  if (it.k === 'm') {
    if (cur) cur.correct.push(it.t); else orphans++;
  } else if (cur && cur.lines.length < 30) {
    cur.lines.push(it.t);
  }
}
return {blocks: blocks, marks: marks, orphans: orphans};
"""

JS_FIND_BUTTON = r"""
function nz(s){return (s||'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').replace(/đ/g,'d').replace(/Đ/g,'D').toLowerCase().replace(/\s+/g,' ').trim();}
const cands = Array.from(document.querySelectorAll("button, input[type=submit], input[type=button], a, .btn"));
for (const el of cands) {
  const t = nz(el.innerText || el.value || '');
  if (t.indexOf('xem dap an') !== -1) return el;
}
return null;
"""

JS_SNAPSHOT = r"""return (document.body && document.body.innerText || '').replace(/\s+/g, ' ').slice(0, 160);"""


class EmptyPageError(RuntimeError):
    pass


class Job:
    """Một đề đang cào: giữ trình duyệt riêng + bước đang chạy để watchdog phát hiện kẹt."""

    def __init__(self, exam):
        self.exam = exam
        self.drv = None
        self.stage = "chờ"
        self.t = time.time()
        self.active = False

    def set(self, stage):
        self.stage, self.t = stage, time.time()

    def get_driver(self):
        if self.drv is None:
            self.set("mở trình duyệt")
            self.drv = create_scraper_driver()
        return self.drv

    def close(self):
        drv, self.drv = self.drv, None
        kill_driver(drv, True)

    def force_kill(self):
        drv, self.drv = self.drv, None
        self.t = time.time()
        kill_driver(drv, False)


SCRAPE_CANCEL = threading.Event()
active_jobs = []
jobs_lock = threading.Lock()


def page_snapshot(drv) -> str:
    try:
        return f"url={drv.current_url} | tiêu đề={drv.title!r} | nội dung={drv.execute_script(JS_SNAPSHOT)!r}"
    except Exception:
        return "(không đọc được trang)"


def click_view_answer(drv) -> bool:
    def do_click(el):
        try:
            drv.execute_script("arguments[0].scrollIntoView({block:'center'});", el)
            el.click()
        except Exception:
            drv.execute_script("arguments[0].click();", el)

    el = drv.execute_script(JS_FIND_BUTTON)
    if el is not None:
        do_click(el)
        return True
    for css in ("input[type='submit']", "button[type='submit']"):
        for el in drv.find_elements(By.CSS_SELECTOR, css):
            try:
                if el.is_displayed() and el.is_enabled():
                    do_click(el)
                    return True
            except Exception:
                continue
    return False


def fetch_blocks(job: Job, drv, exam: dict) -> dict:
    job.set("tải trang")
    try:
        drv.get(exam["href"])
    except TimeoutException:
        raise RuntimeError(f"Tải trang quá {PAGE_TIMEOUT * 2}s")
    job.set("chờ câu hỏi")
    try:
        WebDriverWait(drv, PAGE_TIMEOUT).until(
            EC.presence_of_element_located((By.XPATH, "//*[contains(text(),'Câu ')]")))
    except TimeoutException:
        raise EmptyPageError(f"Trang không có câu hỏi sau {PAGE_TIMEOUT}s | {page_snapshot(drv)}")
    job.set("bấm xem đáp án")
    try:
        drv.execute_script("window.scrollTo(0, document.body.scrollHeight);")
        time.sleep(0.2)
    except Exception:
        pass
    if not click_view_answer(drv):
        raise RuntimeError(f"Không tìm thấy nút 'Xem đáp án' | {page_snapshot(drv)}")
    try:
        drv.switch_to.alert.accept()
    except NoAlertPresentException:
        pass
    except Exception:
        pass
    job.set("chờ dấu đáp án")
    try:
        WebDriverWait(drv, PAGE_TIMEOUT).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, MARK_SELECTOR)))
    except TimeoutException:
        pass
    job.set("trích xuất")
    return drv.execute_script(JS_SCRAPE, MARK_SELECTOR)


def get_exam_list(drv) -> list:
    log(f"Truy cập: {LIST_URL}")
    drv.get(LIST_URL)
    links = WebDriverWait(drv, PAGE_TIMEOUT).until(
        EC.presence_of_all_elements_located((By.CSS_SELECTOR, "a[href*='thi-thu.html?id=']")))
    exams, seen = [], set()
    for a in links:
        try:
            href = a.get_attribute("href") or ""
            name = a.text.strip()
            if not name or "id=" not in href:
                continue
            eid = href.split("id=")[-1].split("&")[0]
            if eid in seen:
                continue
            seen.add(eid)
            exams.append({"name": name, "href": href, "id": eid})
        except Exception:
            continue
    return exams


def finalize_votes(votes: dict):
    """votes: key -> {"q", "sets": {vk: {"n","texts","last"}}}. Trả về (final, số câu mâu thuẫn)."""
    final, conflicts = {}, 0
    for key, d in votes.items():
        sets = d["sets"]
        best_vk, best = max(sets.items(), key=lambda kv: (kv[1]["n"], kv[1]["last"]))
        best_set = set(best_vk)
        if any(not set(vk) <= best_set for vk in sets if vk != best_vk):
            conflicts += 1      # 2 lần cào ra 2 đáp án khác nhau -> không tin, để trống
            continue
        final[key] = (d["q"], best["texts"])
    return final, conflicts


def scrape_exam(job: Job) -> dict:
    exam = job.exam
    eid, name = exam["id"], exam["name"]
    short = name[:50]
    job.active = True
    job.set("bắt đầu")
    log(f"===== Cào: {name} =====")
    scrapes, votes = [], {}
    known = set()
    seq = attempts = consec_err = empty_streak = zero_new = 0
    aborted = False
    try:
        while attempts < MAX_ATTEMPTS and not SCRAPE_CANCEL.is_set():
            attempts += 1
            try:
                drv = job.get_driver()
                data = fetch_blocks(job, drv, exam)
                blocks = data.get("blocks", []) or []
                n_ans = sum(1 for b in blocks if b.get("correct"))
                if not blocks or n_ans == 0:
                    raise RuntimeError(f"Trang không có dấu đáp án (khối={len(blocks)}) | "
                                       f"{page_snapshot(drv)}")
                empty_streak = consec_err = 0
            except Exception as e:
                consec_err += 1
                empty_streak = empty_streak + 1 if isinstance(e, EmptyPageError) else 0
                text = " ".join(str(e).split()) or repr(e)
                log(f"  [{short}] Lỗi lượt #{attempts}: {type(e).__name__}: {text[:300]}")
                if empty_streak >= 2:
                    log(f"  [{short}] Trang không hiển thị câu hỏi 2 lần liên tiếp → bỏ đề.")
                    aborted = True
                    break
                if consec_err >= 2 or is_session_dead(e):
                    job.close()
                if consec_err >= MAX_CONSEC_ERRORS:
                    log(f"  [{short}] Lỗi liên tiếp {consec_err} lần → bỏ đề.")
                    aborted = True
                    break
                job.set("nghỉ sau lỗi")
                SCRAPE_CANCEL.wait(min(2 ** consec_err, 12) + random.random())
                continue

            job.set("ghi nhận")
            keys = set()
            for b in blocks:
                q = clean_question(b.get("q", ""))
                ans = dedupe_answers(b.get("correct", []))
                k = q_key(q)
                if not k or not ans:
                    continue
                seq += 1
                d = votes.setdefault(k, {"q": q, "sets": {}})
                vk = tuple(sorted(a_key(a) for a in ans))
                s = d["sets"].get(vk)
                if s is None:
                    d["sets"][vk] = {"n": 1, "texts": ans, "last": seq}
                else:
                    s["n"] += 1
                    s["last"] = seq
                keys.add(k)
            new = keys - known
            known |= keys
            scrapes.append(keys)
            zero_new = 0 if new else zero_new + 1
            T, S, Q1, Q2, s_est, cov = chao_incidence(scrapes)
            est = f" | ước lượng ~{int(round(s_est))}" if s_est else ""
            log(f"  [{short}] #{attempts}: {n_ans}/{len(blocks)} câu | mới {len(new)} | "
                f"tổng {len(known)} | phủ {cov:.0%}{est}")
            if T >= 2 and (cov >= COVERAGE_TARGET or zero_new >= ZERO_NEW_STOP):
                break
            job.set("nghỉ giữa lượt")
            SCRAPE_CANCEL.wait(random.uniform(DELAY_MIN, DELAY_MAX))
    finally:
        job.close()
        job.active = False

    T, S, Q1, Q2, s_est, cov = chao_incidence(scrapes)
    final, conflicts = finalize_votes(votes)
    if conflicts:
        log(f"  [{short}] {conflicts} câu ra đáp án mâu thuẫn giữa các lần cào → bỏ qua, không ghi vào thư viện.")
    return {"eid": eid, "name": name, "final": final, "T": T, "cov": cov,
            "attempts": attempts, "aborted": aborted, "known": len(known)}


def merge_scrape_results(results: list):
    now = time.time()
    with BO_LOCK:
        for r in results:
            if not r or r["T"] == 0:
                continue
            add = upd = same = 0
            changes = []
            for key, (q, ans) in r["final"].items():
                cur = LIB.items.get(key)
                if cur is None:
                    add += 1
                elif not cur.get("c") and same_answers(cur["a"], ans):
                    same += 1
                    continue
                else:
                    upd += 1
                    if len(changes) < 6:
                        changes.append(f"      • {q[:60]}…: {' | '.join(cur['a'])[:40]} → {' | '.join(ans)[:40]}")
                BO["questions"][key] = {"q": q, "a": ans, "t": now, "exam": r["eid"]}
                LIB.items[key] = {"q": q, "a": ans, "c": False}
            BO["exams"][r["eid"]] = {"name": r["name"], "t": now, "cov": round(r["cov"], 3), "runs": r["T"]}
            log(f"→ {r['name'][:60]}: {r['known']} câu | phủ {r['cov']:.0%} | "
                f"thêm mới {add} | đổi đáp án {upd} | giữ nguyên {same}")
            for c in changes:
                log(c)
        save_bo()
    LIB.reindex()


def run_scrape_batch(chosen: list, skipped_fresh: list, auto_tick: bool):
    global scrape_running
    SCRAPE_CANCEL.clear()
    do_tick = False
    try:
        for n in skipped_fresh:
            log(f"✔ Dùng luôn dữ liệu đã cào gần đây: {n[:60]}")
        results = []
        if chosen:
            jobs = [Job(e) for e in chosen]
            with jobs_lock:
                active_jobs[:] = jobs
            log(f"▶ Cào bổ sung {len(jobs)} đề (tối đa {MAX_PARALLEL} trình duyệt ẩn song song)…")
            pool = ThreadPoolExecutor(max_workers=min(MAX_PARALLEL, len(jobs)))
            futs = [pool.submit(scrape_exam, j) for j in jobs]
            last_hb = time.time()
            while not all(f.done() for f in futs):
                time.sleep(1)
                now = time.time()
                for j in jobs:
                    if j.active and now - j.t > WATCHDOG_SECONDS:
                        log(f"⚠ [{j.exam['name'][:40]}] đứng im ở bước '{j.stage}' > {int(now - j.t)}s "
                            f"→ đóng cưỡng bức trình duyệt đó")
                        j.force_kill()
                if now - last_hb >= 20:
                    last_hb = now
                    run = [f"{j.exam['name'][:30]} [{j.stage}]" for j in jobs if j.active]
                    if run:
                        log("⏳ Đang chạy: " + " | ".join(run))
            pool.shutdown(wait=False)
            for f in futs:
                try:
                    results.append(f.result())
                except Exception as e:
                    log(f"✘ Lỗi một đề: {type(e).__name__}: {str(e)[:150]}")
            merge_scrape_results(results)
            with jobs_lock:
                active_jobs.clear()
        if SCRAPE_CANCEL.is_set():
            log("■ Đã dừng cào (phần đã cào được vẫn lưu vào thư viện).")
        else:
            log(f"✔ Thư viện sẵn sàng: {LIB.count:,} câu (đã gồm bổ sung).")
            do_tick = auto_tick
    except Exception as e:
        log(f"✘ Lỗi cào bổ sung: {type(e).__name__}: {str(e)[:200]}")
    finally:
        scrape_running = False
        ui(update_status_ui)
        ui(refresh_buttons)
    if do_tick:
        prune_dead_sessions()
        if sessions:
            log("▶ Tự động tick sau khi cào…")
            auto_fill_all_sessions()
        else:
            log("ℹ Chưa có cửa sổ làm bài nào. Mở cửa sổ, vào đề rồi bấm nút 2.")


# ==================== GUI ====================
root = tk.Tk()
root.title("Auto-Correct v3 - Tick đáp án + Cào bổ sung")
root.geometry("760x640")
root.minsize(680, 560)

list_sessions = None
btn_open = btn_scrape = btn_stop_scrape = btn_start = btn_reload = None
log_box = lbl_browser = lbl_library = None


def ui(fn, *a):
    root.after(0, lambda: fn(*a))


def log(msg: str):
    def _append():
        log_box.config(state="normal")
        log_box.insert(tk.END, msg + "\n")
        log_box.see(tk.END)
        log_box.config(state="disabled")

    ui(_append)


def refresh_buttons():
    busy = is_running or scrape_running
    st = "disabled" if busy else "normal"
    btn_start.config(state=st)
    btn_scrape.config(state=st)
    btn_reload.config(state=st)
    btn_stop_scrape.config(state="normal" if scrape_running else "disabled")


def refresh_session_listbox():
    list_sessions.delete(0, tk.END)
    with sessions_lock:
        for s in sessions:
            list_sessions.insert(tk.END, s["name"])


def update_status_ui():
    n = len(sessions)
    if n == 0:
        lbl_browser.config(text="Trình duyệt: Chưa mở cửa sổ nào", foreground="#ef4444")
    else:
        lbl_browser.config(text=f"Trình duyệt: {n} cửa sổ InPrivate đang mở", foreground="#22c55e")
    if LIB.source == "none":
        lbl_library.config(text="Thư viện: chưa có dữ liệu (kiểm tra mạng rồi bấm Cập nhật)", foreground="#ef4444")
        return
    src = "GitHub" if LIB.source == "github" else "bản đã tải trước đó (GitHub lỗi)"
    extra = f" + {LIB.bo_applied} câu bổ sung" if LIB.bo_applied else ""
    with BO_LOCK:
        nbo = len(BO["questions"])
    if nbo and not LIB.bo_applied:
        extra = f" (+{nbo} câu bổ sung)"
    lbl_library.config(
        text=f"Thư viện: {LIB.count:,} câu — {src}, đăng {fmt_dt(LIB.date)}{extra}",
        foreground="#22c55e" if LIB.source == "github" else "#eab308",
    )


def reload_library():
    global LIB
    ui(refresh_buttons)
    log("⟳ Đang tải thư viện từ GitHub…")
    new_lib = load_library_full()
    if new_lib:
        LIB = new_lib
        tag = "GitHub" if new_lib.source == "github" else "bản cache (GitHub không truy cập được)"
        log(f"✔ Thư viện sẵn sàng: {new_lib.count:,} câu — nguồn: {tag}, đăng {fmt_dt(new_lib.date)}"
            + (f", áp {new_lib.bo_applied} câu bổ sung" if new_lib.bo_applied else ""))
    else:
        log("✘ Không tải được thư viện và chưa có cache. Kiểm tra kết nối mạng.")
    ui(update_status_ui)
    ui(refresh_buttons)


def open_new_session():
    def work():
        global _next_session_id
        try:
            log("⟳ Đang mở cửa sổ Edge InPrivate…")
            drv = create_driver()
            drv.get(BASE_URL)
            with sessions_lock:
                sid = _next_session_id
                _next_session_id += 1
                sessions.append({"id": sid, "name": f"Cửa sổ {sid} (InPrivate)", "driver": drv})
            log(f"✔ Đã mở Cửa sổ {sid}. Vào trang làm bài rồi bấm nút 2 (hoặc Cào bổ sung).")
            ui(refresh_session_listbox)
            ui(update_status_ui)
        except Exception as e:
            msg = str(e)[:900]
            log(f"✘ Lỗi mở trình duyệt: {msg}")
            ui(lambda: messagebox.showerror("Lỗi mở trình duyệt", msg))

    threading.Thread(target=work, daemon=True).start()


def close_selected_session():
    sel = list_sessions.curselection()
    if not sel:
        messagebox.showinfo("Thông báo", "Hãy chọn cửa sổ cần đóng trong danh sách.")
        return
    with sessions_lock:
        if sel[0] >= len(sessions):
            return
        s = sessions.pop(sel[0])
    try:
        s["driver"].quit()
    except Exception:
        pass
    refresh_session_listbox()
    update_status_ui()


def run_fill_one(s):
    t0 = time.time()
    try:
        f, sk, details = fill_one_driver(s["driver"], LIB)
        return s, f, sk, details, None, time.time() - t0
    except Exception as e:
        return s, 0, 0, [], str(e)[:120], time.time() - t0


def auto_fill_all_sessions():
    global is_running
    if is_running:
        return
    if LIB.count == 0:
        ui(lambda: messagebox.showerror("Lỗi", "Thư viện chưa có dữ liệu. Bấm 'Cập nhật thư viện' trước."))
        return
    prune_dead_sessions()
    ui(refresh_session_listbox)
    ui(update_status_ui)
    with sessions_lock:
        snapshot = list(sessions)
    if not snapshot:
        ui(lambda: messagebox.showwarning(
            "Chưa sẵn sàng", "Chưa có cửa sổ nào.\nHãy mở cửa sổ và vào trang làm bài trước."))
        return

    is_running = True
    ui(refresh_buttons)
    log(f"▶ Bắt đầu tick {len(snapshot)} cửa sổ song song…")
    try:
        total_f = total_s = 0
        with ThreadPoolExecutor(max_workers=min(len(snapshot), 6)) as pool:
            for s, f, sk, details, err, dt in pool.map(run_fill_one, snapshot):
                if err:
                    log(f"• {s['name']}: LỖI — {err}")
                    continue
                total_f += f
                total_s += sk
                log(f"• {s['name']}: điền {f} | bỏ trống {sk} ({dt:.1f}s)")
                for d in details:
                    log(d)
        log(f"■ Xong. Tổng điền: {total_f} | Tổng bỏ trống: {total_s}. Bạn tự kiểm tra, tick nốt câu sót và nộp bài.")
        ui(lambda: messagebox.showinfo(
            "Hoàn thành",
            f"Đã tick xong (chưa nộp bài).\nTổng điền: {total_f} | Tổng bỏ trống: {total_s}\n"
            "Xem chi tiết câu bỏ trống trong khung nhật ký.",
        ))
    except Exception as e:
        msg = str(e)[:500]
        log(f"✘ Lỗi: {msg}")
        ui(lambda: messagebox.showerror("Lỗi", msg))
    finally:
        is_running = False
        ui(refresh_buttons)


# ---------- luồng "Cào bổ sung" ----------
def start_scrape_flow():
    global scrape_running
    if scrape_running or is_running:
        return
    if LIB.count == 0:
        messagebox.showerror("Lỗi", "Thư viện chưa có dữ liệu. Bấm 'Cập nhật thư viện' trước.")
        return
    scrape_running = True
    refresh_buttons()
    threading.Thread(target=prepare_scrape, daemon=True).start()


def end_scrape_flow():
    global scrape_running
    scrape_running = False
    refresh_buttons()


def prepare_scrape():
    log("⟳ Đang tải danh sách đề từ website…")
    drv, exams = None, []
    try:
        drv = create_scraper_driver()
        exams = get_exam_list(drv)
    except Exception as e:
        msg = str(e)[:600]
        log(f"✘ Không tải được danh sách đề: {msg}")
        ui(lambda: messagebox.showerror("Lỗi", f"Không tải được danh sách đề:\n{msg}"))
    finally:
        kill_driver(drv, True)
    if not exams:
        ui(end_scrape_flow)
        return
    log(f"✔ Tìm thấy {len(exams)} đề trên web.")
    ui(show_scrape_dialog, exams)


def show_scrape_dialog(exams: list):
    now = time.time()
    fresh = {}
    with BO_LOCK:
        for e in exams:
            m = BO["exams"].get(e["id"])
            if m and now - float(m.get("t", 0)) < FRESH_SECONDS and float(m.get("t", 0)) > LIB.date \
                    and float(m.get("cov", 0)) >= FRESH_MIN_COV:
                fresh[e["id"]] = now - float(m["t"])

    dlg = tk.Toplevel(root)
    dlg.title("Chọn đề để cào bổ sung")
    dlg.geometry("600x560")
    dlg.transient(root)
    dlg.grab_set()

    tk.Label(dlg, text="Chọn 2-3 đề cần cào lại (Ctrl/Shift để chọn nhiều):",
             font=("Segoe UI", 10, "bold")).pack(anchor="w", padx=12, pady=(10, 2))
    frow = tk.Frame(dlg)
    frow.pack(fill="x", padx=12)
    tk.Label(frow, text="Lọc:").pack(side="left")
    filt = tk.StringVar()
    ttk.Entry(frow, textvariable=filt).pack(side="left", fill="x", expand=True, padx=6)

    fl = tk.Frame(dlg)
    fl.pack(fill="both", expand=True, padx=12, pady=6)
    lb = tk.Listbox(fl, selectmode="extended", font=("Segoe UI", 10), exportselection=False)
    sb = ttk.Scrollbar(fl, orient="vertical", command=lb.yview)
    lb.configure(yscrollcommand=sb.set)
    sb.pack(side="right", fill="y")
    lb.pack(side="left", fill="both", expand=True)

    chosen_ids, visible = set(), []

    def label(e):
        s = e["name"]
        if e["id"] in fresh:
            s += f"    ✔ đã cào {fmt_ago(fresh[e['id']])} — dùng luôn"
        return s

    def refill(*_):
        lb.delete(0, tk.END)
        visible.clear()
        q = filt.get().strip().casefold()
        for e in exams:
            if q and q not in e["name"].casefold():
                continue
            visible.append(e)
            lb.insert(tk.END, label(e))
            if e["id"] in chosen_ids:
                lb.selection_set(tk.END)

    def on_select(_=None):
        sel = set(lb.curselection())
        for i, e in enumerate(visible):
            if i in sel:
                chosen_ids.add(e["id"])
            else:
                chosen_ids.discard(e["id"])

    lb.bind("<<ListboxSelect>>", on_select)
    filt.trace_add("write", refill)
    refill()

    force = tk.BooleanVar(value=False)
    auto_tick = tk.BooleanVar(value=True)
    ttk.Checkbutton(dlg, text="Cào lại cả đề đã cào trong 24h qua", variable=force).pack(anchor="w", padx=12)
    ttk.Checkbutton(dlg, text="Tự động tick sau khi cào xong", variable=auto_tick).pack(anchor="w", padx=12)
    tk.Label(dlg, text=f"Cào tới khi độ phủ ước lượng ≥ {COVERAGE_TARGET:.0%} "
                       f"(tối đa {MAX_ATTEMPTS} lượt/đề).", fg="#64748b").pack(anchor="w", padx=12, pady=(4, 0))

    def cancel():
        dlg.destroy()
        end_scrape_flow()

    def go():
        picked = [e for e in exams if e["id"] in chosen_ids]
        if not picked:
            messagebox.showwarning("Chưa chọn", "Bạn chưa chọn đề nào.", parent=dlg)
            return
        if force.get():
            to_scrape, skipped = picked, []
        else:
            to_scrape = [e for e in picked if e["id"] not in fresh]
            skipped = [e["name"] for e in picked if e["id"] in fresh]
        at = auto_tick.get()
        dlg.destroy()
        refresh_buttons()
        threading.Thread(target=run_scrape_batch, args=(to_scrape, skipped, at), daemon=True).start()

    bf = tk.Frame(dlg)
    bf.pack(pady=12)
    ttk.Button(bf, text="Bắt đầu cào", command=go).pack(side="left", padx=6)
    ttk.Button(bf, text="Hủy", command=cancel).pack(side="left", padx=6)
    dlg.protocol("WM_DELETE_WINDOW", cancel)


def stop_scrape():
    SCRAPE_CANCEL.set()
    log("⏹ Đang dừng cào (các trình duyệt sẽ dừng sau bước hiện tại)…")


def on_close():
    SCRAPE_CANCEL.set()
    with jobs_lock:
        for j in active_jobs:
            try:
                j.force_kill()
            except Exception:
                pass
    with sessions_lock:
        for s in sessions:
            try:
                s["driver"].quit()
            except Exception:
                pass
        sessions.clear()
    root.destroy()


# ---------- dựng giao diện ----------
tk.Label(root, text="Auto-Correct — Edge InPrivate · tick mọi cửa sổ",
         font=("Segoe UI", 13, "bold")).pack(pady=(12, 6))

frame_btn = tk.Frame(root)
frame_btn.pack(pady=2)
btn_open = ttk.Button(frame_btn, text="1. Mở cửa sổ mới (InPrivate)", command=open_new_session)
btn_open.pack(side="left", padx=4)
btn_scrape = ttk.Button(frame_btn, text="Cào bổ sung đề…", command=start_scrape_flow)
btn_scrape.pack(side="left", padx=4)
btn_start = ttk.Button(
    frame_btn, text="2. Bắt đầu làm bài (tất cả cửa sổ)",
    command=lambda: threading.Thread(target=auto_fill_all_sessions, daemon=True).start(),
)
btn_start.pack(side="left", padx=4)

frame_btn2 = tk.Frame(root)
frame_btn2.pack(pady=2)
btn_reload = ttk.Button(frame_btn2, text="Cập nhật thư viện",
                        command=lambda: threading.Thread(target=reload_library, daemon=True).start())
btn_reload.pack(side="left", padx=4)
btn_stop_scrape = ttk.Button(frame_btn2, text="Dừng cào", command=stop_scrape, state="disabled")
btn_stop_scrape.pack(side="left", padx=4)

tk.Label(root, text="Danh sách cửa sổ đang mở:", font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=20, pady=(10, 2))
frame_list = tk.Frame(root)
frame_list.pack(fill="x", padx=20)
list_sessions = tk.Listbox(frame_list, height=4, font=("Segoe UI", 10))
list_sessions.pack(side="left", fill="x", expand=True)
ttk.Button(frame_list, text="Đóng cửa sổ\nđang chọn", command=close_selected_session).pack(side="left", padx=8)

frame_status = tk.Frame(root, pady=8)
frame_status.pack(fill="x", padx=20)
lbl_browser = tk.Label(frame_status, text="", font=("Segoe UI", 10, "bold"))
lbl_browser.pack(anchor="w", pady=1)
lbl_library = tk.Label(frame_status, text="Thư viện: đang tải…", font=("Segoe UI", 10, "bold"))
lbl_library.pack(anchor="w", pady=1)

tk.Label(root, text="Nhật ký:", font=("Segoe UI", 9, "bold")).pack(anchor="w", padx=20)
log_box = scrolledtext.ScrolledText(root, height=14, font=("Consolas", 9), state="disabled", wrap="word")
log_box.pack(fill="both", expand=True, padx=20, pady=(2, 6))

tk.Label(
    root,
    text="Cách dùng: Mở cửa sổ → vào đề → (nếu thư viện cũ) bấm 'Cào bổ sung', chọn đề → tool cào rồi tự tick; "
         "hoặc bấm (2) để tick ngay. Tool không tự nộp bài.",
    font=("Segoe UI", 8), foreground="#64748b", wraplength=700, justify="left",
).pack(padx=20, pady=(0, 8))

root.protocol("WM_DELETE_WINDOW", on_close)
update_status_ui()
threading.Thread(target=reload_library, daemon=True).start()
root.mainloop()
