# =========================
# Imports
# =========================
import streamlit as st
import random
import time
import os
import io
import json
import math
import datetime
from PIL import Image as _PILImage, ImageDraw
from fpdf import FPDF
import ast
import contextlib
from io import StringIO
import unicodedata  # pro normalizaci klíčů v JSONu
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent

def find_file(*cands):
    for c in cands:
        p = Path(c)
        if not p.is_absolute():
            p = BASE_DIR / p  # hledej relativně k souboru
        if p.exists():
            return str(p)
    return None

import time
import streamlit as st

# kolik dlaždic se má odhalit (ponech číslo, které používáš)
TASKS_TO_REVEAL = 20

def make_defaults():
    return dict(
        game_started=False,
        tasks_solved_for_reveal=0,
        score=0,
        best_score=0,
        best_time=float("inf"),
        start_time=None,
        end_time=None,
        current_task=None,
        last_selected_fairytale=None,
        last_selected_class=None,
        last_selected_subject=None,
        revealed_tiles=[False] * TASKS_TO_REVEAL,  # ⬅︎ navázáno na konstantu
        tile_coords=[],
        feedback_message="",
        feedback_type="",
        final_report=None,
        history=[],
        show_full_fairytale=False,
        achievement_date=None,
        diploma_image_path=None,
        current_cjl_task=None,
        _it_index=0,
        _it_last_output="",
        _it_last_eval="",
        _cjl_index=0,
    )

def init_state():
    # inicializuj jen jednou na začátku relace
    if not st.session_state.get("_init_done", False):
        for k, v in make_defaults().items():
            if k not in st.session_state:
                st.session_state[k] = v
        st.session_state["_init_done"] = True

# zavolej co nejdřív (před renderem UI)
init_state()

def _grade_band(grade_str: str) -> str:
    # "1. třída" → 1, "9. třída" → 9
    try:
        n = int(str(grade_str).split(".")[0])
    except Exception:
        n = 1
    return "6-9" if n >= 6 else "1-5"

# =========================
# Bezpečné spouštění Pythonu (IT)
# =========================
# hned po importech / na startu aplikace

def is_code_safe(src: str) -> bool:
    try:
        tree = ast.parse(src, mode="exec")
    except SyntaxError:
        return False
    for node in ast.walk(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom, ast.With, ast.Try, ast.Raise)):
            return False
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id in {"exec", "eval", "open", "__import__"}:
            return False
        if isinstance(node, ast.Attribute) and isinstance(node.attr, str) and node.attr.startswith("__"):
            return False
    return True

def run_user_code_capture_stdout(src: str):
    if not is_code_safe(src):
        return False, "Kód není povolen (import/exec/eval/with/try/open/__import__/__dunder__ zakázáno)."
    fake_out = StringIO()
    safe_builtins = {"print": print, "range": range, "len": len, "abs": abs, "round": round}
    env = {"__builtins__": safe_builtins}
    try:
        with contextlib.redirect_stdout(fake_out):
            exec(src, env, env)
    except Exception as e:
        return False, f"Chyba: {e}"
    return True, fake_out.getvalue().strip()

def start_new_game():
    st.session_state.update({
        "game_started": True,
        "tasks_solved_for_reveal": 0,
        "history": [],
        "feedback_message": "",
        "feedback_type": "",
        "current_task": None,
        "start_time": time.time(),
        "end_time": None,
        "final_report": None,
        "revealed_tiles": [False] * TASKS_TO_REVEAL,
        "tile_coords": [],
    })
    prepare_tiles()
    st.rerun()

# =========================
# Matematické utility
# =========================
def normalize_decimal(s: str):
    s = (s or "").strip().replace(" ", "").replace(",", ".")
    if s == "": raise ValueError("empty")
    return float(s)

def approx_equal(a: float, b: float, tol=1e-2): return abs(a - b) <= tol

def parse_div_remainder(s: str):
    ss = s.strip().lower().replace(" ", "")
    if "zb." not in ss: raise ValueError("missing 'zb.'")
    parts = ss.split("zb.")
    if len(parts) != 2: raise ValueError("bad format")
    return int(parts[0]), int(parts[1])

def reduce_fraction(a, b):
    g = math.gcd(abs(a), abs(b)); a //= g; b //= g
    if b < 0: a, b = -a, -b
    return a, b

def parse_fraction(s: str):
    if "/" not in s: raise ValueError("not a fraction")
    parts = s.replace(" ", "").split("/")
    if len(parts) != 2: raise ValueError("bad fraction")
    a, b = int(parts[0]), int(parts[1])
    if b == 0: raise ValueError("zero denom")
    return a, b

def fraction_equal_reduced(user_str, target_str):
    ua, ub = parse_fraction(user_str); ra, rb = reduce_fraction(ua, ub)
    ta, tb = parse_fraction(target_str); ta, tb = reduce_fraction(ta, tb)
    return (ra == ta and rb == tb and (ua, ub) == (ra, rb))

def parse_ratio(s: str):
    ss = s.replace(" ", ""); 
    if ":" not in ss: raise ValueError("missing ':'")
    a, b = ss.split(":"); a, b = int(a), int(b)
    return reduce_fraction(a, b)

def is_prime(n: int) -> bool:
    if n < 2: return False
    if n % 2 == 0: return n == 2
    r = int(n**0.5)
    for d in range(3, r+1, 2):
        if n % d == 0: return False
    return True

def prime_factorization_dict(n: int) -> dict:
    d, f = 2, {}; x = n
    while d * d <= x:
        while x % d == 0:
            f[d] = f.get(d, 0) + 1; x //= d
        d = 3 if d == 2 else d + 2
    if x > 1: f[x] = f.get(x, 0) + 1
    return f

def parse_pf_input(s: str) -> dict:
    ss = (s or "").strip().lower().replace(" ", "")
    ss = ss.replace("×", "*").replace("x", "*")
    parts = [p for p in ss.split("*") if p]
    if not parts: raise ValueError("empty factorization")
    factors = {}
    for token in parts:
        if "^" in token: base, exp = token.split("^", 1); e = int(exp)
        elif "**" in token: base, exp = token.split("**", 1); e = int(exp)
        else: base, e = token, 1
        p = int(base)
        if not is_prime(p): raise ValueError("non-prime factor")
        factors[p] = factors.get(p, 0) + e
    return factors

def pf_equal(user_str: str, n_target: int) -> bool:
    try: uf = parse_pf_input(user_str)
    except Exception: return False
    return uf == prime_factorization_dict(n_target)

def normalize_yes_no(s: str):
    if s is None: raise ValueError("empty")
    t = s.strip().lower()
    if t in {"ano","a","y","yes","true","1"}: return "ano"
    if t in {"ne","n","no","false","0"}: return "ne"
    raise ValueError("not yes/no")

def ensure_task4(task):
    if isinstance(task, (list, tuple)):
        if len(task) == 4: return task[0], task[1], task[2], task[3]
        if len(task) == 3: return task[0], task[1], task[2], None
        if len(task) == 2: return task[0], task[1], "int", None
    return str(task), "", "info", None

# =========================
# Robustní loader Množin z ma_tasks_sets.json
# =========================
_loaded_ma_sets_path = None
ma_sets_tasks_by_level = {}
for pth in [
    "ma_tasks_sets.json",
    "/mnt/data/ma_tasks_sets.json",
    r"C:\Users\jb\Documents\pohadky_app\ma_tasks_sets.json",   # ← přidáno
]:
    if os.path.exists(pth):
        with open(pth, "r", encoding="utf-8") as f:
            ma_sets_tasks_by_level = json.load(f)
        _loaded_ma_sets_path = pth
        break


def _norm_key(s: str) -> str:
    if s is None: return ""
    t = unicodedata.normalize("NFKD", str(s)).encode("ascii", "ignore").decode("ascii")
    t = t.lower().replace("–","-").replace("—","-")
    for ch in [" ", ".", "_", "-", ":", ";", "\u00a0"]:
        t = t.replace(ch, "")
    return t

def _dict_get_norm(d: dict, wanted: str):
    want = _norm_key(wanted)
    for k, v in d.items():
        if _norm_key(k) == want:
            return v, k
    return None, None

def _flatten_rounds(val):
    if not isinstance(val, dict): return []
    rounds = val.get("rounds")
    if isinstance(rounds, list):
        flat = []
        for rnd in rounds:
            if isinstance(rnd, list):
                flat.extend([x for x in rnd if isinstance(x, dict)])
        return flat
    return []

def _extract_task_list(value):
    if isinstance(value, list):
        return [x for x in value if isinstance(x, dict)]
    if isinstance(value, dict):
        flat = _flatten_rounds(value)
        if flat: return flat
        for key in ["tasks", "items", "data", "list"]:
            if key in value and isinstance(value[key], list):
                return [x for x in value[key] if isinstance(x, dict)]
    return []

def get_sets_block(level: str, topic: str):
    """Najde blok úloh i pro fused klíč '1. třída – množiny' + rounds.
       Když je topic 'Množiny – základ', akceptuje i obecné 'množiny'.
    """
    if not (_loaded_ma_sets_path and isinstance(ma_sets_tasks_by_level, dict) and ma_sets_tasks_by_level):
        return []

    # 1) klasický tvar: json[level][topic]
    lvl_val, _lvl_key = _dict_get_norm(ma_sets_tasks_by_level, level)
    if isinstance(lvl_val, dict):
        top_val, _top_key = _dict_get_norm(lvl_val, topic) or (None, None)
        if top_val is None:
            alt = topic.replace("–","-") if "–" in topic else topic.replace("-","–")
            top_val, _top_key = _dict_get_norm(lvl_val, alt) or (None, None)
        if top_val is not None:
            return _extract_task_list(top_val)

    # 2) fused: např. "1. třída – množiny" (bez „základ“)
    want_lvl = _norm_key(level)
    # akceptuj několik možných tokenů tématu
    topic_norms = {_norm_key(topic)}
    # speciálně u "Množiny – základ" ber i obecné "množiny"
    topic_norms.add(_norm_key("Množiny"))
    topic_norms.add("mnoziny")  # jistota

    best = []
    for k, v in ma_sets_tasks_by_level.items():
        nk = _norm_key(k)
        if want_lvl in nk and any(t in nk for t in topic_norms):
            tasks = _extract_task_list(v)
            if tasks:
                best = tasks
                break

    return best

def normalize_task_type(t):
    if not t: return "int"
    x = str(t).strip().lower()
    if x in {"yn","yesno","yes_no","ano_ne","ano-ne","boolean"}: return "yn"
    if x in {"int","number","count"}: return "int"
    return "int"

def pick_json_task(task_list):
    """Vrátí:
       - MCQ: ("__MA_MCQ__", {"text":..., "options":[...], "correct":"a"}, "mcq", None)
       - QA : (q, a, type, explain)
    """
    random.shuffle(task_list)
    for t in task_list:
        if not isinstance(t, dict): continue
        # MCQ (text/options/correct_option)
        if "options" in t and "text" in t and "correct_option" in t:
            opts = t["options"]
            if isinstance(opts, list) and len(opts) >= 2:
                norm = {"text": str(t["text"]), "options": list(opts),
                        "correct": str(t["correct_option"]).strip().lower()}
                return ("__MA_MCQ__", norm, "mcq", None)
        # QA (q/a/type)
        q = t.get("q") or t.get("question") or t.get("text")
        a = t.get("a") or t.get("answer") or t.get("ans")
        if q is None or a is None: continue
        typ = normalize_task_type(t.get("type"))
        if typ == "yn":
            try: a = normalize_yes_no(a)
            except Exception: continue
        return (str(q), str(a), typ, t.get("explain") or t.get("explanation"))
    return None

# ---------- ČJ: filtrace existujících bloků v JSONu podle prefixu ----------
def _cjl_flatten_rounds(level: str):
    rounds = cjl_tasks_by_level.get(level, {}).get("rounds", [])
    flat = []
    for rnd in rounds:
        if isinstance(rnd, list):
            flat.extend([t for t in rnd if isinstance(t, dict)])
    return flat

def cjl_pool_from_json(level: str, prefix: str):
    """Vezme z JSONu jen úlohy, jejichž 'text' začíná na daný prefix."""
    flat = _cjl_flatten_rounds(level)
    return [t for t in flat if isinstance(t.get("text"), str) and t["text"].strip().startswith(prefix)]

import re, random

# Sady souhlásek (pro „ch“ stačí kontrola na předchozí znak 'h')
_HARD = set(list("hkrdtn"))
_SOFT = set(list("žščřcjďťň"))

def _word_token(text: str) -> str:
    # z textu typu "Doplň: ch_tit" vydoluje "ch_tit"
    m = re.search(r":\s*([^:]+)$", text or "")
    return (m.group(1) if m else text or "").strip()

def _prev_char_before_gap(text: str) -> str:
    tok = _word_token(text)
    i = tok.find("_")
    return tok[i-1].lower() if i > 0 else ""

def _correct_letter(task: dict) -> str:
    """Vrátí skutečné písmeno správné možnosti (i, í, y, ý …) podle options a correct_option."""
    key = (task.get("correct_option") or "").strip().lower()
    mapping = {}
    for opt in task.get("options", []):
        m = re.match(r"\s*([a-c])\)\s*(.+)\s*$", opt, re.I)
        if m:
            mapping[m.group(1).lower()] = m.group(2).strip()
    return mapping.get(key, "")

def cjl_pool_2_y_hard():
    flat = _cjl_flatten_rounds("2. třída")
    out = []
    for t in flat:
        if not isinstance(t, dict): 
            continue
        ch = _prev_char_before_gap(t.get("text",""))
        corr = _correct_letter(t)
        # 'h' zahrnuje i 'ch' (v zápisu "ch_tit" je před podtržítkem právě 'h')
        if ch in _HARD and corr in ("y","ý"):
            out.append(t)
    random.shuffle(out)
    return out

def cjl_pool_2_i_soft():
    flat = _cjl_flatten_rounds("2. třída")
    out = []
    for t in flat:
        if not isinstance(t, dict): 
            continue
        ch = _prev_char_before_gap(t.get("text",""))
        corr = _correct_letter(t)
        if ch in _SOFT and corr in ("i","í"):
            out.append(t)
    random.shuffle(out)
    return out

# ---------- ČJ: generátor 'Vyber správnou slabiku (nejjednodušší slova)' ----------
def cjl_gen_pick_syllable_easy(n: int = 30):
    """Vrátí list MCQ úloh: 'Vyber správnou slabiku, která je na začátku slova …'"""
    bank = [
        ("kolo",   ["ko","lo","ka"], "a"),
        ("domek",  ["mek","da","do"], "c"),
        ("máma",   ["má","la","ko"], "a"),
        ("táta",   ["ti","to","tá"], "c"),
        ("váza",  ["za","vá","ze"], "b"),
        ("nora",   ["na","no","ra"], "b"),
        ("noha",   ["po","ha","no"], "c"),
        ("ryba",   ["ry","ra","ro"], "a"),
        ("lampa",  ["lam","pa","la"], "a"),
        ("seno",   ["no","si","se"], "c"),
        ("víla",   ["la","vi","ví"], "c"),
        ("drak",   ["drak","dr","ak"], "a"),
        ("okno",   ["ok","ko","no"], "a"),
        ("koza",   ["ko","za","ku"], "a"),
        ("voda",   ["vo","vu","va"], "a"),

        ("pes",    ["pe","es","pes"], "c"),
        ("lama",   ["la","ma","am"], "a"),
        ("sova",   ["so","ov","va"], "a"),
        ("díra",   ["di","dí","ra"], "b"),
        ("město",  ["měs","st","to"], "a"),
        ("kůň",    ["ku","ků","kůň"], "c"),
        ("čára",   ["ča","čá","ra"], "b"),
        ("židle",  ["žid","žd","le"], "a"),
        ("šaty",   ["ša","šat","ty"], "a"),
        ("husa",   ["hu","ha","su"], "a"),
        ("med",    ["med","em","md"], "a"),
        ("teta",   ["ta","te","to"], "b"),
        ("luk",    ["lu","uk","luk"], "c"),
        ("hora",   ["ho","ha","ro"], "a"),
        ("auto",   ["au","ut","to"], "a"),
        ("pole",   ["pol","le","po"], "c"),
        ("řeka",   ["ře","re","řek"], "a"),
        ("vosa",   ["vos","sa","vo"], "c"),
        ("míč",    ["mi","míč","my"], "b"),
        ("něco",   ["ně","ne","něc"], "a"),
        ("tělo",   ["těl","te","tě"], "c"),
        ("děda",   ["dě","de","da"], "a"),
        ("pila",   ["li","la","pi"], "c"),
        ("kára",   ["ka","ká","rá"], "b"),
        ("mýdlo",  ["my","mý","mýd"], "c"),
        ("brána",  ["brán","bra","brá"], "c"),
        ("hra",    ["hra","ha","ra"], "a"),
        ("chata",  ["cha","ha","chat"], "a"),
        ("louka",  ["lou","lo","lu"], "a"),
        ("moře",   ["moř","mo","ře"], "b"),
        ("prase",  ["pra","pa","ra"], "a"),
        ("vlak",   ["vlak","va","vl"], "a"),
        ("krabice",["kra","ka","ra"], "a"),
        ("sedlo",  ["se","sed","so"], "b"),
        ("list",   ["li","list","la"], "b"),
        ("ráno",   ["ra","rá","rý"], "b"),
        ("sníh",   ["sni","sníh","sn"], "b"),
        ("včela",  ["vče","vč","vci"], "a"),
        ("křída",  ["kři","kří","kry"], "b"),
        ("svíčka", ["svi","svíč","sv"], "b"),
        ("klíč",   ["kli","klíč","kl"], "b"),
        ("mléko",  ["mlé","mle","ml"], "a"),
        ("dřevo",  ["dre","dře","dř"], "b"),
        ("topení", ["to","te","ta"], "a"),
        ("sáně",   ["sá","san","se"], "a"),
        ("louže",  ["lou","lo","lu"], "a"),
        ("koleda", ["ko","kol","le"], "a"),
        ("květ",   ["k","květ","ky"], "b"),
        ("mrak",   ["mrak","ma","ra"], "a"),
        ("dívka",  ["div","dív","di"], "b"),
        ("měkký",  ["měk","mek","mě"], "a"),
        ("jablko", ["ja","jab","ab"], "a"),
        ("cukr",   ["cu","cuk","kr"], "a"),
        ("věž",    ["věž","ve","vž"], "a"),
        ("život",  ["ži","živ","vo"], "a"),
    ]

    import random
    pool = bank.copy()
    random.shuffle(pool)

    # vyber bez duplicit; když chceš víc než je v bance, dober s opakováním
    if n <= len(pool):
        chosen = pool[:n]
    else:
        chosen = pool + random.choices(pool, k=n - len(pool))

    tasks = []
    for word, options, correct in chosen:
        # options s prefixy "a) / b) / c)" pro zobrazení
        prefixed = [f"a) {options[0]}", f"b) {options[1]}", f"c) {options[2]}"]
        tasks.append({
            "text": f"Vyber správnou slabiku na začátku slova **{word}**:",
            "options": prefixed,
            "correct_option": correct  # pořád "a" | "b" | "c"
        })
    return tasks

# ---------- ČJ: generátor 'Tvrdé a měkké čtení po d, t, n' ----------
# ---------- ČJ: generátor 'Tvrdé a měkké čtení po d, t, n' ----------
def cjl_gen_soft_hard_dtn(n: int = 30):
    """
    MCQ: 'Slabiku „..“ ve slově „…“ čteme: a) měkce, b) tvrdě, c) obě možnosti'
    Zjednodušené pravidlo: měkce = di/ti/ni; dí/tí/ní. Tvrdě = dy/ty/ny; dý/tý/ný.
    """
    import random
    soft_examples = [
        ("dí", "díky"), ("di", "divadlo"), ("ti", "děti"),("ti", "cítit"),
        ("ti", "ticho"), ("ti", "tisk"), ("dí", "díra"), ("di", "divák"),("di","hodiny"),
        ("dí", "chodí"),("dí","budík"),("dí","budí"),("tí","fotí"),("ti","tiše!"),
        ("ti", "tati!"),("tí","letí"),("dí","budík"), ("tí","smetí"),("tí","svítí"),
        ("tí","kvítí"),("ti","tisíc",),("ti","štika"),("ti","čerti"),("tí","utíká"),
        ("tí","natírá"),("ní","koník"),("ni","nikdy"),("ní", "jarní"),("ni","knihy"),
        ("tí","stíny"),("ní","zvoní"),("ní","vodník"),("ní","peníze"),("ní", "kominík"),
        ("ní", "nízko"), ("tí","platí"),("di","rodina"),("di","divoký")
    ]
    hard_examples = [
        ("dý", "dýka"), ("dý", "dýně"),("dý","dým"),("dy","tady"),("dý","dýmka"),
        ("dy","jahody"),("ny","hodiny"),("dý","mladý"),("ty","boty"),("ty","paty"),
        ("ty","noty"),("tý","motýli"),("ty","motyka"),("ný","líný"),("ny","sny"),("ny","dny"),
        ("ny","rány"),("ny","ceny"),("dy","nikdy"),("ný","černý"),("ny","zvony"),("ny","bedny"),
        ("ty", "typ"),  ("tý", "týden"), ("ný", "kamenný"), ("dy","schody"),("dy","rady"),("ný","hodný")  # 'ný' – hodnotíme čtení 'n' + 'ý' jako tvrdé
    ]
    # připravíme banku s označením správné odpovědi ('a' = měkce, 'b' = tvrdě)
    bank = [("a", syl, word) for syl, word in soft_examples] + \
           [("b", syl, word) for syl, word in hard_examples]
    random.shuffle(bank)

    # výběr bez opakování do vyčerpání zásoby; případný „doběr“ s opakováním
    if n <= len(bank):
        chosen = bank[:n]
    else:
        chosen = bank + random.choices(bank, k=n - len(bank))

    out = []
    for corr, syl, word in chosen:
        out.append({
            "text": f"Slabiku **„{syl}“** ve slově **„{word}“** čteme:",
            "options": ["a) měkce", "b) tvrdě", "c) obě možnosti"],
            "correct_option": corr
        })
    return out

import random, re

# 4. třída – z JSONu: jednoslovné položky "Urči slovní druh: …"
def cjl_pool_4_pos_words():
    flat = _cjl_flatten_rounds("4. třída")
    out = []
    for t in flat:
        if not isinstance(t, dict): 
            continue
        txt = (t.get("text") or "").strip()
        # bereme jen úlohy tohoto typu (v JSONu jsou takto pojmenované)
        if txt.startswith("Urči slovní druh"):
            out.append(t)
    random.shuffle(out)
    return out

# 4. třída – generátor: krátké věty s určením slovního druhu
def cjl_gen_4_pos_sentence_v2(n: int = 24):
    import random
    nouns_m = ["princ", "král", "vlk", "pastýř", "dědeček"]
    nouns_f = ["Sněhurka", "babička", "královna", "Karkulka", "víla"]
    adjs    = ["statečný", "rychlý", "tichý", "unavený", "zelený", "zlatý", "mocný", "malý", "velký"]
    verbs   = ["běží", "spí", "pracuje", "čaruje", "vládne", "čeká", "čte", "píše", "hledá", "zpívá"]
    adverbs = ["rychle", "tiše", "dnes", "ráno", "večer"]

    def make_item():
        which = random.choice(["noun","verb","adj"])

        # jednoduché věty v přítomném čase (bez rod/čísel – není třeba shoda v min. čase)
        subj = random.choice(nouns_m + nouns_f)
        if which == "noun":
            # cílem je podst. jméno
            sentence = f"{random.choice(adjs)} {subj} {random.choice(verbs)}."
            target   = subj
            corr     = "a"
        elif which == "verb":
            sentence = f"{subj} {random.choice(adverbs)} {random.choice(verbs)}."
            target   = sentence.split()[-1].rstrip(".")
            corr     = "b"
        else:  # adj
            sentence = f"{subj} je {random.choice(adjs)}."
            target   = sentence.split()[-1].rstrip(".")
            corr     = "c"

        text = f'Urči slovní druh slova „{target}“ ve větě: „{sentence}“'
        return {
            "text": text,
            "options": ["a) podstatné jméno", "b) sloveso", "c) přídavné jméno"],
            "correct_option": corr
        }

    out = [make_item() for _ in range(n)]
    random.shuffle(out)
    return out

import random

def cjl_pool_5_members_json():
    rounds = cjl_tasks_by_level.get("5. třída", {}).get("rounds", [])
    pool = []
    for rnd in rounds:
        for t in rnd:
            if not isinstance(t, dict): 
                continue
            opts = " ".join(t.get("options", [])).lower()
            # bereme úlohy na větné členy (podmět/přísudek/předmět/PU/přívlastek…)
            if any(k in opts for k in ["podmět","přísudek","předmět","pu","přívlastek","nepřímý předmět"]):
                pool.append(t)
    random.shuffle(pool)
    return pool

def cjl_gen_5_pos_all(n: int = 30):
    import random
    bank = {
        "podstatné jméno": ["hrad","princ","město","královna","strom","vojáci"],
        "přídavné jméno": ["rychlý","zlatý","tichá","malý","krásná","mocný"],
        "sloveso": ["běží","spí","pracuje","četl","přišli","píše"],
        "příslovce": ["hned","dnes","tiše","rychle","včera","ráno"],
        "číslovka": ["sedm","třetí","pár","mnoho","oba","desátý"],
        "zájmeno": ["já","ty","on","jeho","někdo","toto"],
        "předložka": ["bez","na","k","u","o","s"],
        "spojka": ["a","ale","nebo","protože","aby","když"],
        "částice": ["prý","ať","nechť","kéž","jen","třeba"],
        "citoslovce": ["ach","jé","fuj","hurá","pst","bum"],
    }
    labels = list(bank.keys())

    def one_item():
        correct = random.choice(labels)
        word = random.choice(bank[correct])
        wrongs = random.sample([l for l in labels if l != correct], 2)
        options = [f"a) {correct}", f"b) {wrongs[0]}", f"c) {wrongs[1]}"]
        # pro trochu variace promícháme pořadí
        import itertools
        order = ["a","b","c"]
        random.shuffle(order)
        mapping = dict(zip(order, [opt.split(") ",1)[1] for opt in options]))
        opts_shuffled = [f"{o}) {mapping[o]}" for o in ["a","b","c"]]
        correct_letter = [k for k,v in mapping.items() if v == correct][0]
        return {
            "text": f"Urči slovní druh: „{word}“",
            "options": opts_shuffled,
            "correct_option": correct_letter
        }

    out = [one_item() for _ in range(n)]
    random.shuffle(out)
    return out

def cjl_gen_5_members_spp(n: int = 24):
    import random
    subs = ["Sněhurka","princ","královna","myslivec","Karkulka","trpaslíci"]
    verbs = ["spí","čte","běží","pracuje","vaří","zpívá","čeká"]
    adjs_m = ["statečný","zlatý","rychlý","tichý"]
    adjs_f = ["krásná","unavená","mocná","červená"]

    def one():
        which = random.choice(["S","P","A"])
        subj = random.choice(subs)
        if which == "S":
            sent = f"{random.choice(adjs_f if subj.endswith('a') else adjs_m)} {subj} {random.choice(verbs)}."
            target = subj; corr = "a"  # podmět
        elif which == "P":
            sent = f"{subj} {random.choice(verbs)}."
            target = sent.split()[-1].rstrip("."); corr = "b"  # přísudek
        else:  # A – přívlastek (přídavné jméno u podmětu)
            adj = random.choice(adjs_f if subj.endswith('a') else adjs_m)
            sent = f"{adj} {subj} {random.choice(verbs)}."
            target = adj; corr = "c"  # přívlastek
        return {
            "text": f'Urči větný člen slova „{target}“ ve větě: „{sent}“',
            "options": ["a) podmět","b) přísudek","c) přívlastek"],
            "correct_option": corr
        }

    out = [one() for _ in range(n)]
    random.shuffle(out)
    return out

def cjl_gen_5_agreement(n: int = 24):
    import random
    masc_anim = ["chlapci","kluci","psi","rytíři","vojáci","tatínkové"]  # → -i
    fem_pl = ["dívky","ženy","maminky","sovy","kočky","princezny"]       # → -y
    stems = ["přišl","běžel","seděl","pracoval","hráli"[:-1], "psal" , "četl"]  # vytvoříme 'přišl__', 'běžel__', …

    # drobná úprava kmenů na '…l__'
    def to_blank(stem):
        if stem.endswith("l"): return stem + "__"
        if stem.endswith("al"): return stem[:-1] + "__"
        if stem.endswith("el"): return stem[:-1] + "__"
        return stem + "__"

    def one():
        if random.random() < 0.5:
            subj = random.choice(masc_anim); corr = "a"; mark = "i"
        else:
            subj = random.choice(fem_pl); corr = "b"; mark = "y"
        base = to_blank(random.choice(["přišl","běžel","seděl","pracoval","hrál","psal","četl"]))
        return {
            "text": f'Shoda podmětu s přísudkem – doplň **i/y**: „{subj} {base}.“',
            "options": ["a) i","b) y","c) —"],
            "correct_option": corr
        }

    out = [one() for _ in range(n)]
    random.shuffle(out)
    return out

import random

# (1) Rod + životnost
def cjl_gen_6_gender_animacy(n: int = 24):
    masc_anim = ["král","princ","rytiř","voják","pes","vlk","chlapec","pán"]
    masc_inan = ["hrad","strom","stůl","zámek","kámen","hřebík","vagon","most"]
    fem       = ["žena","židle","kost","píseň","růže","dívka","učitelka","ulice"]
    neut      = ["město","moře","kuře","stavení","slunce","okno","kolo","vejce"]

    def one():
        which = random.choice(["ma","mi","f","n"])
        if which == "ma":
            w, corr = random.choice(masc_anim), "a"; opts = ["a) mužský životný","b) mužský neživotný","c) střední"]
        elif which == "mi":
            w, corr = random.choice(masc_inan), "b"; opts = ["a) mužský životný","b) mužský neživotný","c) střední"]
        elif which == "f":
            w, corr = random.choice(fem), "b"; opts = ["a) mužský","b) ženský","c) střední"]
        else:
            w, corr = random.choice(neut), "c"; opts = ["a) mužský","b) ženský","c) střední"]
        return {"text": f"Urči rod/životnost: „{w}“",
                "options": opts,
                "correct_option": corr}
    out = [one() for _ in range(n)]
    random.shuffle(out)
    return out

# (2) Vzor (m/ž/s)
def cjl_gen_6_patterns(n: int = 24):
    bank = {
        "pán": ["pán","soused","hráč","hasič"],
        "hrad": ["hrad","strom","stůl","zámek"],
        "muž": ["muž","kapr","medvěd","host"],
        "stroj": ["stroj","čaj","kraj","kočár"],
        "žena": ["žena","dívka","lampa","škola"],
        "růže": ["růže","ulice","židle","louže"],
        "píseň": ["píseň","podešev","pomoc","moucha?"][:3],   # držíme konzistentně 3
        "kost": ["kost","radost","část","zeď"],
        "město": ["město","jablko","okno","srdce"],
        "moře": ["moře","pole","náměstí","rybníce?"][:3],
        "kuře": ["kuře","tele","sele"],
        "stavení": ["stavení","dříví","nářadí"],
    }
    # map word -> správný vzor
    mapping = {}
    for vzor, words in bank.items():
        for w in words:
            mapping[w] = vzor

    all_words = list(mapping.keys())
    vzory = list(bank.keys())

    def one():
        w = random.choice(all_words)
        correct = mapping[w]
        wrongs = random.sample([v for v in vzory if v != correct], 2)
        options = [f"a) {correct}", f"b) {wrongs[0]}", f"c) {wrongs[1]}"]
        # promíchání pořadí tak, a/b/c sedí na UI
        order = ["a","b","c"]; random.shuffle(order)
        labels = dict(zip(order, [opt.split(") ",1)[1] for opt in options]))
        opts = [f"{o}) {labels[o]}" for o in ["a","b","c"]]
        corr = [k for k,v in labels.items() if v == correct][0]
        return {"text": f"Urči vzor pro „{w}“.", "options": opts, "correct_option": corr}

    out = [one() for _ in range(n)]
    random.shuffle(out)
    return out

# (3) Sloveso: osoba/číslo/čas/způsob
def cjl_gen_6_verbs_morph(n: int = 24):
    persons = [
        ("jdu","1. os. j. č."), ("jdeš","2. os. j. č."), ("jde","3. os. j. č."),
        ("jdeme","1. os. mn. č."), ("jdete","2. os. mn. č."), ("jdou","3. os. mn. č.")
    ]
    tenses = [("šel","minulý"), ("čtu","přítomný"), ("půjdu","budoucí")]
    moods  = [("piš!","rozkazovací"), ("psal bych","podmiňovací"), ("píšu","oznamovací")]

    def one():
        which = random.choice(["pers","tense","mood"])
        if which == "pers":
            w, correct = random.choice(persons)
            options = ["a) 1. os. j. č.","b) 1. os. mn. č.","c) 3. os. mn. č."]
            corr = {"1. os. j. č.":"a","1. os. mn. č.":"b","3. os. mn. č.":"c"}[correct]
            text = f"Urči osobu a číslo: „{w}“."
        elif which == "tense":
            w, correct = random.choice(tenses)
            options = ["a) minulý","b) přítomný","c) budoucí"]
            corr = {"minulý":"a","přítomný":"b","budoucí":"c"}[correct]
            text = f"Urči čas slovesa: „{w}“."
        else:
            w, correct = random.choice(moods)
            options = ["a) oznamovací","b) rozkazovací","c) podmiňovací"]
            corr = {"oznamovací":"a","rozkazovací":"b","podmiňovací":"c"}[correct]
            text = f"Urči způsob slovesa: „{w}“."
        return {"text": text, "options": options, "correct_option": corr}

    out = [one() for _ in range(n)]
    random.shuffle(out)
    return out

import random

# (1) Slovotvorba: kořen / předpony / přípony (mytologii použijeme v jiných tématech)
def cjl_gen_7_wordformation(n: int = 24):
    samples = [
        {"word":"nepřátelský", "prefix":"ne",   "root":"přátel", "suffix":"-ský"},
        {"word":"předmluva",   "prefix":"před", "root":"mluv",   "suffix":"-a"},
        {"word":"přehrada",    "prefix":"pře",  "root":"hrad",   "suffix":"-a"},
        {"word":"doletět",     "prefix":"do",   "root":"let",    "suffix":"-ět"},
        {"word":"kreslířka",   "prefix":"—",    "root":"kresl",  "suffix":"-ířka"},
        {"word":"mladík",      "prefix":"—",    "root":"mlad",   "suffix":"-ík"},
        {"word":"neviditelný", "prefix":"ne",   "root":"vid",    "suffix":"-itelný"},
        {"word":"předložka",   "prefix":"před", "root":"lož",    "suffix":"-ka"},
        {"word":"vytisknout",  "prefix":"vy",   "root":"tisk",   "suffix":"-nout"},
    ]
    prefixes = ["ne","pře","vy","do","na","před","z","po","—"]
    suffixes = ["-ný","-ský","-ka","-ek","-ost","-ík","-ota","-ení","-nout","-ět","-itel","-ířka","-itelný"]
    roots    = list({s["root"] for s in samples})

    def ask_prefix(s):
        correct = s["prefix"]
        if correct == "—":
            opts = ["a) ne-","b) vy-","c) žádná (bez předpony)"]; corr = "c"
        else:
            wrongs = [p for p in prefixes if p not in [correct,"—"]]
            o1, o2 = random.sample(wrongs, 2)
            opts = [f"a) {correct}-", f"b) {o1}-", f"c) {o2}-"]; corr = "a"
        return {
            "text": f"Urči **předponu** ve slově „{s['word']}“.",
            "options": opts, "correct_option": corr
        }

    def ask_suffix(s):
        correct = s["suffix"]
        wrongs = random.sample([x for x in suffixes if x != correct], 2)
        opts = [f"a) {correct}", f"b) {wrongs[0]}", f"c) {wrongs[1]}"]
        return {
            "text": f"Urči **příponu** ve slově „{s['word']}“.",
            "options": opts, "correct_option": "a"
        }

    def ask_root(s):
        correct = s["root"]
        wrongs = random.sample([r for r in roots if r != correct], 2)
        opts = [f"a) {correct}", f"b) {wrongs[0]}", f"c) {wrongs[1]}"]
        return {
            "text": f"Urči **kořen** slova „{s['word']}“.",
            "options": opts, "correct_option": "a"
        }

    makers = [ask_prefix, ask_suffix, ask_root]
    out = [random.choice(makers)(random.choice(samples)) for _ in range(n)]
    random.shuffle(out); return out

# (2) Slova přejatá (řecké / latinské / jiné)
def cjl_gen_7_loanwords(n: int = 24):
    greek = ["demokracie","fyzika","filozofie","geografie","telefon","syntéza","analýza","hypotéza"]
    latin = ["maximum","minimum","centrum","univerzita","kultura","kolonie","forma","radius"]
    other = ["špagety","džus","čokoláda","robot","tango","kakao","golf","tramvaj"]
    all_pairs = [(w,"řecké") for w in greek] + [(w,"latinské") for w in latin] + [(w,"jiné") for w in other]
    def one():
        w, origin = random.choice(all_pairs)
        opts = ["a) řecké","b) latinské","c) jiné"]
        corr = {"řecké":"a","latinské":"b","jiné":"c"}[origin]
        return {"text": f"Urči původ slova „{w}“.","options": opts,"correct_option": corr}
    return [one() for _ in range(n)]

# (3) Sloveso: kategorie + vzory
def cjl_gen_7_verbs(n: int = 30):
    persons = [
        ("jdu","1. os. j. č."), ("jdeš","2. os. j. č."), ("jde","3. os. j. č."),
        ("jdeme","1. os. mn. č."), ("jdete","2. os. mn. č."), ("jdou","3. os. mn. č.")
    ]
    tenses = [("nesl","minulý"), ("nese","přítomný"), ("ponese","budoucí")]
    moods  = [("nes!","rozkazovací"), ("nesl bych","podmiňovací"), ("nesu","oznamovací")]
    aspects = [("psát","nedokonavý"),("napsat","dokonavý"),("číst","nedokonavý"),("přečíst","dokonavý"),
               ("dělat","nedokonavý"),("udělat","dokonavý")]
    voices  = [("Perseus porazil netvora.","činný"), ("Netvor byl poražen Persem.","trpný"), ("Athéna se usmála.","činný")]
    reflex  = [("smát se","zvratné"),("bát se","zvratné"),("vrátit se","zvratné"),("jít","nezvratné")]
    # slovesné vzory (infinitiv -> vzor)
    vzor_of = {"nést":"nese","brát":"bere","mazat":"maže","péct":"peče","umřít":"umře","sázet":"sází","prosit":"prosí","trpět":"trpí","tisknout":"tiskne","krýt":"kryje"}
    vzory = list(set(vzor_of.values()))

    def q_person():
        w, lab = random.choice(persons)
        mapping = {"1. os. j. č.":"a","1. os. mn. č.":"b","3. os. mn. č.":"c"}
        return {"text": f"Urči osobu a číslo: „{w}“.","options":["a) 1. os. j. č.","b) 1. os. mn. č.","c) 3. os. mn. č."],"correct_option": mapping.get(lab,"c")}
    def q_tense():
        w, lab = random.choice(tenses)
        return {"text": f"Urči čas slovesa: „{w}“.","options":["a) minulý","b) přítomný","c) budoucí"],"correct_option":{"minulý":"a","přítomný":"b","budoucí":"c"}[lab]}
    def q_mood():
        w, lab = random.choice(moods)
        return {"text": f"Urči způsob slovesa: „{w}“.","options":["a) oznamovací","b) rozkazovací","c) podmiňovací"],"correct_option":{"oznamovací":"a","rozkazovací":"b","podmiňovací":"c"}[lab]}
    def q_aspect():
        w, lab = random.choice(aspects)
        return {"text": f"Urči vid slovesa: „{w}“.","options":["a) dokonavý","b) nedokonavý","c) —"],"correct_option":"a" if lab=="dokonavý" else "b"}
    def q_voice():
        w, lab = random.choice(voices)
        return {"text": f"Urči slovesný rod (věta: „{w}“).","options":["a) činný","b) trpný","c) zvratný"],"correct_option":{"činný":"a","trpný":"b","zvratný":"c"}[lab]}
    def q_reflex():
        w, lab = random.choice(reflex)
        return {"text": f"Je sloveso „{w}“ zvratné?","options":["a) zvratné","b) nezvratné","c) —"],"correct_option":"a" if lab=="zvratné" else "b"}
    def q_pattern():
        inf, vz = random.choice(list(vzor_of.items()))
        wrongs = random.sample([v for v in vzory if v != vz], 2)
        return {"text": f"Urči slovesný vzor pro infinitiv „{inf}“.","options":[f"a) {vz}", f"b) {wrongs[0]}", f"c) {wrongs[1]}"],"correct_option":"a"}

    makers = [q_person,q_tense,q_mood,q_aspect,q_voice,q_reflex,q_pattern]
    out = [random.choice(makers)() for _ in range(n)]
    random.shuffle(out); return out

# (4) Ostatní větné členy (předmět / přísl. určení / doplněk) – mytologické věty
def cjl_gen_7_members_other(n: int = 24):
    subs = ["Perseus","Odysseus","Athéna","Héraklés","Theseus"]
    verbs= ["nesl","porazil","hledal","čekal","odplouval","mluvil","se vrátil"]
    places=["do Athén","do Tróje","k moři","na horu","domů","na ostrov"]
    times = ["v noci","ráno","večer","po boji","po cestě"]

    def one():
        which = random.choice(["obj","adv","comp"])
        s = random.choice(subs)
        if which=="obj":
            sent = f"{s} nesl hlavu Medúzy."
            target = "hlavu Medúzy"; corr="a"   # předmět
        elif which=="adv":
            sent = f"{s} cestoval {random.choice(times)}."
            target = sent.split()[-1].rstrip("."); corr="b"  # přísl. určení (času)
        else:
            sent = f"{s} se vrátil unavený."
            target = "unavený"; corr="c"        # doplněk
        return {
            "text": f'Urči větný člen výrazu „{target}“ ve větě: „{sent}“',
            "options": ["a) předmět","b) příslovečné určení","c) doplněk"],
            "correct_option": corr
        }

    return [one() for _ in range(n)]

# (5) Skladba – věta hlavní × vedlejší (mytologické věty)
def cjl_gen_7_main_sub(n: int = 24):
    mains = [("Perseus letěl a Athéna mu radila.","Perseus letěl","hlavní"),
             ("Odysseus bojoval, ale neustoupil.","Odysseus bojoval","hlavní")]
    subs  = [("Perseus věděl, že Medúsa je nebezpečná.","že Medúsa je nebezpečná","vedlejší"),
             ("Odysseus se zastavil, protože se blížila bouře.","protože se blížila bouře","vedlejší"),
             ("Kdo překoná zkoušku, zvítězí.","Kdo překoná zkoušku","vedlejší")]
    pairs = mains + subs

    def one():
        s, part, typ = random.choice(pairs)
        opts = ["a) věta hlavní","b) věta vedlejší","c) jednoduchá věta"]
        corr = "a" if typ=="hlavní" else "b"
        return {"text": f'Ve větě „{s}“ je část „{part}“:','options': opts,'correct_option': corr}
    return [one() for _ in range(n)]

# (6) Poměry + typ souvětí (mytologické věty)
def cjl_gen_7_relations(n: int = 24):
    # A) poměr mezi větami
    conj = [("Perseus běžel a Athéna radila.","spojovací"),
            ("Perseus zaváhal, ale Athéna ho vedla.","odporovací"),
            ("Perseus uspěje, nebo padne.","vylučovací")]
    # B) typ souvětí
    types= [("Perseus letěl a Athéna radila.","souřadné"),
            ("Perseus věděl, že se vrátí.","podřadné"),
            ("Perseus letí.","jednoduchá")]

    def one():
        if random.random()<0.5:
            s, lab = random.choice(conj)
            opts=["a) spojovací","b) vylučovací","c) odporovací"]
            corr={"spojovací":"a","vylučovací":"b","odporovací":"c"}[lab]
            return {"text": f"Urči **poměr** mezi větami: „{s}“","options":opts,"correct_option":corr}
        else:
            s, lab = random.choice(types)
            opts=["a) souvětí souřadné","b) souvětí podřadné","c) jednoduchá věta"]
            corr={"souřadné":"a","podřadné":"b","jednoduchá":"c"}[lab]
            return {"text": f"Urči **typ**: „{s}“","options":opts,"correct_option":corr}

    return [one() for _ in range(n)]

# ---------- ČJ 8. třída: generátory ----------

def _myth_sentences():
    # základní zásobník vět pro skladební jevy
    return [
        "Zeus vládl na Olympu.",
        "Héra žárlila na smrtelné ženy.",
        "Odysseus se po válce vracel domů.",
        "Prométheus přinesl lidem oheň.",
        "Persefona se každé jaro vrací z podsvětí.",
        "Athéna ochraňovala hrdiny a města.",
        "Héraklés splnil dvanáct úkolů.",
        "Apollón vedl múzy k písni a tanci.",
        "Artemis střežila lesy a zvěř.",
        "Theseus porazil Minótaura v labyrintu."
    ]

def cjl_gen_8_sentence_members(n=32):
    """Určování větných členů (podmět, přísudek, předmět/přívlastek/PU).
       V otázce vyznačíme cílové slovo uvozovkami.
    """
    import random
    sentences = _myth_sentences()
    roles = [
        ("podmět", "a"),
        ("přísudek", "b"),
        ("předmět", "c"),
    ]
    # pomocné extrakce pro jednoduché věty
    def split_simple(s):
        # velmi jednoduché dělení: [Subj] [Verb] [rest]
        parts = s.rstrip(".").split()
        if len(parts) < 2: return parts[0], parts[1] if len(parts)>1 else "", ""
        subj = parts[0]
        verb = parts[1]
        rest = " ".join(parts[2:])
        return subj, verb, rest

    out = []
    while len(out) < n:
        s = random.choice(sentences)
        subj, verb, rest = split_simple(s)
        # vyber náhodně, co budeme určovat
        choice = random.choice(["S","V","O"])
        if choice == "S" and subj:
            target = subj
            opts = ["a) podmět","b) přísudek","c) předmět"]
            corr = "a"
        elif choice == "V" and verb:
            target = verb.rstrip(",")
            opts = ["a) podmět","b) přísudek","c) předmět"]
            corr = "b"
        else:
            # vezmeme první podstatné jméno z 'rest' jako pseudo-předmět
            cand = [w.strip(",") for w in rest.split() if w and w[0].isalpha()]
            if not cand: continue
            target = cand[0]
            opts = ["a) podmět","b) přísudek","c) předmět"]
            corr = "c"

        text = f"Urči větný člen slova „{target}“ ve větě: „{s}“"
        out.append({"text": text, "options": opts, "correct_option": corr})
    random.shuffle(out)
    return out

def cjl_gen_8_main_vs_sub(n=28):
    """Urči, zda zvýrazněná část (v uvozovkách) je věta hlavní (VH) nebo vedlejší (VV)."""
    import random
    templates = [
        ('Řekl, že se vrátí.',             'že se vrátí',        "b"),  # VV
        ('Když Persefona odejde, smutní příroda.', 'Když Persefona odejde', "b"),
        ('Odysseus věděl, že domů povede dlouhá cesta.', 'že domů povede dlouhá cesta', "b"),
        ('Héraklés splnil úkoly a pokračoval dál.', 'Héraklés splnil úkoly', "a"), # VH
        ('Zeus přikázal, aby lidé zachovali pořádek.', 'aby lidé zachovali pořádek', "b"),
        ('Athéna poradila hrdinovi a ten uspěl.', 'ten uspěl', "a"),
        ('Ačkoli pršelo, Apollón zpíval.', 'Ačkoli pršelo', "b"),
        ('Theseus našel cestu a vyšel z labyrintu.', 'Theseus našel cestu', "a"),
    ]
    out=[]
    while len(out)<n:
        s, frag, corr = random.choice(templates)
        out.append({
            "text": f"Urči, zda část „{frag}“ ve větě: „{s}“ je…",
            "options": ["a) věta hlavní (VH)", "b) věta vedlejší (VV)", "c) nevětný výraz"],
            "correct_option": corr
        })
    random.shuffle(out)
    return out

def cjl_gen_8_subordinate_types(n=28):
    """Druhy vedlejších vět – 3 možnosti (příčinná/časová/účelová/…).
       Zaměřeno na nejběžnější typy.
    """
    import random
    bank = [
        ("Vím, že se vrátíš.",                 "VV předmětná",   ["VV podmětná","VV předmětná","VV přívlastková"], "b"),
        ("Kdo přišel, uvidí Athénu.",         "VV podmětná",    ["VV podmětná","VV časová","VV příčinná"],       "a"),
        ("Uviděl chrám, který chránila Athéna.","VV přívlastková",["VV přísudková","VV přívlastková","VV účelová"],"b"),
        ("Zůstali, protože pršelo.",           "VV příčinná",    ["VV příčinná","VV časová","VV podmínková"],     "a"),
        ("Přišli, když se setmělo.",           "VV časová",      ["VV časová","VV účelová","VV přípustková"],     "a"),
        ("Učinil to, aby uspěl.",              "VV účelová",     ["VV účelová","VV podmínková","VV příčinná"],     "a"),
        ("Půjdeme, jestli přestane pršet.",    "VV podmínková",  ["VV přípustková","VV podmínková","VV časová"],  "b"),
        ("Šel, ačkoli byl unaven.",            "VV přípustková", ["VV účelová","VV časová","VV přípustková"],     "c"),
    ]
    out=[]
    while len(out)<n:
        s, label, opts, corr = random.choice(bank)
        out.append({
            "text": f"Urči druh vedlejší věty ve větě: „{s}“",
            "options": [f"a) {opts[0]}", f"b) {opts[1]}", f"c) {opts[2]}"],
            "correct_option": corr
        })
    random.shuffle(out)
    return out

def cjl_gen_8_commas(n=24):
    """Psaní čárek v souvětích."""
    import random
    bank = [
        ("Vím že to zvládneš.",                "Vím, že to zvládneš."),
        ("Když Persefona odejde smutní příroda.","Když Persefona odejde, smutní příroda."),
        ("Řekl že přijde.",                    "Řekl, že přijde."),
        ("Ačkoli pršelo hrdina pokračoval.",   "Ačkoli pršelo, hrdina pokračoval."),
        ("Zůstal protože chtěl pomoci.",       "Zůstal, protože chtěl pomoci."),
        ("Athéna poradila hrdinovi a ten uspěl.", "Athéna poradila hrdinovi a ten uspěl."),  # bez čárky
    ]
    out=[]
    while len(out)<n:
        wrong, correct = random.choice(bank)
        # nabídneme správnou, „zbytečnou čárku“, a původní
        zbytecna = correct.replace(",", "") + ("," if "," not in correct else "")
        options = [f"a) {correct}", f"b) {wrong}", f"c) {zbytecna}"]
        corr = "a"
        out.append({
            "text": f"Doplň čárku: „{wrong}“",
            "options": options,
            "correct_option": corr
        })
    random.shuffle(out)
    return out

def cjl_pool_8_mix_from_json():
    """Mix pro 8. třídu: primárně JSON pro 8. ročník; fallback = 8 + 7 + 6."""
    import random
    flat8 = _cjl_flatten_rounds("8. třída")
    pool = [t for t in flat8 if isinstance(t, dict)]

    # Fallback: pokud by náhodou 8. třída v JSONu chyběla/ byla prázdná,
    # doplň z 7. a 6. třídy (ať je co procvičovat).
    if not pool:
        flat7 = _cjl_flatten_rounds("7. třída")
        flat6 = _cjl_flatten_rounds("6. třída")
        pool = [t for t in (flat8 + flat7 + flat6) if isinstance(t, dict)]

    random.shuffle(pool)
    return pool

import random

# 9/1 Literární druhy a žánry
def cjl_gen_9_lit_forms_genres(n: int = 28):
    druhy = [("lyrika","druh"),("epika","druh"),("drama","druh")]
    zanry = [("balada","žánr"),("epos","žánr"),("pohádka","žánr"),
             ("povídka","žánr"),("novela","žánr"),("román","žánr"),
             ("komedie","žánr"),("tragédie","žánr")]
    all_items = druhy + zanry

    def one():
        w, typ = random.choice(all_items)
        if typ == "druh":
            opts = ["a) literární druh","b) literární žánr","c) jazykový prostředek"]; corr = "a"
            text = f"Urči: „{w}“ je…"
        else:
            opts = ["a) literární druh","b) literární žánr","c) jazykový prostředek"]; corr = "b"
            text = f"Urči: „{w}“ je…"
        return {"text": text, "options": opts, "correct_option": corr}

    return [one() for _ in range(n)]

# 9/2 Slohové postupy (mytologické mini-věty)
def cjl_gen_9_styles(n: int = 28):
    vypr = ["Perseus vypráví, jak porazil netvora.", "Odysseus popisuje svou cestu domů v jednotlivých epizodách."]
    pop  = ["Chrám má vysoké sloupy a mramorovou předsíň.", "Athénin štít je kruhový, s bohatou výzdobou."]
    vykl = ["Epos je rozsáhlý epický žánr s hrdinským námětem.", "Tragédie je dramatický žánr s vážným konfliktem."]
    bank = [(s,"vyprávěcí") for s in vypr] + [(s,"popisný") for s in pop] + [(s,"výkladový") for s in vykl]

    def one():
        s, kind = random.choice(bank)
        opts = ["a) vyprávěcí","b) popisný","c) výkladový"]
        corr = {"vyprávěcí":"a","popisný":"b","výkladový":"c"}[kind]
        return {"text": f"Urči **slohový postup**: „{s}“", "options": opts, "correct_option": corr}

    return [one() for _ in range(n)]

# 9/3 Figury a tropy (mytologické příklady)
def cjl_gen_9_figures_tropes(n: int = 30):
    tropy = [
        ("Moře se zasmálo.", "personifikace"),
        ("Hrdina je lev.", "metafora"),
        ("Pětkrát jsem to říkal!", "hyperbola"),
        ("Vypil jsem sklenici.", "metonymie"),  # místo „obsahu sklenice“
    ]
    figury = [
        ("A hrdina běží, a volá, a doufá…", "anafora"),
        ("Přišel, viděl, zvítězil.", "enumerace"),
        ("Do boje kráčí Perseus.", "inverze"),
        ("Běž, běž!", "epizeuxis"),
    ]
    allq = tropy + figury

    def one():
        s, lab = random.choice(allq)
        opts = ["a) metafora/personifikace/metonymie (trop)","b) řečnická figura (anafora/epizeuxis/inverze…)","c) slohový postup"]
        corr = "a" if lab in {"personifikace","metafora","hyperbola","metonymie"} else "b"
        return {"text": f"Urči: „{s}“ je…", "options": opts, "correct_option": corr}

    return [one() for _ in range(n)]

# 9/4 Synonyma × antonyma × homonyma
def cjl_gen_9_sah(n: int = 28):
    syn = [("zámek (stavba) — palác","synonyma"),("velký — obrovský","synonyma")]
    ant = [("den — noc","antonyma"),("vysoký — nízký","antonyma")]
    hom = [("koruna (stromu) — koruna (měna)","homonyma"),("zámek (u dveří) — zámek (stavba)","homonyma")]
    bank = syn + ant + hom

    def one():
        pair, kind = random.choice(bank)
        opts = ["a) synonyma","b) antonyma","c) homonyma"]
        corr = {"synonyma":"a","antonyma":"b","homonyma":"c"}[kind]
        return {"text": f"Urči vztah: {pair}", "options": opts, "correct_option": corr}

    return [one() for _ in range(n)]

# 9/5 Mix 9. třídy z JSONu
def cjl_pool_9_mix_from_json():
    flat9 = _cjl_flatten_rounds("9. třída")
    pool = [t for t in flat9 if isinstance(t, dict)]
    random.shuffle(pool)
    return pool

# 9/6 Celkové opakování – všechna kola ze souboru JSON (1.–9.)
def cjl_pool_all_json_mix():
    pool = []
    for lvl, payload in (cjl_tasks_by_level or {}).items():
        rounds = payload.get("rounds", [])
        for rnd in rounds:
            for t in rnd:
                if isinstance(t, dict):
                    pool.append(t)
    random.shuffle(pool)
    return pool

def cjl_gen_9_lit_from_mini(n: int = 18):
    import random
    items = _lit_items_normalized()
    if len(items) < 3:
        return []
    sample = random.sample(items, min(n, len(items)))
    out = []
    for it in sample:
        correct = it["term"]
        others  = [x["term"] for x in items if x is not it]
        wrongs  = random.sample(others, 2)
        opts = [correct, wrongs[0], wrongs[1]]
        random.shuffle(opts)
        corr_letter = "abc"[opts.index(correct)]
        out.append({
            "text": f'Vyber správný název k definici: „{it["note"]}“',
            "options": [f"a) {opts[0]}", f"b) {opts[1]}", f"c) {opts[2]}"],
            "correct_option": corr_letter
        })
    return out

def cjl_gen_9_fig_from_mini(n: int = 18):
    import random
    items = _fig_items_normalized()
    if len(items) < 3:
        return []
    sample = random.sample(items, min(n, len(items)))
    out = []
    for it in sample:
        correct = it["term"]
        others  = [x["term"] for x in items if x is not it]
        wrongs  = random.sample(others, 2)
        opts = [correct, wrongs[0], wrongs[1]]
        random.shuffle(opts)
        corr_letter = "abc"[opts.index(correct)]
        out.append({
            "text": f'Poznej pojem podle charakteristiky: „{it["note"]}“',
            "options": [f"a) {opts[0]}", f"b) {opts[1]}", f"c) {opts[2]}"],
            "correct_option": corr_letter
        })
    return out


# --- 9. třída: sjednocení mini-anotací na {'term','note'} ---
def _lit_items_normalized():
    """Vrátí LIT_MINI jako [{'term','note'}, ...] bez ohledu na původní klíče."""
    try:
        items = LIT_MINI
    except NameError:
        return []
    out = []
    for it in items:
        term = it.get("term") or it.get("spravna_odpoved")
        note = it.get("note") or it.get("anotace")
        if term and note:
            out.append({"term": term, "note": note})
    return out

def _fig_items_normalized():
    """Vrátí FIG_TROP_MINI / FIG_MINI jako [{'term','note'}, ...]."""
    items = []
    for name in ("FIG_TROP_MINI", "FIG_MINI"):  # podpora obou názvů
        try:
            items = globals()[name]
            break
        except KeyError:
            continue
    if not items:
        return []
    out = []
    for it in items:
        term = it.get("term") or it.get("spravna_odpoved")
        # zkombinuj vysvětlení + případnou ukázku do jedné 'note'
        if "note" in it:
            note = it["note"]
        else:
            expl = it.get("vysvetleni", "")
            ex = it.get("ukazka", "")
            note = (expl or "") + (f" — Ukázka: {ex}" if ex else "")
        if term and note:
            out.append({"term": term, "note": note})
    return out

# ---------- ČJ: master-pool podle tématu ----------
def build_cjl_pool(level: str, confirmed_topic: str):
    # 1. třída
    if level == "1. třída":
        if confirmed_topic == "Doplň písmeno":
            return cjl_pool_from_json(level, "Doplň písmeno")
        if confirmed_topic == "Spočítej slabiky":
            return cjl_pool_from_json(level, "Kolik slabik má slovo")
        if confirmed_topic == "Vyber správnou slabiku (nejjednodušší slova)":
            return cjl_gen_pick_syllable_easy()
        if confirmed_topic == "Tvrdé a měkké čtení po d, t, n":
            return cjl_gen_soft_hard_dtn()

    # 2. třída
    if level == "2. třída":
        # Vyžaduje mít definované cjl_pool_2_y_hard() a cjl_pool_2_i_soft()
        if confirmed_topic.startswith("Doplň y/ý"):
            return cjl_pool_2_y_hard()
        if confirmed_topic.startswith("Doplň i/í"):
            return cjl_pool_2_i_soft()

    # 3. třída – vyjmenovaná slova po B, L, M, P, S, V, Z + mix
    if level == "3. třída":
        order = [
            "Vyjmenovaná slova po B",
            "Vyjmenovaná slova po L",
            "Vyjmenovaná slova po M",
            "Vyjmenovaná slova po P",
            "Vyjmenovaná slova po S",
            "Vyjmenovaná slova po V",
            "Vyjmenovaná slova po Z",
        ]
        rounds = cjl_tasks_by_level.get(level, {}).get("rounds", [])
        if confirmed_topic in order:
            idx = order.index(confirmed_topic)
            if 0 <= idx < len(rounds) and isinstance(rounds[idx], list):
                return [t for t in rounds[idx] if isinstance(t, dict)]
            return []
        if "dohromady" in confirmed_topic.lower():
            return _cjl_flatten_rounds(level)
    
    if level == "4. třída":
        topic = confirmed_topic.lower().replace("–","-")
        if topic == "slovní druhy - mix":
            return _cjl_flatten_rounds(level)
        if topic.startswith("určování pádu"):
            # bereš úlohy z JSONu podle prefixu textu:
            return cjl_pool_from_json(level, "Urči pád podstatného jména")
        if topic.startswith("slovní druhy ve větě"):
            return cjl_gen_4_pos_sentence_v2()  # viz níže

    if level == "5. třída":
        t = confirmed_topic.lower()
        if t.startswith("určování základních větných členů:"):
            return cjl_gen_5_members_spp()
        if t == "určování základních větných členů":
            return cjl_pool_5_members_json()     # z JSONu (už hotovo)
        if t == "slovní druhy":
            return cjl_gen_5_pos_all()
        if t.startswith("shoda podmětu s přísudkem"):
            return cjl_gen_5_agreement()
        
    if level == "6. třída":
        t = confirmed_topic.lower()
        if t.startswith("rod a životnost"):
            return cjl_gen_6_gender_animacy()
        if t.startswith("vzor podstatného"):
            return cjl_gen_6_patterns()
        if t.startswith("sloveso: osoba"):
            return cjl_gen_6_verbs_morph()
        if t.startswith("souhrn – mix"):
            # Mix z JSONu (stávající kolo) + případně doplňkové položky, pokud JSON ještě nemáš rozšířený
            # Fallback
            return _cjl_flatten_rounds(level)
        
    if level == "7. třída":
        t = confirmed_topic.lower()
        if t.startswith("slovotvorba"):
            return cjl_gen_7_wordformation()
        if t.startswith("slova přejatá"):
            return cjl_gen_7_loanwords()
        if t.startswith("sloveso:"):
            return cjl_gen_7_verbs()
        if t.startswith("ostatní větné členy"):
            return cjl_gen_7_members_other()
        if t.startswith("skladba –") or t.startswith("skladba -"):
            return cjl_gen_7_main_sub()
        if t.startswith("poměry"):
            return cjl_gen_7_relations()
        if t.startswith("souhrn – mix"):
            return _cjl_flatten_rounds(level)  # bere existující JSON pro 7. třídu

        
    # 8. třída
    if level == "8. třída":
        t = confirmed_topic.lower()
        if t.startswith("určování větných členů"):
            return cjl_gen_8_sentence_members()
        if t.startswith("věta hlavní × věta vedlejší"):
            return cjl_gen_8_main_vs_sub()
        if t.startswith("druhy vedlejších vět"):
            return cjl_gen_8_subordinate_types()
        if t.startswith("psaní čárek"):
            return cjl_gen_8_commas()
        if "mix" in t:
            return cjl_pool_8_mix_from_json()

    if level == "9. třída":
        t = confirmed_topic.lower()
        if t.startswith("literární druhy"):
            return cjl_gen_9_lit_forms_genres()
        if t.startswith("slohové postupy"):
            return cjl_gen_9_styles()
        if t.startswith("figury") or t.startswith("tropy"):
            return cjl_gen_9_figures_tropes()
        if t.startswith("synonyma") or t.startswith("antonyma") or t.startswith("homonyma"):
            return cjl_gen_9_sah()
        if "mix úloh" in t:
            return cjl_pool_9_mix_from_json()
        if "celkové opakování" in t:
            return cjl_pool_all_json_mix()

        if confirmed_topic == "Literární druhy a žánry":
            return cjl_gen_9_lit_from_mini()
        if confirmed_topic == "Figury a tropy":
            return cjl_gen_9_fig_from_mini()


# --- helper pro školní zaokrouhlování .5 nahoru ---
def _round_to(n: int, base: int) -> int:
    r = n % base
    return n - r if r * 2 < base else n + (base - r)

def _normalize_numeric_str(s: str) -> str:
    s = (s or "").strip()
    # sjednotit minus a oddělovatka
    s = s.replace("\u2212", "-")          # případný unicode „−“
    s = s.replace("\u00A0", "").replace(" ", "")  # NBSP a mezery (tisícovky)
    s = s.replace(",", ".")               # čárka -> tečka
    # oprava okrajů typu ".5" nebo "12."
    if s.startswith("."): s = "0" + s
    if s.endswith("."):  s = s + "0"
    return s

def parse_int_answer(s: str):
    t = _normalize_numeric_str(s)
    try:
        # povolit zápis 12.0 == 12
        if "." in t:
            f = float(t)
            if abs(f - round(f)) < 1e-9:
                return int(round(f))
            return None
        return int(t)
    except Exception:
        return None

def parse_float_answer(s: str, decimals: int = 2):
    t = _normalize_numeric_str(s)
    try:
        return round(float(t), decimals)
    except Exception:
        return None


# =========================
# Pohádky 
# =========================


fairytales_data = {
    "Dráček z mechového lesa": {
        "text": "V Mechovém lese, v místech, kde mechy byly měkké jako polštáře a paprsky slunce tančily mezi větvemi, bydlel dráček Šimonek. S vílou Klárkou značili kroky kamínky a objevovali rytmus a melodii slov.  Dráček Šimonek nebyl žádný děsivý drak – byl celý zelený, měl kulaté bříško, třepotavá křidélka a smál se, až se mu od pusy místo ohně valily bubliny! Každý den létal nízko nad zemí a počítal, kolik hub vyrostlo, kolik ptáčků zpívá a kolik mravenců si staví cestu. Bavilo ho to – byl totiž moc zvědavý. Jednoho dne ale pršelo tak silně, že se všechny cestičky v lese roztekly. Dráček nevěděl, kudy domů. Sedl si pod kapradinu a smutně foukal bublinky. V tu chvíli kolem šla víla Klárka. „Šimonku, proč jsi smutný?“ zeptala se. „Ztratil jsem se! Neumím spočítat, kolik kroků vede k mojí jeskyni,“ povzdychl si dráček. „To nevadí,“ usmála se víla. „Spočítáme to spolu! Každých deset kroků označíme kamínkem.“ A tak šli. Po každých deseti krocích položili kamínek. Po dvaceti krocích – dva kamínky. Po třiceti – tři. A hádejte co? Když položili šestý kamínek, dráček vykřikl radostí: „To je moje jeskyně!“ Od té doby Šimonek vždy, když prší, pomáhá ostatním zvířátkům v lese najít cestu pomocí počítání kroků a kamínků. A víte co? Už se nikdy neztratil. Naučil se, že počítání může zachránit den.",
        "moral": "Naučme se počítat čísla a prožívat cestu k přátelství.",
        "obrazek_path": "dracek.png"
    },
    "O Šípkové Růžence": {
        "text": "Trny bludiště i vzory řeči: velké písmeno, tečka, slabiky. Matěj trpělivostí probudil království. Jak to bylo od začátku? Kdysi dávno se v království narodila malá princezna Růženka. Král s královnou uspořádali velkou oslavu a pozvali víly z celého světa. Každá víla přinesla princezně dar – krásu, zpěv, radost… Ale jedna víla nebyla pozvaná. A protože se urazila, přišla nepozvána a zvolala: „Až jí bude šestnáct, píchne se o trn a usne na sto let!“ Všichni se polekali. Jedna hodná víla ale řekla: „Nebude to navždy – až ji někdo s čistým srdcem najde, probudí se.“ Král dal spálit všechny trny v království. Ale jeden zůstal schovaný – v koutě staré věže. A tak když bylo Růžence právě šestnáct let, šla se projít po zámku. Objevila schody, po kterých nikdy nešla… a v prachu věže objevila starý kolovrátek. Píchla se – a v tu ránu usnula. Usnulo i celé království. Stromy narostly, trny prorostly zámek. Les spal. Sto let… Až jednoho dne přišel mladý kluk jménem Matěj. Byl zvědavý a odvážný. Když viděl, že trny tvoří bludiště, začal počítat, kudy se dostane dál. Počítal kroky, hledal vzory, skládal cesty. Až došel ke dveřím… Uvnitř uviděl dívku, která spala jako anděl. Matěj ji tiše oslovil: „Jsi Růženka? Já jsem Matěj. Přinesl jsem ti světlo dnešního dne.“ V tu chvíli se Růženka probudila. Les se prosvítil. Trny se proměnily v květy.         A co dál? Matěj s Růženkou se stali přáteli – a každý den počítali květiny, ptáky i roky, které už nespí.",
        "moral": "Trpělivost a pozorné čtení probouzí význam.",
        "obrazek_path": "ruzenka.png"
    },
    "Popelka": {
        "text": "Jednou byla dívka, která třídila fazole a slova; na plese vnímala hudbu i řeč – měkké a tvrdé souhlásky. V jedné daleké zemi žila dívka jménem Popelka. Její jméno vzniklo podle popela, který denně vymetala z krbu. I když žila v těžkých podmínkách – její nevlastní matka a dvě sestry jí stále poroučely – Popelka byla chytrá, trpělivá a měla dobré srdce. Když měla chvilku klidu, hrála si Popelka s kamínky a fazolemi. Nejenže z nich skládala obrazce, ale také počítala – sčítala je, řadila podle velikosti, třídila podle barvy. Matematika jí pomáhala zapomenout na starosti. Jednou večer přišel do vsi královský posel a rozhlásil: „Princ pořádá velký bál! Vybere si nevěstu. Každá dívka je zvána!“ Sestry se začaly chystat – počítaly šaty, boty a šperky: „Já mám 5 náušnic, ty máš 2... to je 7! Potřebujeme ještě 3 do deseti!“ Popelka tiše doufala, že půjde taky. Ale macecha jí jen řekla: „Ty nikam nejdeš, nemáš co na sebe – a nejdřív roztřiď 3 hrnce hrachu a čočky!“ Popelka si sedla a zoufala si – ale vtom se objevil bílý ptáček. „Pomohu ti. Ale musíš pomoci i ty mně – spočítej, kolik je 3x7.“ „To je dvacet jedna,“ řekla Popelka. Ptačí pomocníci zamávali křídly a všechna zrnka roztřídili. A vtom – zablesklo se. Na dvoře stála víla. „Zasloužíš si jít na ples. Pomohla jsi ostatním a umíš počítat!“ Mávla hůlkou – Popelka měla šaty poseté hvězdami, skleněné střevíčky a kočár z dýně. „Ale pamatuj – o půlnoci vše zmizí!“ Na plese Popelka okouzlila prince. Tancovali spolu a smáli se. Princ jí řekl: „Chci dívku, která má nejen krásné oči, ale i bystrý rozum. Položím ti hádanku: Když dnes máme 12 hostů, zítra přijde o 5 víc, kolik jich bude celkem?“ „Sedmnáct!“ usmála se Popelka. Princ byl ohromen. Ale hodiny odbily dvanáct, Popelka utekla… a ztratila jeden střevíček. Druhý den princ objížděl celé království a zkoušel skleněný střevíček dívce po dívce. V každém domě se zastavil, spočítal dívky a zapsal si, kolik pokusů už udělal. Až nakonec dorazil do posledního domu – kde našel tu pravou. Střevíček padl – a Popelka i princ věděli, že jejich životy se právě změnily.",
        "moral": "Krása bez rozumu nevydrží – ale rozum a laskavost září navždy. Ten, kdo počítá, třídí, učí se a pomáhá ostatním, nakonec najde cestu i ze smutku.",
        "obrazek_path": "popelka.png"
    },
    "Počítání s lesní vílou Klárkou": {
        "text": "V hlubokém zeleném lese, kde slunce jemně prosvítá mezi listy, žila malá víla jménem Klárka. Každé ráno si oblékla svou růžovou květinovou sukýnku a vyletěla ze své šiškové chaloupky. Víla Klárka měla důležitý úkol – počítat vše, co se v lese děje. Kolik květin rozkvetlo, kolik ptáčků se narodilo, kolik veverek si schovalo oříšky. Jenže jednoho dne se všechno zamotalo! 🌸 „Dnes mi to nějak nejde,“ povzdychla si Klárka. „Pořád ztrácím počet!“ Vtom přišel dráček Šimonek. „Já ti pomůžu,“ řekl. A tak začali spolu: 🐞 „Támhle jsou 3 berušky,“ řekla Klárka. 🐦 „A tam 2 sýkorky, to je dohromady…?“ „5!“ vykřikl Šimonek radostně.       Pak potkali 4 veverky a každá měla 2 oříšky. „Kolik oříšků dohromady?“ zeptala se víla. Šimonek chvilku počítal… „8 oříšků!“ Celý den tak spolu počítali. Nakonec Klárka řekla: „Díky, dráčku. Učila jsem les počítat, ale dneska mě to naučil les a Ty!“     A od té doby chodili lesem spolu – víla s kouzelnou hůlkou a dráček s bystrou hlavičkou.",
        "moral": "Počítání může být zábava – zvlášť, když na to nejsi sám!",
        "obrazek_path": "vila.png"
    },
    "Sněhurka a sedm trpaslíků": {
        "text": "Kdysi dávno žila krásná dívka jménem Sněhurka. Měla vlasy černé jako noc, pleť bílou jako sníh a srdce laskavé jako jarní slunce. Jednoho  dne musela utéct do lesa, protože zlá královna jí nepřála. Běhala mezi stromy, až narazila na malý domeček. Zaklepala, ale nikdo  neodpověděl. Opatrně vešla – uvnitř bylo sedm židliček, sedm hrníčků a sedm postýlek. Sněhurka byla unavená, a tak si na chvilku lehla. A co se nestalo? Domeček patřil sedmi trpaslíkům – každý měl jinou barvu čepičky a jméno podle své nálady: Červený: Veselík, Oranžový: Popleta, Žlutý: Sluníčko, Zelený: Moudřík, Modrý: Plačtík, Fialový: Chrápálek, Bílý: Počtář. Když Sněhurku našli, vůbec se nezlobili. Byli rádi, že s nimi zůstane – vařila jim, uklízela a učila počítat a poznávat barvy. Jednoho dne však přišla zlá královna v přestrojení a nabídla Sněhurce červené jablko. Ale nebylo obyčejné – bylo začarované! Sněhurka si kousla… a usnula. Trpaslíci byli smutní. Ale jednoho dne projížděl kolem lesem princ, který uslyšel, co se stalo. Položil jablko na váhu a zjistil, že červená půlka vážila víc než zelená – a byla to ta kouzelná! Když jablko rozlomili a zakouzlili kouzelnou formuli (kterou naučil Počtář), Sněhurka se probudila! A víte co? Všichni se radovali, tancovali podle barev duhy – a každý den počítali nové příběhy.",
        "moral": "Někdy i malý trpaslík nebo obyčejné číslo může změnit velký příběh.",
        "obrazek_path": "snehurka.png"
    },
    "Červená Karkulka": {
        "text": "Karkulka šla navštívit svou babičku a nesla jí jídlo. V lese potkala vlka, který ji přelstil a dostal se k babičce dřív. Naštěstí je obě zachránil statečný myslivec.",
        "moral": "Kdo je podmět, co je přísudek? Ve větě i v příběhu je důležité vědět, kdo co dělá a komu. Rozumět větám znamená rozumět příběhům.",
        "obrazek_path": "karkulka.png"
    },
    "O Zlatovlásce": {
        "text": "Kdysi dávno žila v zámku princezna jménem Zlatovláska. Měla vlasy jako slunce – zlaté, lesklé a dlouhé až po paty. Ale nebyla jen krásná, byla i moudrá a laskavá. Každý den se procházela v zahradě a povídala si s ptáčky, květinami i malými broučky. Jednoho dne se v království objevil mladý kuchař Jiřík. Pracoval na zámku a zaslechl, že princezna je zakletá: „Zlatovláska nemůže být šťastná, dokud někdo nesplní tři kouzelné úkoly,“ řekl starý zahradník. Jiřík se rozhodl, že jí pomůže. Nebál se ničeho – ani draka, ani hádanek. První úkol: „Přines z řeky perlu, kterou tam upustil král,“ řekla zlatá rybka. Jiřík skočil do vody, početl bubliny – bylo jich deset – a na dně našel perlu. Druhý úkol: „Rozlušti hádanku,“ řekla moudrá sova. „Když mám dvě křídla a neumím létat – co jsem?“ Jiřík přemýšlel… „Dveře!“ zvolal. A sova pokývala hlavou. Třetí úkol: „Najdi srdce princezny,“ řekla čarovná květina. Jiřík šel do zahrady, kam Zlatovláska ráda chodila, a posadil se. „Tady je její srdce. Miluje květiny, zvířata a svět,“ řekl tiše. V tu chvíli se zakletí zlomilo. Zlatovláska se usmála a její zlaté vlasy zazářily ještě víc než dřív. A jak to dopadlo? Jiřík zůstal na zámku, vařil tu nejlepší polévku na světě – a srdce Zlatovlásky bylo šťastné.",
        "moral": "Jiřík rozpozná přímou řeč, slovní druhy a stavbu věty. Moudrá řeč otevírá brány.",
        "obrazek_path": "zlatovlaska.png"
    },
    "Sněhová královna": {
        "text": "Byli jednou dva kamarádi – Gerda a Kaj. Každý den si hráli na zahradě, běhali, sbírali květiny a dívali se na hvězdy. Jednoho zimního dne ale přiletěla Sněhová královna. Byla krásná, ale studená jako led. Mráz jí létal kolem vlasů a vločky jí sedaly na ramena. Když Kaj koukal z okna, jedna vločka mu spadla přímo do oka a malý střep ledu mu vklouzl do srdce. Od té chvíle už nebyl stejný. Přestal se smát, začal být zlý a odešel s královnou do jejího ledového zámku na dalekém severu. Gerda byla smutná, ale nevzdala se. Vydala se Kaje hledat. Šla lesem, kolem řeky, potkala vrány, lišku, babičku s květinami, a dokonce i prince a princeznu. Všichni jí pomáhali. Nakonec došla až ke zmrzlému zámku, kde seděl Kaj – úplně ztichlý a bledý. Už si ani nepamatoval, kdo je. Gerda ho obejmula. A slza z jejího oka dopadla na jeho srdce. Led roztál. Kaj si vzpomněl! Drželi se za ruce, sníh kolem začal tát a celý ledový zámek se proměnil v jaro. Spolu se vrátili domů – šťastní, že se nikdy nevzdali.",
        "moral": "Přátelství a slova dokážou roztavit led.",
        "obrazek_path": "snehova_kralovna.png"
    },
    "Perníková chaloupka": {
        "text": "Kdysi dávno, v malé chalupě na okraji lesa, žil dřevorubec se svými dvěma dětmi – Jeníčkem a Mařenkou. Byli chudí, ale vždy si všechno dělili, i to nejmenší. Otec jim jednoho dne dal poslední, co měl: malé červené jablíčko. „Děti moje, podělte se,“ řekl. „Ať vám vydrží co nejdéle.“ Mařenka se usmála a řekla: „Půlka pro tebe, půlka pro mě.“ Jeníček přikývl, ale místo aby jablíčko rozkrojili, jen si z něj oba malinko kousli – a pak ho schovali. A co bylo zvláštní – jablko zůstalo celé. Nezdálo se, že by ubylo. „To je zvláštní,“ řekla Mařenka. „Asi ví, že se dělíme.“ Druhého dne je macecha zavedla hluboko do lesa. Děti si chtěly zapamatovat cestu zpět, ale déšť smyl stopy a ptáci sezobali drobky. Bloudili dlouho. Když měli hlad, vytáhli jablíčko. „Už nám moc nezbylo,“ řekl Jeníček. „Ale vždyť se na něj podívej – pořád je celé,“ zašeptala Mařenka. A opravdu – jablíčko zůstávalo kulaté, lesklé a šťavnaté, přestože se z něj občas kousli. Možná proto, že se nikdy nehádali, kdo má víc. Pak spatřili chaloupku – z perníku, cukroví a bonbonů. Voněla jako sen. Ale děti věděly, že něco, co je až příliš sladké, může být nebezpečné. Ulomili si jen kousek – a i ten si rozdělili. A jablíčko, které nosili s sebou, pořád zůstávalo v kapse – celé, teplé, jako by dýchalo. Vtom se otevřely dveře. Vyšla stará žena, vlídná na pohled. Pozvala je dovnitř, ale brzy zavřela Jeníčka do klece a Mařenku nutila vařit. Děti však neztratily naději – měly pořád své jablíčko, které si dávaly večer potají k nosu, aby si připomněly domov. Mařenka vymyslela plán. Když čarodějnice chtěla Jeníčka upéct, poprosila ji, ať jí ukáže, jak se leze do pece. Když tam vlezla, Mařenka dvířka zavřela. Děti se osvobodily a našly truhlu se zlaťáky. Ale největší poklad měly u sebe: jablíčko, které zůstávalo celé – protože se o něj vždy dělily. Na cestě domů potkávaly hladové zvířátko, unaveného poutníka – každému nabídly kousek. A jablko? Zůstávalo kulaté. Možná proto, že ten, kdo dává s láskou, nikdy nepřijde o to, co má.",
        "moral": "Jeníček a Mařenka dělí jablíčko i slova – slabiky, hlásky, významy. Poctivost a porozumění vedou domů.",
        "obrazek_path": "pernikova_chaloupka.png"
    },
    "O slepičce a kohoutkovi": {
        "text": "Byli jednou kohoutek Galois a slepička Poule. Celý den se spolu hrabali v prachu dvora a hledali dobrůtky. Byli nerozluční – vždy si dělili, co našli, a nikdy se nehádali. Jednoho dne, když už slunce zapadalo a země voněla večerem, našel kohoutek v hlíně zlatavé semínko – krásné, kulaté, lesklé, jaké ještě nikdy neviděli. „Jé, semínko!“ zakokrhal kohoutek. „Našel jsem ho první, je moje!“ Slepička ale sklopila hlavičku a tiše řekla: „Copak jsme se nedomluvili, že vše dělíme napůl?“ Kohoutek se zarazil. Dlouze se na semínko zadíval, pak na slepičku, a zase na semínko. „Ale když jsem ho našel první...“ zamumlal. A v tu chvíli se zlaté semínko zatřpytilo a začalo mizet. Kohoutek zůstal stát s otevřeným zobákem – semínko bylo pryč! V trávě zašuměl vánek a zněl jako hlas: „Co je sobecké, ztrácí se. Co je sdílené, roste.“ Kohoutek se podíval na slepičku. Zahanbeně sklonil hlavu. „Příště budeme dělit, ať najde kdo chce,“ řekl. A od té doby si vše, co našli, spravedlivě rozdělovali – i když to bylo jen jedno jediné semínko.",
        "moral": "Co je nalezeno pro sebe, bývá snadno ztraceno. Co je sdíleno, má sílu růst.",
        "obrazek_path": "slepicka.png"
    },
    "O jednorožci a dráčkovi": {
    "text": "V zemi za Duhovými horami žil bílý jednorožec jménem Lumin. Jeho roh zářil tak jasně, že dokázal prozářit i nejtemnější noc. Lumin miloval klid a ticho louky, kde rostly květiny všech barev, a každý den se procházel mezi nimi, aby nasbíral trochu radosti do svého kouzelného srdce. Jednoho dne uslyšel v dálce podivné šustění a šupinaté škrábání. Když se otočil, uviděl malého zeleného dráčka s kulatýma očima a křídly, která byla skoro větší než on sám. Dráček se jmenoval Foglík – a byl to opravdový zvědavec. Uměl sice chrlit oheň, ale raději z něj dělal jen teplý vánek, aby nikomu neublížil. „Ahoj,“ zavolal Foglík, „co tu děláš?“ „Sbírám světlo a radost do svého rohu,“ odpověděl Lumin a usmál se. „Světlo? To by se mi hodilo. V jeskyni, kde bydlím, je pořád tma.“ A tak se zrodil nápad – každý den spolu vyrazili na cestu: Lumin svým rohem osvětloval tmavé kouty lesa a Foglík mu na oplátku pomáhal přeletět hluboké rokle, když mu nabídl křídla. Časem zjistili, že dohromady tvoří dokonalý tým – světlo a teplo, klid a hravost, zem a nebe. Jednoho večera se přihnala bouře. Lesem se prohnal vítr tak silný, že utrhl most přes řeku. Lumin by se sám přes vodu nedostal, ale Foglík ho vzal na hřbet a přenesl ho do bezpečí. Vděčný jednorožec potom rozzářil celý břeh tak jasně, že ostatní zvířátka našla cestu domů. Od té doby byli Lumin a Foglík nerozluční. A kdokoliv z kraje potřeboval pomoc, věděl, že když uvidí světlo rohu a zaslechne šustění malých dračích křídel, přichází dva nejlepší přátelé, kteří nikdy neodmítnou podat pomocnou ruku… nebo křídlo.", 
    "moral": "Skutečné přátelství vzniká tam, kde se lidé (nebo kouzelné bytosti) doplňují a pomáhají si. Každý má jiné schopnosti – a právě díky nim můžeme společně zvládnout to, co bychom sami nedokázali.",
    "obrazek_path":"jednorozec.png"
    },
    "Tyranosaurus Rex a tajemství modrého lesa": {
    "text":"Kdysi dávno, když svět patřil dinosaurům a po krajině se proháněly obrovské ještěři, žil v hustých pralesích mladý tyranosaurus jménem Rex. Nebyl největší ani nejsilnější z rodu, ale měl zvědavé oči a srdce odvážného badatele. Rex rád pozoroval okolí – místo toho, aby lovil od rána do večera, toulal se po lese a naslouchal zpěvu ptakoještěrů, šumění větru v kapradinách a bublání potůčků. Jednoho dne mu jeho kamarádka Tria, malá bystrá triceratops, pověděla o legendě: „Za horami je Modré údolí, kde roste strom, který se nikdy neláme a jeho listy svítí v noci. Říká se, že kdo z něj sní list, pozná, jak ochránit svůj domov.“ Rex se rozhodl, že ho musí najít. Cesta nebyla jednoduchá – musel projít močály, vyhnout se nebezpečným allosaurům a přejít přes řeku plnou mosasaurů. Ale na každé překážce mu někdo pomohl: pterosaurus ho převezl přes propast, stádo parazaurolofů ho varovalo před bahnitou pastí, a Tria mu kryla záda před hladovým deinonychem. Když konečně dorazili do Modrého údolí, zjistili, že strom opravdu svítí jemným modrým světlem. Rex si utrhl jeden list a ochutnal ho. V tu chvíli pochopil, že síla není jen v ostrých zubech a drápech, ale hlavně v přátelství a ochotě chránit druhé. A tak se vrátil domů, kde s ostatními dinosaury začal hlídat les, čistit řeky a odhánět nebezpečí, které by mohlo ublížit jejich krajině.",
    "moral": "I ten nejmocnější je opravdu silný teprve tehdy, když umí chránit a pomáhat druhým.",
    "obrazek_path": "tyrex.png"
    },
    "O princezně Daphnii Pulex" :{
    "text": "V hlubokém údolí, kde ranní mlhy objímaly vrcholky hor a potoky zpívaly tichou píseň, se rozkládalo křišťálové jezírko. Jeho voda byla tak průzračná, že i hvězdy v noci záviděly jejímu lesku. V té vodní říši žila princezna jménem Daphnia Pulex – malá, průhledná bytůstka, kterou lidé nazývají perloočkou. Daphnia nebyla obyčejná princezna. Vládla říši neviditelné pro lidské oko – světu mikroskopických bytostí. Její plášť byl z jemného chitinu, leskl se jako sklo, a uvnitř něj tlouklo srdíčko tak drobné, že by se schovalo v slze. Každý den mávala svými anténkami a tančila ve vodním sloupci, aby našla nejčerstvější kapičky potravy – drobounký fytoplankton. Ale nad jezírkem visela hrozba. Z hor se blížila bouře a s ní příval bahna, které by zakalilo vodu. „Když nebudeme mít světlo,“ povzdechla si Daphnia, „řasy neporostou a naše říše vyhladoví.“ Tu se Daphnia rozhodla pro odvážný čin. Pomocí zvláštní schopnosti, kterou jí dala příroda – cyklomorfózy – změnila svůj tvar. Vytvořila si na hlavě kouzelnou přilbici a prodloužila trny na svém těle, aby ji dravci neohrozili a aby mohla odplout až do horních, ještě čistých vrstev vody. Tam rozeslala neviditelné signály svým sestrám a bratřím. Všichni společně se seřadili do tichého vodního průvodu a pomalu přefiltrovali proudící vodu, jako by chtěli z jezírka odfouknout temnotu. Trvalo to tři dny a tři noci, než se voda znovu rozzářila modrozeleným světlem života. Řasy se začaly množit, rybky si přišly pochutnat a celé jezírko se opět stalo zpívající zahradou. Od té doby se mezi obyvateli jezírka říká: „Malé srdce může vykonat velké věci – když bije pro všechny.",
    "moral": "„Malé srdce může vykonat velké věci – když bije pro všechny. Vědecká poznámka ukrytá v příběhu:",
    "obrazek_path": "dafne.png"
     },
}

# --- Mýty pro 6.–9. třídu (oddělený katalog) ---
# --- Mýty pro 6.–9. třídu (oddělený katalog) ---
myths_data = {
    "Python": {
        "text":"Na úpatí hory Parnas, nedaleko města Delfy, žilo strašlivé prastaré monstrum – obrovský had jménem Python. Podle pověsti se zrodil z hlíny, kterou zanechal potopou očištěný svět, nebo byl potomkem samotné země, bohyně Gaie. Python střežil posvátné místo, kde z útrob země vyvěraly tajemné výpary, a kde lidé cítili, že se mohou dotknout hlasu bohů. Když se bohyně Létó měla stát matkou Apollóna a Artemidy, žárlivá Héra proti ní poslala právě tohoto hada. Python měl zabránit, aby Létó našla bezpečné místo k porodu. Létó však božskou ochranou nakonec porodila dvojčata – a její syn Apollón se rozhodl matčinu křivdu pomstít. Ještě jako mladý bůh si Apollón vzal luk a stříbrné šípy a vydal se proti Pythonovi. Strhla se veliká bitva, v níž se had svíjel a syčel kolem Parnasu. Apollón jej nakonec prostřílel svými šípy a Python padl mrtev u pramene Kastalské studny. Na památku svého vítězství založil Apollón v Delfách věštírnu, kde kněžka Pýthie sedávala na trojnožce a pronášela tajemné věštby. Samotný název „Pýthie“ a „pythijské hry“ odkazuje právě na poraženého Pythona.", 
        "moral":"Apollónovo vítězství nad Pythonem symbolizuje vítězství řádu, světla a umění nad chaosem a temnotou. Python, stvořený ze země, představuje sílu přírody a pradávného, instinktivního světa. Apollón, bůh hudby, poezie a věšteb, na jeho místě zakládá centrum řecké spirituality – delfskou věštírnu.",
        "obrazek_path":"python.png"

        },
    "Dafné": {
        "text": "Kdysi dávno, v době, kdy na světě ještě kráčeli bohové, žila krásná dívka jménem Dafné. Byla dcerou boha řeky Peneia a celé dny trávila v lesích, kde sbírala byliny a lovila zvěř. Měla ráda svobodu a klid, a proto se chtěla vyhnout všem nápadníkům. Jednoho dne se však stalo něco zvláštního. Bůh Apollón, ochránce hudby, poezie a světla, se dostal do sporu s bohem lásky, malým okřídleným Erotem. Apollón se mu posmíval, že jeho luk a šípy jsou jen pro děti. Erot se rozhodl ukázat, jak mocná jeho zbraň je. Vystřelil dva šípy: Zlatý šíp lásky zasáhl Apollóna – ten se okamžitě zamiloval do první dívky, kterou uviděl: byla to právě Dafné. Olovený šíp odporu zasáhl Dafné – od té chvíle cítila k Apollónovi jen strach a nechuť. Apollón běžel za ní, volal na ni slova lásky a sliboval jí všechno možné, ale Dafné utíkala stále dál. Běžela lesem, přes potoky a louky, dokud nemohla dál. Cítila, že ji Apollón skoro chytá. V zoufalství zavolala na svého otce, boha řeky: „Otče, pomoz mi! Změň mou podobu, ať už mě nemůže nikdy chytit!“ V tu chvíli začaly Dafné nohy těžknout a měnit se v kořeny, její ruce se proměnily v větve a prsty v listy. Její tělo se pokrylo kůrou a v mžiku se z ní stal vavřínový strom. Apollón k ní doběhl a objal její kmen. Bylo mu smutno, ale přísahal, že ji nikdy nezapomene. Vavřínové listy se pro něj staly symbolem slávy a vítězství – z nich se pletly věnce pro básníky a vítěze sportovních her.",
        "moral":"Příběh ukazuje, že ne každý cit musí být opětován a že svoboda je pro některé cennější než sláva. Mýtus vysvětluje původ vavřínu jako symbolu vítězství a slávy v řecké kultuře.",
        "obrazek_path": "dafne_apolon.png"
        },
    "Prométheus": {
        "text": "Na počátku časů, když bohové vládli z hory Olymp, žili lidé ještě v temnotě a nevědomosti. Neměli oheň, neuměli tvořit nástroje, jejich život byl chladný a plný strachu. Prométheus, „ten, který myslí dopředu“, byl z rodu Titánů. Měl lidstvo rád a chtěl jim pomoci. Viděl, jak lidé hladoví a třesou se zimou, zatímco bohové v přepychu hodují na Olympu. Rozhodl se tedy, že lidem přinese dar, který jim dá sílu a vědění – oheň. Tajně se vypravil na Olymp, přiblížil se k vozu boha Hélia a do dutého stébla rákosu ukryl jiskru slunečního ohně. Tuto jiskru pak donesl lidem na zem. Od té chvíle se vše změnilo: lidé se naučili vařit jídlo, kovat nástroje i zbraně, stavět domy a chránit se před divou zvěří. Stali se svobodnějšími a silnějšími. Když to však zjistil vládce bohů Zeus, rozhněval se. Nechtěl, aby lidé byli příliš mocní a nezávislí. Rozhodl se Prométhea potrestat. Nechal jej přikovat k hoře Kavkaz. Tam měl Prométheus trpět strašlivý úděl: každý den k němu přilétal obrovský orel, který mu kloval do jater. Protože byl Prométheus nesmrtelný, játra mu v noci vždy dorostla – a druhý den muka začínala znovu. Tak trpěl dlouhá staletí, až ho nakonec vysvobodil hrdina Héraklés, když přilétajícího orla skolil šípem a Prométhea osvobodil z pout.",
        "moral": "Prométheus je symbolem odvahy a oběti pro dobro lidstva. Oheň, který přinesl, představuje poznání, techniku, umění a civilizaci. Jeho trest ukazuje, že mocní se často bojí, když lidé získávají přílišnou sílu a svobodu.Poznání je dar i závazek: kdo víc ví, nese víc odpovědnosti.",
        "obrazek_path": "prometheus.png"
    },
    "Ikaros": {
        "text": "Kdysi dávno žil na Krétě slavný vynálezce a stavitel Daidalos. Byl to muž, který uměl vyrobit téměř cokoli – stroje, sochy, i spletité stavby. Právě on postavil pro krále Mínóa slavný Labyrint, v němž byl uvězněn netvor Minotaurus. Když však Daidalos pomohl Athénskému hrdinovi Théseovi z Labyrintu uprchnout, král se rozhněval. Daidala i jeho syna Ikara nechal uvěznit na ostrově Kréta, aby nemohli vyzradit tajemství Labyrintu. Daidalos se nechtěl smířit s vězením. Přemýšlel, jak uprchnout. Moře střežily lodě, ale nebe zůstalo volné. Vynalezl tedy něco, co lidé nikdy neměli – křídla. Sestrojil je z ptačích per, která připevnil voskem na dřevěnou kostru. Pro sebe i pro Ikara vyrobil stejná křídla. Než vzlétli, varoval syna: „Leť se mnou, Ikarie, a drž se uprostřed cesty. Nesmíš letět příliš nízko, jinak tě pohltí vlhkost moře. A nesmíš stoupat příliš vysoko, jinak žár slunce roztaví vosk, který drží tvá křídla pohromadě.“ Společně se vznesli k obloze a letěli nad mořem. Lidé dole je považovali za bohy. Ikaros byl opojen svobodou. Cítil se jako pták – nebo snad jako bůh. A zapomněl na otcovu radu. Začal stoupat výš a výš, stále blíž ke slunci. Žár se opřel do jeho křídel a vosk začal měknout a kapat. Pera se rozpadla, křídla se zlomila – a Ikaros padal. Zřítil se do moře, které se od té doby nazývá Ikarovo. Daidalos, zlomený žalem, ale stále živý, doletěl až do Sicílie, kde našel útočiště.",
        "moral": "Ikaros symbolizuje mladistvou pýchu a lehkomyslnost, touhu dosáhnout víc, než je dovoleno. Daidalos je obrazem rozumu a zkušenosti, který však někdy nedokáže uchránit před unáhleností. Příběh varuje před tím, jak snadno může svoboda přejít v hybris – přehnanou pýchu, která přináší pád.",
        "obrazek_path": "ikaros.png"
    },
    "Orfeus a Eurydika": {
        "text": "Orfeus byl syn boha Apollóna a múzy Kalliopé. Už od malička měl dar hudby – když hrál na svou lyru a zpíval, zastavil vítr, utišil rozbouřenou řeku a i divoká zvířata ho poslouchala. Jeho písně byly tak krásné, že dokázaly obměkčit i nejtvrdší srdce. Orfeus se zamiloval do krásné dívky Eurydiky. Byla to čistá a něžná láska, a tak se vzali. Jejich štěstí však netrvalo dlouho. Jednoho dne, když Eurydika běžela loukou, šlápla na hada, ten ji uštknul a ona zemřela. Orfeus byl zoufalý. Nedokázal se smířit s tím, že navždy ztratil svou milovanou. Rozhodl se udělat něco, co ještě žádný smrtelník nezkusil – sestoupit do podsvětí a přivést ji zpět. Podsvětí vládl Hádés se svou manželkou Persefonou. Nikdo, kdo jednou překročil hranici, se nevracel zpátky. Ale Orfeus šel s odhodláním a s lyrou v ruce. Hrál a zpíval tak krásně, že i stíny mrtvých se zastavily, aby naslouchaly, a netvor Kerberos, trojhlavý pes, přestal štěkat a ulehl k jeho nohám. Když se Orfeus dostal k Hádu a Persefoně, zahrál píseň tak smutnou, že i srdce boha mrtvých bylo dojaté. Hádés řekl: „Dobře, Orfee, dovolím ti odvést Eurydiku zpět na svět živých. Ale je tu podmínka – půjde za tebou a ty se nesmíš ani jednou otočit, dokud nevyjde na denní světlo. Pokud se otočíš, ztratíš ji navždy.“ Orfeus vyrazil. Cítil, jak jeho milovaná kráčí za ním – slyšel její kroky, vnímal její přítomnost, ale nemohl ji vidět. Stoupali vzhůru tmavými chodbami podsvětí. Jen pár kroků chybělo k východu. V Orfeovi ale zvítězila pochybnost – co když tam opravdu není? Co když jej Hádés oklamal? V tu chvíli se otočil. A spatřil Eurydiku, jak se na něj smutně usmívá, než zmizí zpět do říše mrtvých – tentokrát navždy. Orfeus zůstal sám, naplněný žalem. Putoval světem, ale jeho písně už nebyly radostné – byly smutné a teskné. Nakonec byl roztrhán rozvášněnými Ménadami, služebnicemi boha Dionýsa. Jeho duše však sestoupila do podsvětí a tam se znovu setkala s Eurydikou. Od té chvíle už byli navždy spolu.",
        "moral": "Láska a důvěra potřebují vytrvalost: jeden okamžik netrpělivosti může všechno zmařit. Láska je silná, ale vyžaduje důvěru – pochybnost může zničit i ten největší dar. Umění má moc obměkčit i to nejtvrdší srdce – Orfeova hudba otevřela brány podsvětí. Některé ztráty jsou nevratné – příběh učí, že smrt patří k lidskému osudu. Naděje a smutek se prolínají – Orfeův příběh je zároveň tragický i krásný, protože ukazuje hloubku lidské lásky.",
        "obrazek_path": "orfeus.png"
    },
    "Persefona a Hádes": {
        "text": "Persefona byla krásná dívka, dcera nejvyšší bohyně plodnosti a úrody, Démétry, a vládce bohů, Dia. Vyrůstala na loukách a v zahradách, obklopená květinami a světlem. Kdekoliv šla, tam rozkvetly stromy a tráva se zazelenala. Jednoho dne, když Persefona s přítelkyněmi sbírala květiny na louce, spatřila zvláštní narcis, který byl nádhernější než všechny ostatní. Když jej utrhla, rozevřela se země a z hlubin vyjel Hádés, vládce podsvětí, v černém voze taženém ohnivými koňmi. Persefonu unesl a odvezl ji do své říše mrtvých, aby se stala jeho manželkou a královnou. Démétér hledala svou dceru po celém světě. Toulala se dnem i nocí, dokud se nedozvěděla pravdu – že ji odnesl Hádés. Zoufalství ji ochromilo. Přestala pečovat o pole a zahrady, úroda vyschla, stromy přestaly rodit a na zemi přišel hladomor. Lidé začali umírat a svět se ponořil do bídy. Nakonec musel zasáhnout samotný Zeus. Nechtěl, aby lidstvo zahynulo, a proto poslal posla Hermése, aby přinesl zprávu Hádovi: musí Persefonu propustit. Hádés nechtěl přijít o svou manželku. Nabídl Persefoně jídlo – a ona, aniž tušila následky, snědla několik zrníček granátového jablka. V podsvětí platilo přísné pravidlo: kdo tam okusí jídlo, nemůže odejít navždy. Proto byl uzavřen kompromis: Persefona bude část roku u své matky na zemi a část roku v podsvětí s Hádém. Když je Persefona na zemi, Démétér se raduje a svět je plný života – nastává jaro a léto. Když však musí sestoupit k Hádovi, Démétér se zarmoutí, příroda usíná a přichází podzim a zima.Mýtus učí přijmout cykly ztráty a návratu, tmy a světla.",
        "moral": "Život má své rytmy: místo boje s nimi hledej, jak v nich moudře žít. Život je koloběh – po období hojnosti přichází útlum a smutek, ale po zimě vždy znovu přichází jaro. Každá radost má svou cenu – Persefona má dvě podoby života, stejně jako člověk zakouší světlo i temnotu. Matčina láska je mocná – Démétrin zármutek otřásl světem i bohy. Úmluva a rovnováha – mýtus ukazuje, že i bohové musejí hledat kompromisy, aby svět fungoval.",
        "obrazek_path": "persefona.png"
    },
    "Sisyfos": {
        "text": "Kdysi dávno vládl v Řecku chytrý a prohnaný král jménem Sisyfos (někdy psán Sisyphos). Byl to král města Korintu, slavný svou vynalézavostí, ale ještě více svou vychytralostí a klamem. Sisyfos byl známý tím, že dokázal přelstít kohokoli – lidi i bohy. Zrazoval cizince, porušoval přísahy a prodával tajemství olympských bohů. Jednou dokonce prozradil řekům, že bůh Zeus unesl nymfu Aigínu. Bohové mu to nemohli zapomenout. Když se jeho čas naplnil, poslal Zeus boha smrti Thanata, aby Sisyfa odvedl do podsvětí. Jenže Sisyfos nebyl snadná kořist. Podařilo se mu Thanata přelstít a dokonce jej spoutal řetězy. Smrt přestala fungovat – lidé přestali umírat a na zemi vznikl zmatek. Bohové byli rozhořčeni, protože narušený řád vesmíru hrozil zničit svět. Nakonec musel zasáhnout bůh války Áres, který Thanata vysvobodil a Sisyfa odvedl do podsvětí. Ani tam se Sisyfos nesmířil se svým osudem. Než zemřel, přikázal své ženě Mérope, aby neprovedla řádný pohřební rituál. V podsvětí si pak stěžoval bohyni Persefoně, že jeho žena neprojevila patřičnou úctu, a vyprosil si povolení vrátit se na zem, aby ji potrestal. Jakmile se však vrátil, znovu začal žít jako král a odmítal odejít zpět. Teprve po dlouhé době jej bohové násilím přinutili vrátit se do říše mrtvých. Tentokrát už mu neodpustili. Zeus a Hádés rozhodli, že Sisyfos dostane trest, který nikdy neskončí. Musel valit obrovský kámen do strmého kopce. Jenže pokaždé, když se dostal téměř na vrchol, kámen se mu vytrhl a skutálel zpět dolů. A tak Sisyfos začínal svůj úkol znovu a znovu – navěky, bez naděje na úspěch.",
        "moral": "Smysl často nevzniká výsledkem, ale postojem k práci samotné.",
        "obrazek_path": "sisyfos.png"
    },
    "Odysseus a Sirény": {
        "text": "Po skončení trojské války se hrdina Odysseus vracel se svými druhy na rodný ostrov Ithaku. Jeho cesta byla však plná nebezpečí a zkoušek. Jedna z nejstrašnějších pastí čekala na širém moři – zpěv Sirén. Sirény byly bytosti s ženskými hlasy, krásné a neodolatelné, ale jejich těla byla napůl ptačí. Žily na ostrově obklopeném skalisky a víry. Každý, kdo uslyšel jejich zpěv, byl okouzlen, zapomněl na vše, a plul za hlasem, až jeho loď ztroskotala o skály. Odysseus o tomto nebezpečí věděl – varovala ho kouzelnice Kirké. Poradil se s družinou a vymyslel plán. Když se jejich loď blížila k ostrovu Sirén, Odysseus přikázal námořníkům, aby si ucpali uši včelím voskem. Sám však toužil slyšet zpěv těchto bytostí, aby poznal jejich moc – a přesto přežil. Proto nařídil, aby jej pevně přivázali ke stěžni a nepovolovali pouta, i kdyby je prosil. Jakmile se přiblížili, Sirény začaly zpívat. Jejich hlas byl sladký a svůdný: slibovaly Odysseovi poznání všech tajemství světa a slávu, pokud k nim připluje. Odysseus se zmítal v provazech, volal na muže, aby jej odvázali a zamířili k ostrovu. Ale námořníci, se zakrytýma ušima, neslyšeli nic a pokračovali v plavbě. Sirény křičely a zpívaly, ale loď už byla mimo jejich dosah. Tak Odysseus přežil tuto zkoušku – jediný smrtelník, který slyšel zpěv Sirén a nezahynul.", 
        "moral": "Sirény představují svody, které lákají člověka k zkáze pod rouškou krásy a slibů. Odysseus zosobňuje moudrost a schopnost předvídat: věděl, že lidská vůle je slabá, proto se nechal připoutat, aby se ochránil před vlastní touhou. Mýtus ukazuje, že někdy se člověk musí omezit a přijmout hranice, aby se zachránil.",
        "obrazek_path": "sireny.png"
    },
    "Perseus a Medúza": {
        "text": "Kdysi dávno žila trojice strašlivých sester Gorgon – Sthenó, Euryalé a Medúza. Jen jedna z nich, Medúza, byla smrtelná. Její krása byla tak veliká, že podle některých pověstí dokonce přilákala Poseidona do chrámu bohyně Athény. Tímto znesvěcením se Athéna rozhněvala a Medúzu potrestala: proměnila její nádherné vlasy v jedovaté hady a její pohled v kletbu – kdokoli se jí podíval do očí, zkameněl. Král Polydektés toužil po krásné Danai, matce hrdiny Persea, a chtěl se Perseuse zbavit. Přikázal mu, aby přinesl hlavu Medúzy – úkol, který se zdál nemožný. Perseovi se však dostalo pomoci od bohů. Hermés mu daroval křídlaté sandály, aby mohl létat, a kouzelný meč. Athéna mu poskytla lesklý bronzový štít, v němž se zrcadlil obraz, takže se na Medúzu nemusel dívat přímo. Od nymf získal ještě přilbu neviditelnosti a kouzelnou brašnu (kibisis), v níž mohl hlavu bezpečně ukrýt. Vydal se tedy do sídla Gorgon, kde spaly mezi zkamenělými oběťmi. Perseus postupoval opatrně, kráčel pozpátku a díval se jen do štítu jako do zrcadla. Přiblížil se k Medúze a jediným rozhodným úderem jí usekl hlavu. V tu chvíli se z její krve zrodil okřídlený kůň Pegasos a bojovník Chrysaór. Perseus pak vložil hlavu do brašny a s pomocí božských darů unikl rozzuřeným nesmrtelným sestrám. Cestou domů zažil ještě mnoho dobrodružství – například zachránil princeznu Andromedu, kterou měl pohltit mořský netvor. Nakonec se vrátil a ukázal hlavu Medúzy Polydektovi a jeho dvořanům – ti se proměnili v kámen.",         "moral": "Síla bez rozumu nestačí; připravenost a pomoc druhých rozhodují.",      
        "moral": "Perseus představuje odvahu, ale také moudrost a opatrnost – zvítězil ne silou, ale díky darům bohů a schopnosti použít je chytře. Medúza je symbolem nebezpečné, ničivé krásy i trestu bohů. Její hlava se stala ochranou: Athéna ji umístila na svůj štít, aby odrážela zlo.",
        "obrazek_path": "meduza.png"
    },
    "Theseus a Minotaurus": {
        "text": "Kdysi dávno vládl na ostrově Kréta mocný král Mínós. V jeho paláci se ukrývalo děsivé tajemství: netvor jménem Minotaurus – napůl člověk, napůl býk. Tento tvor se zrodil jako trest bohů, a aby jej mohl Mínós ukrývat, nechal od vynálezce Daidala postavit obrovský Labyrint, z něhož nebylo úniku. Každých devět let musela Athény, které Mínós přemohl ve válce, posílat na Krétu hroznou daň: sedm chlapců a sedm dívek, kteří byli v Labyrintu obětováni Minotaurovi. Když přišel čas třetí oběti, rozhodl se mladý hrdina Théseus, syn athénského krále Aigea, že tuto hanbu ukončí. Přihlásil se mezi obětované a vyplul na Krétu s pevnou vůlí Minotaura zabít. Na Krétě se do něj zamilovala Ariadna, dcera krále Mínóa. Bylo jí líto mladého hrdiny a rozhodla se mu pomoci. Darovala mu klubko nití, které mu měl poskytnout Daidalos. „Přivaž ho ke vchodu Labyrintu,“ řekla, „a odvíjej. Až budeš vycházet, půjdeš zpátky po niti.“ Théseus se vydal do temného Labyrintu. Nit odvíjel krok za krokem, až dorazil do samého středu, kde čekal Minotaurus. Strhla se strašlivá bitva – polobýk útočil s nelidskou silou, ale Théseus byl rychlý, obratný a odvážný. Nakonec se mu podařilo netvora skoliti a zabít. Podle niti se pak vrátil zpět a spolu s ostatními Athéňany uprchl z Labyrintu. Na lodi odvezl Ariadnu s sebou, ale jejich příběh měl další složitý vývoj. Do Athén se však vrátil jako hrdina, který ukončil krvavou daň a zachránil své město.",
        "moral": "Minotaurus symbolizuje nelidské vášně a temné síly, které člověka ohrožují. Labyrint představuje zmatek a nebezpečí života – bez rozumu a vedení bychom v něm bloudili. Théseus je hrdina, který se odváží čelit zlu, a díky odvaze i pomoci druhých (Ariadna, Daidalos) zvítězí. Ariadnina nit se stala symbolem moudrosti a cesty ven z nesnází, vedení, které umožňuje překonat chaos.",
        "obrazek_path": "theseus.png"
    }
}


# --- Knihovna podle pásma ročníků ---
STORY_LIBRARY = {
    "1-5": fairytales_data,  # stávající pohádky
    "6-9": myths_data,       # mýty
}

# =========================
# Poznámky (ČJ / MA / IT)
# =========================
cjl_notes_by_level = {
    "3. třída": ["Vyjmenovaná slova a příbuzná slova."],
    "4. třída": ["Slovní druhy – základní orientace."],
    "5. třída": ["Větné členy; analýza jednoduchých vět."],
    "6. třída": ["Shoda přísudku s podmětem; přímá řeč."],
    "7. třída": ["Souvětí, spojky, druhy vedlejších vět."],
    "8. třída": ["Vedlejší věty, interpunkce; slovní zásoba."],
    "9. třída": ["Rekapitulace pravopisu; literární minimum."]
}
math_notes_by_level = {
    "1. třída": ["Sčítání a odčítání do 10.",
                "Sčítání a odčítání do 20 (s i bez přechodu přes 10).", 
                 "Množiny – základ: {…}, počet prvků, „patří / nepatří“ (∈ / ∉) – intuitivně.",
                 "Formát odpovědi: celé číslo (např. 14)."],
    "2. třída": ["Sčítání/odčítání do 100; malá násobilka 2–9.","Formát odpovědi: celé číslo."],
    "3. třída": ["Sčítání/odčítání do 1000; dělení se zbytkem.",
                 "Formát (dělení se zbytkem): „podíl zb. zbytek“ (např. 5 zb. 2)."],
    "4. třída": ["Násobení/dělení vícecifernými čísly; zaokrouhlování.","Formát: celé číslo; u zaokrouhlení celé číslo."],
    "5. třída": ["Desetinná čísla; zlomky (krácení, porovnání).","Formát: čísla na 2 desetinná místa; zlomky zkráceně a/b."],
    "6. třída": ["Rozklad na prvočinitele; NSD/NSN; procenta; zlomky se stejným jmenovatelem."],
    "7. třída": ["Celá čísla; lineární rovnice; poměr a úměrnost."],
    "8. třída": ["Mocniny/odmocniny; Pythagoras; kruh (obvod/obsah)."],
    "9. třída": ["Rovnice; x^2=a; statistika; procenta/finance."]
}
# === MA: témata pro selectbox + formáty odpovědí (1.–9. třída) ===
MA_TOPICS_BY_GRADE = {
    "1. třída": ["Počítání - do 10", "Počítání - do 20 s přechodem přes 10", "Množiny – základ"],
    "2. třída": ["Sčítání a odčítání do 100", "Malá násobilka 2–9", "Sudá/lichá v množině", "Násobky 2–9 – třídění do množin",  ],
    "3. třída": ["Sčítání a odčítání do 1000", "Dělení se zbytkem"],
    "4. třída": ["Násobení vícecifernými čísly", "Dělení vícecifernými čísly", "Zaokrouhlování"],
    "5. třída": ["Desetinná čísla", "Zlomky: krácení", "Zlomky: porovnání"],
    "6. třída": ["Rozklad na prvočinitele", "NSD a NSN", "Procenta", "Zlomky se stejným jmenovatelem"],
    "7. třída": ["Celá čísla", "Lineární rovnice (základ)", "Poměr a úměrnost"],
    "8. třída": ["Mocniny a odmocniny", "Pythagorova věta", "Kruh: obvod a obsah"],
    "9. třída": ["Rovnice", "Kvadratické rovnice x²=a", "Statistika (průměr/medián)", "Procenta/finance"],
}
# === Témata (přidáváme „Množiny – …“) ===
MA_TOPICS_BY_GRADE["3. třída"] += [
    "Množiny – A∪B, A∩B, A\\B (1..20)",
    "Venn – 2 množiny (čísla 1..20)",
]
MA_TOPICS_BY_GRADE["4. třída"] += [
    "Venn – 3 množiny (2/3/5)",
    "Kartézský součin – počty",
]
MA_TOPICS_BY_GRADE["5. třída"] += [
    "Inkluze–exkluze (2–3 množ.)",
    "Komplement, De Morgan",
]
MA_TOPICS_BY_GRADE["6. třída"] += [
    "Intervaly jako množiny",
    "Sjednocení/průnik intervalů",
]
MA_TOPICS_BY_GRADE["7. třída"] += [
    "Kartézský součin – mřížka",
    "Relace vs. funkce (A→B)",
]
MA_TOPICS_BY_GRADE["8. třída"] += [
    "Obraz/předobraz množiny",
    "Složené nerovnice – intervaly",
]
MA_TOPICS_BY_GRADE["9. třída"] += [
    "Ekvivalence, třídy (mod n)",
    "Mocnina množiny, 2^n",
]



MA_TOPIC_FORMAT = {
    "1. třída": {
        "Počítání - do 10": "celé číslo 0–10",
        "Počítání - do 20 s přechodem přes 10": "celé číslo 0–20",
        "Množiny – základ": "počet prvků (celé číslo) nebo **ano/ne**",
    },
    "2. třída": {
        "Sčítání a odčítání do 100": "celé číslo",
        "Malá násobilka 2–9": "celé číslo",
    },
    "3. třída": {
        "Sčítání a odčítání do 1000": "celé číslo",
        "Dělení se zbytkem": "`podíl zb. zbytek` (např. `5 zb. 2`)",
    },
    "4. třída": {
        "Násobení vícecifernými čísly": "celé číslo",
        "Dělení vícecifernými čísly": "celé číslo",
        "Zaokrouhlování": "celé číslo",
    },
    "5. třída": {
        "Desetinná čísla": "na 2 desetinná místa (tečka NEBO čárka)",
        "Zlomky: krácení": "`a/b` (zkráceně)",
        "Zlomky: porovnání": "`<`, `>`, nebo `=`",
    },
    "6. třída": {
        "Rozklad na prvočinitele": "např. `2·2·3`",
        "NSD a NSN": "celé číslo",
        "Procenta": "na 2 desetinná místa (tečka NEBO čárka)",
        "Zlomky se stejným jmenovatelem": "`a/b` (zkráceně)",
    },
    "7. třída": {
        "Celá čísla": "celé číslo (může být záporné)",
        "Lineární rovnice (základ)": "číslo na 2 desetinná místa (tečka NEBO čárka)",
        "Poměr a úměrnost": "`a : b` (zkráceně)",
    },
    "8. třída": {
        "Mocniny a odmocniny": "číslo (u odmocnin na 2 desetinná místa (tečka NEBO čárka))",
        "Pythagorova věta": "na 2 desetinná místa (tečka NEBO čárka)",
        "Kruh: obvod a obsah": "na 2 desetinná místa (tečka NEBO čárka)",
    },
    "9. třída": {
        "Rovnice": "číslo na 2 desetinná místa (tečka NEBO čárka)",
        "Kvadratické rovnice x²=a": "nezáporné řešení, na 2 desetinná místa (tečka NEBO čárka)",
        "Statistika (průměr/medián)": "na 2 desetinná místa (tečka NEBO čárka)",
        "Procenta/finance": "na 2 desetinná místa (tečka NEBO čárka)",
    },
}

# === Formát odpovědi do poznámky (jen krátké doplnění) ===
MA_TOPIC_FORMAT.setdefault("3. třída", {}).update({
    "Množiny – A∪B, A∩B, A\\B (1..20)": "celé číslo / MCQ",
    "Venn – 2 množiny (čísla 1..20)": "MCQ",
})
MA_TOPIC_FORMAT.setdefault("4. třída", {}).update({
    "Venn – 3 množiny (2/3/5)": "MCQ",
    "Kartézský součin – počty": "celé číslo",
})
MA_TOPIC_FORMAT.setdefault("5. třída", {}).update({
    "Inkluze–exkluze (2–3 množ.)": "celé číslo",
    "Komplement, De Morgan": "MCQ",
})
MA_TOPIC_FORMAT.setdefault("6. třída", {}).update({
    "Intervaly jako množiny": "MCQ",
    "Sjednocení/průnik intervalů": "MCQ",
})
MA_TOPIC_FORMAT.setdefault("7. třída", {}).update({
    "Kartézský součin – mřížka": "celé číslo",
    "Relace vs. funkce (A→B)": "MCQ",
})
MA_TOPIC_FORMAT.setdefault("8. třída", {}).update({
    "Obraz/předobraz množiny": "MCQ",
    "Složené nerovnice – intervaly": "MCQ",
})
MA_TOPIC_FORMAT.setdefault("9. třída", {}).update({
    "Ekvivalence, třídy (mod n)": "MCQ",
    "Mocnina množiny, 2^n": "celé číslo",
})


# po definici MA_TOPIC_FORMAT:
MA_TOPIC_FORMAT["7. třída"]["Lineární rovnice (základ)"] = "číslo na 2 desetinná místa (tečka NEBO čárka)"
MA_TOPIC_FORMAT["2. třída"].update({
    "Sudá/lichá v množině": "Vyber jednu z možností a/b/c",
    "Násobky 2–9 – třídění do množin": "Vyber jednu z možností a/b/c",
})

# Doplňkové poznámky k vybraným tématům (zobrazí se pod hlavní větou pro ročník)
MA_TOPIC_HINTS = {
    "3. třída": {
        "Množiny – A∪B, A∩B, A\\B (1..20)": [
            "Uvažuj U={1..20}, A a B jsou množiny čísel podle zadání."
        ],
        "Venn – 2 množiny (čísla 1..20)": [
            "Zamysli se, zda prvek patří do A, do B, do obou, nebo do žádné."
        ],
    },
    "4. třída": {
        "Venn – 3 množiny (2/3/5)": [
            "A: násobky 2, B: násobky 3, C: násobky 5; sleduj průniky."
        ],
        "Kartézský součin – počty": [
            "Počet prvků A×B je |A|·|B|."
        ],
    },
    "5. třída": {
        "Inkluze–exkluze (2–3 množ.)": [
            "Pro dvě množiny platí |A∪B|=|A|+|B|−|A∩B|."
        ],
        "Komplement, De Morgan": [
            "De Morgan: (A∪B)ᶜ = Aᶜ ∩ Bᶜ a (A∩B)ᶜ = Aᶜ ∪ Bᶜ."
        ],
    },
    "6. třída": {
        "Intervaly jako množiny": [
            "Otevřený ( ), uzavřený [ ]; porovnej s nerovnicemi."
        ],
        "Sjednocení/průnik intervalů": [
            "Průnik = společná část; sjednocení = všechno dohromady."
        ],
    },
    "7. třída": {
        "Kartézský součin – mřížka": [
            "Počet bodů v mřížce m×n je m·n."
        ],
        "Relace vs. funkce (A→B)": [
            "Funkce: každému x∈A přiřazuje právě jedno y∈B."
        ],
    },
    "8. třída": {
        "Obraz/předobraz množiny": [
            "f(A) = {f(x): x∈A}, f⁻¹(B) = {x: f(x)∈B}."
        ],
        "Složené nerovnice – intervaly": [
            "Spoj dvě nerovnice a převeď na interval(y)."
        ],
    },
    "9. třída": {
        "Ekvivalence, třídy (mod n)": [
            "[k] = {… , k−n, k, k+n, …}; je to rozklad Z na n tříd.",
        ],
        "Mocnina množiny, 2^n": [
            "Počet podmnožin množiny s n prvky je 2^n."
        ],
    },
}

# === IT témata do selectboxu (jen UI popisy; úlohy se berou podle ročníku) ===
# můžeš si je kdykoli změnit – na logiku úloh to nemá vliv
IT_TOPICS_BY_GRADE = {
    "1. třída": ["Chůze po špičkách", "Posbírej 3 jahody"],
    "2. třída": ["Chůze + překážky", "Sběr ikon + pořadí"],
    "3. třída": ["Delší trasy + cyklus", "Jednoduché bludiště"],
    "4. třída": ["Optimalizace kroků", "Check-pointy a klíče"],
    "5. třída": ["Vzory a perioda", "Skládání slov (pořadí)"],
    # 6.–9. můžeš nechat prázdné (fallback níže) nebo si je pojmenuj:
    "6. třída": ["Základy: print / + / *", "Text + délka", "Celá čísla, //, %"],
    "7. třída": ["Podmínky if/else", "Seznamy: len/sum/[-1]", "Funkce (def)"],
    "8. třída": ["Mocniny/odmocniny", "Pythagoras", "Obvod kruhu (2 dp)"],
    "9. třída": ["Průměr/medián (2 dp)", "Posloupnosti (aₙ)", "Sestav větu ze slov"],
}

# -----------------------
# Poznámky k učivu (IT) – hlavní téma NAHOŘE + vzorový kód
# -----------------------
it_notes_by_level = {
    "1. třída": [
        "Tisk textu a čísel pomocí příkazu print. (Navazuje na ČJ: čtení krátkých slov a vět; MA: malé počty.)",
        "Příklad – text:\n```python\nprint('Ahoj')\nprint(\"Drak\")\n```",
        "Příklad – čísla:\n```python\nprint(2+3)\nprint(3*4)\n```"
    ],
    "2. třída": [
        "Spojování textu a práce s délkou textu. (Navazuje na ČJ: slova a písmena.)",
        "Příklad – věta s mezerou:\n```python\nprint('Ahoj světe')\n```",
        "Příklad – délka slova:\n```python\nprint(len('pohádka'))  # vytiskne 7\n```",
        "Příklad – poslední písmeno:\n```python\ns = 'víla'\nprint(s[-1])  # vytiskne a\n```"
    ],
    "3. třída": [
        "Celé dělení // a zbytek %; poslední znak řetězce. (Navazuje na MA: dělení se zbytkem; ČJ: práce s písmeny.)",
        "Příklad – celočíselné dělení a zbytek:\n```python\nprint(10//3)  # 3\nprint(10%3)   # 1\n```",
        "Příklad – poslední písmeno:\n```python\ns = 'drak'\nprint(s[-1])  # k\n```"
    ],
    "4. třída": [
        "Podmínka (if/else), zaokrouhlení pomocí round, porovnání. (Navazuje na MA: zaokrouhlování, porovnávání.)",
        "Příklad – podmínka:\n```python\na = 5\nprint('ano' if a > 3 else 'ne')\n```",
        "Příklad – zaokrouhlení na 2 desetinná místa:\n```python\nprint(round(3.14159, 2))  # 3.14\n```",
        "Příklad – porovnání:\n```python\nprint(7 > 4)  # True\n```"
    ],
    "5. třída": [
        "Tisk a práce se seznamem: délka, poslední prvek, součet prvků. (Navazuje na MA: sčítání více čísel.)",
        "Příklad – délka seznamu:\n```python\nL = [1, 2, 3]\nprint(len(L))  # 3\n```",
        "Příklad – poslední prvek seznamu:\n```python\nL = [3, 6, 9]\nprint(L[-1])  # 9\n```",
        "Příklad – součet prvků seznamu cyklem:\n```python\nL = [4, 5, 9]\ns = 0\nfor x in L:\n    s += x\nprint(s)  # 18\n```"
    ],
    "6. třída": [
        "Desetinná čísla (2 desetinná místa) a procenta. (Navazuje na MA: procenta a desetinná čísla.)",
        "Příklad – 2 desetinná místa:\n```python\nprint(f\"{10/4:.2f}\")  # 2.50\n```",
        "Příklad – procenta:\n```python\ntotal = 200\np = 15\nprint(f\"{total*p/100:.2f}\")  # 30.00\n```"
    ],
    "7. třída": [
        "Celá čísla (i záporná), vlastní funkce, // a % se zápornými. (Navazuje na MA: celá čísla, jednoduché funkce v IT.)",
        "Příklad – sčítání se zápornými:\n```python\nprint(-3 + 5)  # 2\n```",
        "Příklad – funkce:\n```python\ndef dvojnasobek(x):\n    return x*2\nprint(dvojnasobek(6))  # 12\n```",
        "Příklad – dělení a zbytek se zápornými:\n```python\nprint(-11//4)\nprint(-11%4)\n```"
    ],
    "8. třída": [
        "Mocniny, odmocniny, Pythagoras, obvod kruhu. (Navazuje na MA: mocniny/odmocniny, geometrie.)",
        "Příklad – mocnina a odmocnina:\n```python\nprint(7**2)\nprint(49**0.5)\n```",
        "Příklad – Pythagoras (3,4,5):\n```python\na = 3; b = 4\nprint((a*a + b*b) ** 0.5)  # 5.0\n```",
        "Příklad – obvod kruhu r=5 (π≈3.14):\n```python\nr = 5\nprint(f\"{2*3.14*r:.2f}\")\n```"
    ],
    "9. třída": [
        "Průměr a medián seznamu, spojování slov do věty. (Navazuje na MA: statistika; ČJ: větná stavba.)",
        "Příklad – průměr (2 dp):\n```python\nL = [2, 4, 6]\nprint(f\"{sum(L)/len(L):.2f}\")  # 4.00\n```",
        "Příklad – medián u sudého počtu:\n```python\nL = [1, 4, 7, 8]\nm = (L[1] + L[2]) / 2\nprint(f\"{m:.2f}\")  # 5.50\n```",
        "Příklad – spojování slov do věty:\n```python\nslova = ['Učíme', 'se', 'Python']\nprint(' '.join(slova))\n```"
    ],
}

# === Poznámky pro IT podle TÉMAT (6.–9. třída) ===
IT_TOPIC_NOTES = {
    "6. třída": {
        # z 1. třídy (print, +, *)
        "Základy: print / + / *": [
            "Tisk textu a čísel pomocí `print`.",
            "Příklad – text:\n```python\nprint('Ahoj')\nprint(\"Drak\")\n```",
            "Příklad – čísla:\n```python\nprint(2+3)\nprint(3*4)\n```"
        ],
        # z 2. třídy (len, indexace)
        "Text + délka": [
            "Spojování textu a práce s délkou textu (`len`).",
            "Příklad – věta s mezerou:\n```python\nprint('Ahoj světe')\n```",
            "Příklad – délka slova:\n```python\nprint(len('pohádka'))  # 7\n```",
            "Příklad – poslední písmeno:\n```python\ns = 'víla'\nprint(s[-1])  # a\n```"
        ],
        # z 3. třídy (//, %)
        "Celá čísla, //, %": [
            "Celočíselné dělení `//` a zbytek `%`.",
            "Příklad:\n```python\nprint(10//3)  # 3\nprint(10%3)   # 1\n```"
        ],
    },
    "7. třída": {
        # z 4. třídy (if/else)
        "Podmínky if/else": [
            "Podmínka `if/else` a jednoduché porovnání.",
            "Příklad – podmínka:\n```python\na = 5\nprint('ano' if a > 3 else 'ne')\n```",
            "Příklad – porovnání:\n```python\nprint(7 > 4)  # True\n```"
        ],
        # z 5. třídy (seznamy, len, [-1], součet)
        "Seznamy: len/sum/[-1]": [
            "Délka seznamu, poslední prvek, součet prvků.",
            "Příklad – délka:\n```python\nL = [1, 2, 3]\nprint(len(L))  # 3\n```",
            "Příklad – poslední prvek:\n```python\nL = [3, 6, 9]\nprint(L[-1])  # 9\n```",
            "Příklad – součet cyklem:\n```python\nL = [4, 5, 9]\ns = 0\nfor x in L:\n    s += x\nprint(s)  # 18\n```"
        ],
        # z 7. třídy (vlastní funkce)
        "Funkce (def)": [
            "Vlastní funkce a návratová hodnota.",
            "Příklad:\n```python\ndef dvojnasobek(x):\n    return x*2\nprint(dvojnasobek(6))  # 12\n```"
        ],
    },
    "8. třída": {
        # z 8. třídy
        "Mocniny/odmocniny": [
            "Mocnina `a**b`, druhá odmocnina `x**0.5`.",
            "Příklad:\n```python\nprint(7**2)\nprint(49**0.5)\n```"
        ],
        "Pythagoras": [
            "Přepona `sqrt(a*a+b*b)` (zde `**0.5`).",
            "Příklad:\n```python\na=3; b=4\nprint((a*a + b*b) ** 0.5)  # 5.0\n```"
        ],
        "Obvod kruhu (2 dp)": [
            "Použij π≈3.14 a tisk na 2 dp.",
            "Příklad:\n```python\nr = 5\nprint(f\"{2*3.14*r:.2f}\")\n```"
        ],
    },
    "9. třída": {
        # z 9. třídy
        "Průměr/medián (2 dp)": [
            "Aritmetický průměr a medián (na 2 dp).",
            "Příklad – průměr:\n```python\nL=[2,4,6]\nprint(f\"{sum(L)/len(L):.2f}\")  # 4.00\n```",
            "Příklad – medián u sudého počtu:\n```python\nL=[1,4,7,8]\nm=(L[1]+L[2])/2\nprint(f\"{m:.2f}\")  # 5.50\n```"
        ],
        # doplněné krátce (navazuje na MA/7: posloupnosti)
        "Posloupnosti (aₙ)": [
            "Arit.: `a_n = a + (n-1)*d`; Geom.: `a_n = a * q**(n-1)`."
        ],
        # z 9. třídy
        "Sestav větu ze slov": [
            "Spojení slov: `' '.join(slova)`."
        ],
    },
}

def build_it_tasks_by_topic():
    by = {g:{} for g in ["6. třída","7. třída","8. třída","9. třída"]}

    # 6. třída
    # Základy: print / + / *
    basics = []
    basics += [{"prompt": f"Vytiskni text: Ahoj", "starter":"", "expected_stdout":"Ahoj"}]
    basics += [{"prompt": f"Vytiskni {a}+{b}", "starter":"", "expected_stdout": str(a+b)} for a,b in [(2,3),(3,4),(5,6)]]
    basics += [{"prompt": f"Vytiskni {a}*{b}", "starter":"", "expected_stdout": str(a*b)} for a,b in [(2,3),(3,5),(4,4)]]
    by["6. třída"]["Základy: print / + / *"] = basics

    # Text + délka
    tdl = []
    tdl += [{"prompt": "Vytiskni délku slova 'pohádka'", "starter":"", "expected_stdout":"7"}]
    tdl += [{"prompt": "Vytiskni poslední písmeno slova 'víla'", "starter":"", "expected_stdout":"a"}]
    tdl += [{"prompt": "Vytiskni větu 'Ahoj světe'", "starter":"", "expected_stdout":"Ahoj světe"}]
    by["6. třída"]["Text + délka"] = tdl

    # Celá čísla, //, %
    dm = []
    for a,b in [(10,3),(11,4),(20,6),(25,7)]:
        dm.append({"prompt": f"Vytiskni {a}//{b}", "starter":"", "expected_stdout": str(a//b)})
        dm.append({"prompt": f"Vytiskni {a}%{b}",  "starter":"", "expected_stdout": str(a%b)})
    by["6. třída"]["Celá čísla, //, %"] = dm

    # 7. třída
    # Podmínky if/else
    cond = [{"prompt":"Je 7 > 4? Vytiskni True/False", "starter":"", "expected_stdout":"True"},
            {"prompt":"Je 3 > 5? Vytiskni True/False", "starter":"", "expected_stdout":"False"}]
    by["7. třída"]["Podmínky if/else"] = cond

    # Seznamy: len/sum/[-1]
    lists = []
    lists += [{"prompt": f"Vytiskni délku seznamu {L}", "starter":"", "expected_stdout": str(len(L))} for L in [[1,2,3],[3,6,9,12]]]
    lists += [{"prompt": f"Vytiskni poslední prvek seznamu {L}", "starter":"", "expected_stdout": str(L[-1])} for L in [[3,6,9],[2,5,7,11]]]
    lists += [{"prompt": f"Vytiskni součet prvků seznamu {L}", "starter":"", "expected_stdout": str(sum(L))} for L in [[4,5,9],[1,2,3,4]]]
    by["7. třída"]["Seznamy: len/sum/[-1]"] = lists

    # Funkce (def)
    by["7. třída"]["Funkce (def)"] = [
        {"prompt":"Definuj funkci dvojnasobek(x) a vytiskni dvojnasobek(6)", "starter":"", "expected_stdout":"12"}
    ]

    # 8. třída
    by["8. třída"]["Mocniny"] = [{"prompt": f"Vytiskni {n}**{e}", "starter":"", "expected_stdout": str(n**e)} for n,e in [(3,2),(4,2),(5,2),(2,3)]]
    by["8. třída"]["Odmocniny"] = [{"prompt": f"Vytiskni druhou odmocninu z {s} (pomocí **0.5)", "starter":"", "expected_stdout": str(float(s**0.5))} for s in [9,16,25,36]]
    by["8. třída"]["Pythagoras"] = [{"prompt": f"Pro odvěsny {a} a {b} vytiskni přeponu", "starter":"", "expected_stdout": str(float(c))} for a,b,c in [(3,4,5),(5,12,13),(6,8,10)]]
    by["8. třída"]["Obvod kruhu (2 dp)"] = [{"prompt": f"Vytiskni obvod kruhu pro r={r} (π≈3.14, 2 dp)", "starter":"", "expected_stdout": f"{2*3.14*r:.2f}"} for r in [3,4,5,7]]

    # 9. třída
    by["9. třída"]["Průměr/medián (2 dp)"] = (
        [{"prompt": f"Vytiskni průměr čísel {arr} (2 dp)", "starter":"", "expected_stdout": f"{sum(arr)/len(arr):.2f}"} for arr in [[2,4,6],[1,2,3,4,5],[10,20,30]]]
        + [{"prompt": f"Vytiskni medián čísel {arr} (2 dp)", "starter":"", "expected_stdout": f"{(arr[1]+arr[2])/2:.2f}"} for arr in [[1,4,7,8],[2,5,6,10]]]
    )
    seq = []
    for a,d,n in [(3,7,5),(1,9,5),(2,8,4)]:  # arit.
        seq.append({"prompt": f"Arit. posloupnost a={a}, d={d}, n={n} → vytiskni a_n", "starter":"", "expected_stdout": str(a+(n-1)*d)})
    for a,q,n in [(2,3,4),(1,2,5)]:         # geom.
        seq.append({"prompt": f"Geom. posloupnost a={a}, q={q}, n={n} → vytiskni a_n", "starter":"", "expected_stdout": str(a*(q**(n-1)))})
    by["9. třída"]["Posloupnosti (aₙ)"] = seq
    by["9. třída"]["Sestav větu ze slov"] = [{"prompt": f"Sestav větu ze slov {slova} (mezera mezi slovy)", "starter":"", "expected_stdout": " ".join(slova)} for slova in [["Učíme","se","Python"],["Pohádky","nás","baví"]]]

    return by

IT_TASKS_BY_TOPIC = build_it_tasks_by_topic()

# =========================
# IT Úkoly (návrat původních)
# =========================
def build_it_tasks_by_level():
    tasks = {}
    # 1. třída
    t1 = []
    texts = ["Ahoj","Drak","Víla","Python","Les","Popelka","Šimonek","Klárka","Bublina","Pohádka"]
    sums = [(2,3),(5,4),(7,2),(9,1),(6,3)]
    prods = [(2,5),(3,3),(4,2),(5,2),(6,2)]
    for s in texts:
        t1.append({"prompt": f"Vytiskni přesně text: {s}", "starter":"", "expected_stdout": s})
    for a,b in sums:
        t1.append({"prompt": f"Vytiskni výsledek {a}+{b}", "starter":"", "expected_stdout": str(a+b)})
    for a,b in prods:
        t1.append({"prompt": f"Vytiskni výsledek {a}*{b}", "starter":"", "expected_stdout": str(a*b)})
    tasks["1. třída"] = t1[:20]
    # 2. třída
    t2=[]; pairs=[("Ahoj","světe"),("Dobrý","den"),("Víla","Klárka"),("Drak","Šimonek"),("Pohádky","baví")]
    words=["les","strom","okno","kočka","drak","pohádka","víla","kámen"]
    for a,b in pairs: t2.append({"prompt": f"Vytiskni: {a} {b} (včetně mezery)", "starter":"", "expected_stdout": f"{a} {b}"})
    for w in words: t2.append({"prompt": f"Vytiskni délku slova '{w}'", "starter":"", "expected_stdout": str(len(w))})
    nums=[6,10,3,7,9,12,5,8]
    for x in nums: t2.append({"prompt": f"Vytiskni druhou mocninu čísla {x}", "starter":"", "expected_stdout": str(x*x)})
    tasks["2. třída"] = t2[:20]
    # 3. třída
    t3=[]; pairs=[(1,2),(3,4),(5,6),(7,8),(9,10)]
    for a,b in pairs:
        t3.append({"prompt": f"Vytiskni součet {a}+{b}", "starter":"", "expected_stdout": str(a+b)})
        t3.append({"prompt": f"Vytiskni rozdíl {a}-{b}", "starter":"", "expected_stdout": str(a-b)})
    names=["Eva","Jan","Petr","Ivana","Šárka","Marek","Tereza","Adam"]
    for n in names: t3.append({"prompt": f"Vytiskni 'Ahoj, {n}!'", "starter":"", "expected_stdout": f"Ahoj, {n}!"})
    tasks["3. třída"] = t3[:20]
    # 4. třída
    t4=[]
    for a in [5,2,7,0,10,3]:
        exp = "ano" if a>3 else "ne"
        t4.append({"prompt": f"Když a={a}, vytiskni 'ano', pokud a>3, jinak 'ne'.", "starter":"", "expected_stdout": exp})
    rounds=[3.14159,2.71828,1.995,2.345,7.005,5.555,12.349,0.845]
    for v in rounds: t4.append({"prompt": f"Zaokrouhli {v} na 2 desetinná místa a vytiskni", "starter":"", "expected_stdout": f"{round(v,2)}"})
    comps=[(7,4),(2,9),(5,5),(10,1),(3,3)]
    for a,b in comps: t4.append({"prompt": f"Vytiskni True/False: {a}>{b}", "starter":"", "expected_stdout": str(a>b)})
    tasks["4. třída"] = t4[:20]
    # 5. třída
    t5=[]; lists=[[1,2,3],[5,5,5],[2,4,6,8],[10,9,8],[3,7,1,5,9],[6,6,6,6],[1,3,5,7,9],[2,3,5,7,11],[100,200],[4]]
    for L in lists[:7]: t5.append({"prompt": f"Vytiskni délku seznamu {L}", "starter":"", "expected_stdout": str(len(L))})
    for L in lists[:7]: t5.append({"prompt": f"Vytiskni první prvek seznamu {L}", "starter":"", "expected_stdout": str(L[0])})
    for L in lists[7:10]: t5.append({"prompt": f"Vytiskni poslední prvek seznamu {L}", "starter":"", "expected_stdout": str(L[-1])})
    for L in lists[4:10]: t5.append({"prompt": f"Sečti prvky {L} cyklem for a vytiskni součet", "starter":"", "expected_stdout": str(sum(L))})
    tasks["5. třída"] = t5[:20]
    # 6. třída
    t6=[]; decs=[(10,4),(7,2),(5,2),(9,4),(8,3)]
    for a,b in decs: t6.append({"prompt": f"Vytiskni {a}/{b} na 2 desetinná místa", "starter":"", "expected_stdout": f"{a/b:.2f}"})
    sums=[(3.5,2.25),(1.2,3.4),(5.55,2.45),(10.0,0.75),(2.345,2.005)]
    for a,b in sums: t6.append({"prompt": f"Vytiskni součet {a}+{b} na 2 dp", "starter":"", "expected_stdout": f"{(a+b):.2f}"})
    perc=[(200,15),(500,20),(250,12),(400,25),(800,5),(1000,30),(150,40),(90,50),(360,10),(720,15)]
    for total,p in perc[:10]: t6.append({"prompt": f"Vytiskni {p}% z {total} (na 2 dp)", "starter":"", "expected_stdout": f"{total*p/100:.2f}"})
    tasks["6. třída"] = t6[:20]
    # 7. třída
    t7=[]; pairs=[(12,5),(20,3),(15,4),(18,6),(21,7),(19,2)]
    for a,b in pairs:
        t7.append({"prompt": f"Vytiskni {a}//{b}", "starter":"", "expected_stdout": str(a//b)})
        t7.append({"prompt": f"Vytiskni {a}%{b}", "starter":"", "expected_stdout": str(a%b)})
    tasks["7. třída"] = t7[:20]
    # 8. třída
    t8=[]; powers=[(3,2),(4,2),(5,2),(2,3),(6,2),(7,2),(8,2),(9,2)]
    for n,e in powers: t8.append({"prompt": f"Vytiskni {n}**{e}", "starter":"", "expected_stdout": str(n**e)})
    roots=[9,16,25,36,49,64]
    for s in roots: t8.append({"prompt": f"Vytiskni druhou odmocninu z {s} (…i **0.5)", "starter":"", "expected_stdout": str(float(s**0.5))})
    pyth=[(3,4,5),(5,12,13),(6,8,10)]
    for a,b,c in pyth: t8.append({"prompt": f"Pro odvěsny {a} a {b} vytiskni přeponu (Pythagoras)", "starter":"", "expected_stdout": str(float(c))})
    circles=[3,4,5,7]
    for r in circles: t8.append({"prompt": f"Vytiskni obvod kruhu o poloměru {r} (π≈3.14, 2 dp)", "starter":"", "expected_stdout": f"{2*3.14*r:.2f}"})
    tasks["8. třída"] = t8[:20]
    # 9. třída
    t9=[]; arith=[(3,7,5),(10,5,3),(1,9,5),(2,8,4)]
    for a,d,n in arith: t9.append({"prompt": f"Arit. posloupnost a={a}, d={d}, n={n} → vytiskni a_n", "starter":"", "expected_stdout": str(a+(n-1)*d)})
    geom=[(2,3,4),(1,2,5)]
    for a,q,n in geom: t9.append({"prompt": f"Geom. posloupnost a={a}, q={q}, n={n} → vytiskni a_n", "starter":"", "expected_stdout": str(a*(q**(n-1)))})
    med_pairs=[[1,4,7,8],[2,5,6,10],[3,3,7,9],[0,10,20,30]]
    for arr in med_pairs: t9.append({"prompt": f"Vytiskni medián čísel {arr} (2 dp)", "starter":"", "expected_stdout": f"{(arr[1]+arr[2])/2:.2f}"})
    reverse=[(120,20),(150,50),(240,20),(330,10)]
    for new,p in reverse: t9.append({"prompt": f"Po zdražení o {p}% je cena {new}. Vytiskni původní cenu (2 dp)", "starter":"", "expected_stdout": f"{(new/(1+p/100)):.2f}"})
    joins=[["Ahoj","jak","se","máš?"],["Dnes","je","pátek"],["Učíme","se","Python"],["Pohádky","nás","baví"]]
    for slova in joins: t9.append({"prompt": f"Sestav větu ze slov {slova} (mezera mezi slovy)", "starter":"", "expected_stdout": " ".join(slova)})
    tasks["9. třída"] = t9[:20]
    return tasks

it_tasks_by_level = build_it_tasks_by_level()

# --- IT: remap původních 1.–9. ročníků do 6.–9. podle náročnosti ---
IT_REMAP_TO_6_9 = {
    "6. třída": ["1. třída", "2. třída", "3. třída"],
    "7. třída": ["4. třída", "5. třída"],
    "8. třída": ["6. třída", "7. třída"],
    "9. třída": ["8. třída", "9. třída"],
}

def _remap_it_levels(notes_src: dict, tasks_src: dict):
    notes_dst, tasks_dst = {}, {}
    for dst, srcs in IT_REMAP_TO_6_9.items():
        merged_notes, merged_tasks = [], []
        for s in srcs:
            merged_notes.extend(notes_src.get(s, []))
            merged_tasks.extend(tasks_src.get(s, []))
        notes_dst[dst] = merged_notes
        tasks_dst[dst] = merged_tasks
    return notes_dst, tasks_dst

# postav kolabované mapy
_it_notes_6_9, _it_tasks_6_9 = _remap_it_levels(it_notes_by_level, it_tasks_by_level)

# v 1.–5. třídě IT skryj (prázdný seznam), v 6.–9. nahraď kolabovanými
for _g in [f"{i}. třída" for i in range(1, 6)]:
    it_tasks_by_level[_g] = []
for _g, _L in _it_tasks_6_9.items():
    it_tasks_by_level[_g] = _L
for _g, _L in _it_notes_6_9.items():
    it_notes_by_level[_g] = _L


# =========================
# Konstanty + session defaults
# =========================
TASKS_TO_REVEAL = 20
class_to_db_level = {f"{i}. třída": f"{i}. třída" for i in range(1,10)}
DEFAULTS = dict(
    game_started=False, tasks_solved_for_reveal=0, score=0, best_score=0,
    best_time=float('inf'), start_time=None, end_time=None, current_task=None,
    last_selected_fairytale=None, last_selected_class=None, last_selected_subject=None,
    revealed_tiles=[False]*20, tile_coords=[], feedback_message="", feedback_type="",
    final_report=None, history=[], show_full_fairytale=False, achievement_date=None,
    diploma_image_path=None, current_cjl_task=None, _it_index=0,
    _it_last_output="", _it_last_eval="", _cjl_index=0
)

# =========================
# ČJ úlohy (JSON)
# =========================

cjl_tasks_by_level = {}
cjl_path = find_file(
    "cjl_tasks.json",
    "/mnt/data/cjl_tasks.json",
    r"C:\Users\jb\Documents\pohadky_app\cjl_tasks.json",
)
if cjl_path:
    with open(cjl_path, "r", encoding="utf-8") as f:
        cjl_tasks_by_level = json.load(f)

# === ČJ témata a poznámky ===
CJL_TOPICS_BY_GRADE = {
    "1. třída": [
        "Vyber správnou slabiku (nejjednodušší slova)",
        "Doplň písmeno",
        "Spočítej slabiky",
        "Tvrdé a měkké čtení po d, t, n",
    ],
    "2. třída": [
        "Doplň y/ý po tvrdých souhláskách (h, ch, k, r, d, t, n)",
        "Doplň i/í po měkkých souhláskách (ž, š, č, ř, c, j, ď, ť, ň)",
    ],
    "3. třída": [
        "Vyjmenovaná slova po B",
        "Vyjmenovaná slova po L",
        "Vyjmenovaná slova po M",
        "Vyjmenovaná slova po P",
        "Vyjmenovaná slova po S",
        "Vyjmenovaná slova po V",
        "Vyjmenovaná slova po Z",
        "Vyjmenovaná slova – dohromady",
    ],
    "4. třída" : [
    "Slovní druhy - mix",                       # beze změny (bere vše z JSONu)
    "Určování pádu podstatných jmen",          # NOVÉ (bere prefixem z JSONu níže)
    "Slovní druhy ve větě (slovo)",            # generované věty, viz nový generator
    ],
    "5. třída": [
    "Určování základních větných členů",
    "Slovní druhy",
    "Určování základních větných členů: podmět, přísudek, přívlastek",
    "Shoda podmětu s přísudkem (i/y)",
    ],
    "6. třída" : [
        "Rod a životnost (podstatná jména)",
        "Vzor podstatného jména (m/ž/s)",
        "Sloveso: osoba, číslo, čas, způsob",
        "Souhrn – mix",
    ],
    "7. třída" : [
    "Slovotvorba: kořen, předpony, přípony",
    "Slova přejatá (řecká/latinská/jiná)",
    "Sloveso: mluvnické kategorie a vzory",
    "Ostatní větné členy (předmět / přísl. určení / doplněk)",
    "Skladba – věta hlavní × vedlejší",
    "Poměry mezi větami (spojovací / vylučovací / odporovací; souřadné × podřadné)",
    "Souhrn – mix",
    ],
     "8. třída": [
        "Určování větných členů",
        "Věta hlavní × věta vedlejší",
        "Druhy vedlejších vět",
        "Psaní čárek v souvětí",
        "Mix úloh",
    ],
    "9. třída" : [
    "Literární druhy a žánry",
    "Slohové postupy",
    "Figury a tropy",
    "Synonyma, antonyma, homonyma",
    "Mix úloh",
    "Celkové opakování",
    ]
}


cjl_notes_by_level = {
    "1. třída": [
        "Formát: vyber a), b) nebo c)."
    ],
    "2. třída": [
        "Po tvrdých píšeme y/ý: h, ch, k, r, d, t, n. Po měkkých píšeme i/í: ž, š, č, ř, c, j, ď, ť, ň.",
        "Pozor na d/t/n: měkké čteme v kombinacích di/ti/ni; dě/tě/ně; dí/tí/ní.",
    ],
    "3. třída": [
        "Doplňuj i/y/í/ý ve vyjmenovaných slovech a slovech příbuzných.",
        "Formát: výběr a/b/c (klikni na možnost)."
    ],
    "4. třída": [
    "Určuj slovní druhy (podstatná jména, slovesa, přídavná jména; občas i další – příslovce, číslovky ap.).",
    "Formát: výběr a/b/c (klikni na možnost)."
    ],
    "5. třída": [
    "Základní větné členy, rozšířené slovní druhy a shoda podmětu s přísudkem.",
    "Formát: výběr a/b/c (klikni na možnost)."
    ],
    "6. třída" : [
    "Podstatná jména: rod (m/ž/s), u mužského i životnost; vzory m/ž/s. Slovesa: osoba/číslo, čas, způsob.",
    "Formát: výběr a/b/c."
    ],
    "7. třída": [
    "Slovotvorba (kořen/předpona/přípona), přejatá slova, kategorie sloves, ostatní větné členy a skladba.",
    "Formát: 3 možnosti (a/b/c).",
    ],
    "8. třída" : [
    "Skladba: určujeme podmět, přísudek, předmět, přívlastek, příslovečná určení ap.",
    "VH × VV: VH stojí samostatně; VV bývá uvedena spojkou/záj. „že, aby, když, protože, ačkoli, který…“",
    "Druhy VV: podmětná, předmětná, přívlastková, příslovečná (časová, příčinná, účelová, podmínková, přípustková…).",
    "Čárky: před podřadicími spojkami, u vložených VV, u přístavků; pozor na souřadné vs. podřadné spojení."
    ]
}

# doplň k nim krátký tahák pro jednotlivá témata 3. třídy
CJL_TOPIC_NOTES_G3 = {
    "Vyjmenovaná slova po B": "Základ: být, bydlit, obyvatel, byt, příbytek, nábytek, dobytek, obyčej, bystrý, bylina, kobyla, býk, babyka a příbuzná slova.",
    "Vyjmenovaná slova po L": "Základ: slyšet, mlýn, blýskat se, polykat, plynout, plýtvat, vzlykat, lysý, lýko, lýtko, lyže, pelyněk, plyš a příbuzná slova.",
    "Vyjmenovaná slova po M": "Základ: my, mýt, myslit, mýlit se, hmyz, myš, hlemýžď, mýtit, zamykat, smýkat, dmýchat, chmýří, nachomýtnout se, mýto, mykat, mys, Litomyšl, sumýš a příbuzná slova.",
    "Vyjmenovaná slova po P": "Základ: pýcha, pytel, pysk, netopýr, slepýš, pyl, kopyto, klopýtat, třpytit se, zpytovat, pykat, pýr, pýří, pýřit se, čepýřit se a příbuzná slova.",
    "Vyjmenovaná slova po S": "Základ: syn, sytý, sýr, syrový, sychravý, usychat, sýkora, sýček, sysel, syčet, sypat a příbuzná slova.",
    "Vyjmenovaná slova po V": "Základ: vy/vý, vysoký, výt, výskat, zvykat, žvýkat, vydra, výr, vyžle, povyk, výheň a příbuzná slova.",
    "Vyjmenovaná slova po Z": "Základ: brzy, jazyk, nazývat (se), Ruzyně a příbuzná slova.",
}


CJL_TOPIC_NOTES_G4 = {
    "Slovní druhy - mix": "Procvičení všech slovních druhů dohromady.",
    "Určování pádu podstatných jmen": "1. (kdo? co?), 2. (koho? čeho?), 3. (komu? čemu?), 4. (koho? co?), 5. (oslovujeme), 6. (o kom? o čem?), 7. (s kým? s čím?).",
    "Slovní druhy ve větě (slovo)": "Určuj podle role slova ve *větě*; zvýrazněné slovo je uvedeno zvlášť v zadání.",
}

CJL_TOPIC_NOTES_G5 = {
    "Základní větné členy ve větách": "Podmět (kdo? co?), přísudek (co dělá? co se děje?), předmět, přísl. určení, přívlastek…",
    "Slovní druhy": "Trénujeme všech 9 slovních druhů: PJ, PřJ, Sl, Přsl, Čísl, Záj, Předl, Spoj, Část, Cit.",
    "Určování základních větných členů: podmět, přísudek, přívlastek": "Jen trojice: podmět × přísudek × přívlastek.",
    "Shoda podmětu s přísudkem (i/y)": "Mn. číslo m. životný → **-i** (chlapci přišli), ženský → **-y** (dívky přišly).",
}

CJL_TOPIC_NOTES_G6 = {
    "Rod a životnost (podstatná jména)": "Rod: mužský/ženský/střední; u mužského navíc životný × neživotný (např. „král“ životný, „hrad“ neživotný).",
    "Vzor podstatného jména (m/ž/s)": "m: pán, hrad, muž, stroj; ž: žena, růže, píseň, kost; s: město, moře, kuře, stavení.",
    "Sloveso: osoba, číslo, čas, způsob": "Osoba/číslo (jdu/jdeš/jde…); čas (minulý/přítomný/budoucí); způsob (oznamovací, rozkazovací, podmiňovací).",
    "Souhrn – mix (z JSONu)": "Směs z JSONu (shoda, pád/rod/vzor, osoby/časy, interpunkce…) + přidané 2. kolo.",
}

CJL_TOPIC_NOTES_G7 = {
    "Slovotvorba: kořen, předpony, přípony": "Kořen nese význam (přátel-), předpona (ne-, pře-, vy-…), přípona (-ský, -ík, -ka, -nout…).",
    "Slova přejatá (řecká/latinská/jiná)": "Př. řecké: demokracie, fyzika; latinské: centrum, maximum; jiný původ: špagety, džus, robot.",
    "Sloveso: mluvnické kategorie a vzory": "Osoba/číslo/čas/způsob/vid/rod (činný/trpný); vzory: nese, bere, maže, peče, umře, sází, prosí, trpí, tiskne, kryje.",
    "Ostatní větné členy (předmět / přísl. určení / doplněk)": "Předmět: „nesl hlavu“; Přísl. určení: „v noci“; Doplněk: „vrátil se unavený“.",
    "Skladba – věta hlavní × vedlejší": "Vedlejší bývá zavedená spojkami „že, aby, protože, když, který…“.",
    "Poměry mezi větami (…)" : "Spojovací (a), vylučovací (nebo), odporovací (ale); souvětí souřadné vs. podřadné.",
}
CJL_TOPIC_NOTES_G9 = {
    "Literární druhy a žánry": 
        "Druhy: lyrika / epika / drama. Žánry: báseň, balada, epos, povídka, novela, román, komedie, tragédie.\n\n"
        "**Mini-anotace:**\n"
        "• Krátký příběh s jedinou dějovou linií (pastýř najde prsten a rozhoduje se, zda ho vrátí) → **povídka (epika)**\n"
        "• Rozsáhlý básnický příběh o hrdinovi a nadlidských překážkách → **epos (epika)**\n"
        "• Lyrická výpověď o stesku a radosti z návratu Persefony → **báseň (lyrika)**\n"
        "• Temný příběh v poezii o vině a trestu → **balada (lyricko-epická)**\n"
        "• Text určený pro jeviště, konflikt postav → **drama (žánr dle provedení)**",
    "Slohové postupy": "Vyprávěcí × popisný × výkladový (případně úvahový). Poznávej podle účelu textu.",
    "Figury a tropy":
        "Tropy (metafora, metonymie, personifikace, hyperbola…) × figury (anafora, epizeuxis, inverze, enumerace, gradace…).\n\n"
        "**Mini-anotace/ukázky:**\n"
        "• „Hrdina je lev.“ → **metafora (trop)**\n"
        "• „Vypil jsem sklenici.“ (nádoba místo obsahu) → **metonymie (trop)**\n"
        "• „Moře se zasmálo.“ → **personifikace (trop)**\n"
        "• „Říkal jsem to tisíckrát!“ → **hyperbola (trop)**\n"
        "• „Běž, běž!“ → **epizeuxis (figura)**\n"
        "• „Kde domov můj, kde vlast má?“ → **anafora (figura)**\n"
        "• „Do boje kráčí Perseus.“ → **inverze (figura)**\n"
        "• „Přišel, viděl, zvítězil.“ → **enumerace/asyndeton (figura)**",
    "Synonyma, antonyma, homonyma": "Synonyma = podobný význam; antonyma = opačný; homonyma = stejný tvar, jiný význam.",
    "Mix úloh": "Bere přímo úlohy pro 9. třídu z JSONu.",
    "Celkové opakování (všechna témata ZŠ)": "Velký mix napříč všemi ročníky."
}

LIT_MINI = [
  {
    "anotace": "Krátký příběh s jedinou dějovou linií: pastýř najde ztracený prsten a rozhodne se, zda ho vrátí.",
    "spravna_odpoved": "žánr: povídka (druh: epika)"
  },
  {
    "anotace": "Rozsáhlý básnický příběh o hrdinovi, který překonává nadlidské překážky a putuje světem bohů a lidí.",
    "spravna_odpoved": "žánr: epos (druh: epika)"
  },
  {
    "anotace": "Krátká lyrická báseň: mluvčí vyjadřuje stesk po domově a radost z jarního návratu Persefony.",
    "spravna_odpoved": "žánr: báseň (druh: lyrika)"
  },
  {
    "anotace": "Příběh s ponurým vyzněním a tragickým pádem hrdiny zaslepeného pýchou (hybris).",
    "spravna_odpoved": "žánr: tragédie (druh: drama)"
  },
  {
    "anotace": "Vyprávění, kde chytrý hrdina oklame netvora; motivy zázračných pomocníků a kouzelných předmětů.",
    "spravna_odpoved": "žánr: pohádka (druh: epika)"
  },
  {
    "anotace": "Krátká próza s mravním ponaučením; zvířata mluví lidskou řečí a zrcadlí lidské vlastnosti.",
    "spravna_odpoved": "žánr: bajka (druh: epika)"
  },
  {
    "anotace": "Dramatický text s veselým vyústěním; nedorozumění a slovní hříčky přivádějí hrdiny do komických situací.",
    "spravna_odpoved": "žánr: komedie (druh: drama)"
  },
  {
    "anotace": "Prozaický útvar středního rozsahu – jedna rozhodující epizoda v životě hrdiny, sevřená kompozice.",
    "spravna_odpoved": "žánr: novela (druh: epika)"
  },
  {
    "anotace": "Rozsáhlý prozaický útvar se spletitými vztahy a více postavami, dlouhé časové období.",
    "spravna_odpoved": "žánr: román (druh: epika)"
  },
  {
    "anotace": "Baladické vyprávění v poezii – temný tón, vina a trest; hrdina nese následky svého činu.",
    "spravna_odpoved": "žánr: balada (druh: lyricko-epická báseň)"
  },
  {
    "anotace": "Krátký lyrický útvar – soustředěný obraz, zvukomalba, citová výpověď, bez dějové linky.",
    "spravna_odpoved": "druh: lyrika (žánr: lyrická báseň)"
  },
  {
    "anotace": "Text určený k jevištnímu provedení – dialogy, scénické poznámky, konflikt postav.",
    "spravna_odpoved": "druh: drama (žánr dle provedení – komedie/tragédie)"
  }
]

FIG_TROP_MINI = [
  {
    "ukazka": "Hrdina je lev.",
    "vysvetleni": "Přenesení významu na základě podobnosti.",
    "spravna_odpoved": "trop: metafora"
  },
  {
    "ukazka": "Vypil jsem sklenici.",
    "vysvetleni": "Záměna pojmenování na základě věcné souvislosti (nádoba × obsah).",
    "spravna_odpoved": "trop: metonymie"
  },
  {
    "ukazka": "Moře se zasmálo a vítr si zapískal.",
    "vysvetleni": "Neživému se připisují lidské vlastnosti/činnosti.",
    "spravna_odpoved": "trop: personifikace"
  },
  {
    "ukazka": "Říkal jsem to tisíckrát!",
    "vysvetleni": "Zveličení pro zdůraznění.",
    "spravna_odpoved": "trop: hyperbola"
  },
  {
    "ukazka": "Neviděl jsem ani nohu.",
    "vysvetleni": "Část označuje celek (nebo naopak).",
    "spravna_odpoved": "trop: synekdocha"
  },
  {
    "ukazka": "A bojoval, a běžel, a doufal…",
    "vysvetleni": "Opakování téhož spojovacího prostředku.",
    "spravna_odpoved": "figura: polysyndeton"
  },
  {
    "ukazka": "Přišel, viděl, zvítězil.",
    "vysvetleni": "Bezpříznakové řazení bez spojek.",
    "spravna_odpoved": "figura: asyndeton (též enumerace)"
  },
  {
    "ukazka": "Kde domov můj, kde vlast má?",
    "vysvetleni": "Opakování slov na začátku veršů/vět.",
    "spravna_odpoved": "figura: anafora"
  },
  {
    "ukazka": "Hrdina běží, běží proti bouři.",
    "vysvetleni": "Bezprostřední opakování téhož výrazu.",
    "spravna_odpoved": "figura: epizeuxis"
  },
  {
    "ukazka": "Do boje kráčí Perseus.",
    "vysvetleni": "Obrácený (netypický) slovosled pro zdůraznění.",
    "spravna_odpoved": "figura: inverze"
  },
  {
    "ukazka": "Pomalý krok, rychlejší dech, bouřlivé srdce.",
    "vysvetleni": "Stupňování (slabé → silné).",
    "spravna_odpoved": "figura: gradace"
  },
  {
    "ukazka": "Athéna chránila města: moudrost, řád, právo.",
    "vysvetleni": "Výčtový postup.",
    "spravna_odpoved": "figura: enumerace"
  }
]

# =========================
# MA úlohy (JSON)
# =========================
# — Jedno místo, kde mapuješ (třída, téma) na klíč v JSONu —
MA_JSON_TOPICS = {
    ("1. třída", "Množiny – základ"): "1. třída – množiny",
    ("2. třída", "Sudá/lichá v množině"): "2. třída – sudá/lichá",
    ("2. třída", "Násobky 2–9 – třídění do množin"): "2. třída – násobky",
    ("3. třída", "Venn – 2 množiny (čísla 1..20)"): "3. třída – Venn 2",
    ("4. třída", "Venn – 3 množiny (2/3/5)"): "4. třída – Venn 3",
    ("5. třída", "Inkluze–exkluze (2–3 množ.)"): "5. třída – Inkluze exkluze",
    ("5. třída", "Komplement, De Morgan"): "5. třída – De Morgan",
    ("6. třída", "Intervaly jako množiny"): "6. třída – Intervaly 1",
    ("6. třída", "Sjednocení/průnik intervalů"): "6. třída – Intervaly 2",
    ("7. třída", "Relace vs. funkce (A→B)"): "7. třída – Relace funkce",
    ("8. třída", "Obraz/předobraz množiny"): "8. třída – Obraz předobraz",
    ("9. třída", "Ekvivalence, třídy (mod n)"): "9. třída – Ekviv třídy",
}

def generate_diploma_pdf(username, score, time_s, fairytale_title,
                         achievement_date, level, subject_display,
                         topic_line, image_path,
                         crop_mode="auto"):
    pdf = FPDF(orientation='L', unit='mm', format='A4'); pdf.add_page()
    pw, ph = pdf.w, pdf.h
    try:
        pdf.add_font("DejaVuSans","", "DejaVuSansCondensed.ttf", uni=True)
        pdf.add_font("DejaVuSans","B","DejaVuSansCondensed.ttf", uni=True)
    except RuntimeError:
        pdf.set_font("Arial","",24)

    # pozadí – poloprůhledný obrázek s chytrým cropem
    if image_path and os.path.exists(image_path):
        original_img = _PILImage.open(image_path)
        iw, ih = original_img.size

        # horní půlka pro vybrané/přenastavené pohádky
        crop_top = (
            crop_mode == "top-half"
            or (crop_mode == "auto" and fairytale_title in {"Odysseus a Sirény", "Sisyfos","Theseus a Minotaurus", "Persefona a Hádes", "O Zlatovlásce", "O jednorožci a dráčkovi","Python","Orfeus a Eurydika" })
        )
        if crop_top:
            original_img = original_img.crop((0, 0, iw, ih // 2))
            iw, ih = original_img.size

        img_rgba = original_img.convert("RGBA")
        bg = _PILImage.new("RGBA", img_rgba.size, (255, 255, 255, 255))
        img_rgba.putalpha(128)
        final_bg = _PILImage.alpha_composite(bg, img_rgba)

        buf = io.BytesIO()
        final_bg.convert("RGB").save(buf, format="JPEG")
        buf.seek(0)

        # zvětšit na stránku se zachováním AR
        ar = iw / ih
        if pw / ph > ar:
            bw, bh = pw, pw / ar
        else:
            bh, bw = ph, ph * ar

        # pro top-half vypadá líp nahoře, jinak centrovat
        if crop_top:
            x = (pw - bw) / 2; y = 0
        else:
            x = (pw - bw) / 2; y = (ph - bh) / 2

        pdf.image(buf, x=x, y=y, w=bw, h=bh)

    # titulky
    pdf.set_font("DejaVuSans","",36)
    pdf.set_xy(10,30); pdf.cell(0,10,'Diplom',0,1,'C')
    pdf.set_font("DejaVuSans","",18); pdf.set_xy(10,50)
    pdf.cell(0,10, f'Tento diplom získává za skvělý výkon ve hře Pohádky s {subject_display}', 0, 1, 'C')
    pdf.set_font("DejaVuSans","B",48); pdf.set_xy(10,90); pdf.cell(0,10,username,0,1,'C')
    pdf.set_font("DejaVuSans","",16); pdf.set_xy(10,120)
    pdf.cell(0,10,f'za úspěšné vyřešení {score} úkolů v pohádce "{fairytale_title}"', 0, 1, 'C')
    # datum z achievement_date (pokud je), jinak nyní
    when = achievement_date.strftime("%d.%m.%Y %H:%M") if achievement_date else datetime.datetime.now().strftime("%d.%m.%Y %H:%M")
    pdf.set_xy(10,130); pdf.cell(0,10,f'Úroveň: {level} · Čas: {time_s:.2f} s · {when}', 0, 1, 'C')
    if topic_line:
        pdf.set_xy(10,142); pdf.cell(0,10,f'Téma: {topic_line}', 0, 1, 'C')

    return bytes(pdf.output(dest='S'))

# =========================
# Streamlit page
# =========================
st.set_page_config(page_title="Pohádky: MA / ČJ / IT", layout="wide")
st.title("🌟 Pohádky+")

# Init session state
for k, v in DEFAULTS.items():
    if k not in st.session_state:
        st.session_state[k] = v

# Sidebar
st.sidebar.title("📚 Volby")



tridy = [f"{i}. třída" for i in range(1,10)]
vyber_tridy = st.sidebar.selectbox("Vyberte úroveň", tridy, index=0)
subject = st.sidebar.radio("Předmět", options=["MA","ČJ","IT"], index=0, horizontal=True)

band = _grade_band(vyber_tridy)                       # "1-5" nebo "6-9"
catalog = STORY_LIBRARY.get(band, {})                 # správná knihovna
titles = list(catalog.keys()) or ["(zatím nic)"]      # titulky pro select
vyber = st.sidebar.selectbox("Vyberte příběh", titles, index=0)

# Reset při změně voleb
if (st.session_state.last_selected_fairytale != vyber
    or st.session_state.last_selected_class != vyber_tridy
    or st.session_state.last_selected_subject != subject):
    st.session_state.current_task = None
    st.session_state.last_selected_fairytale = vyber
    st.session_state.last_selected_class = vyber_tridy
    st.session_state.last_selected_subject = subject
    st.session_state.feedback_message = ""
    st.session_state.feedback_type = ""
    st.session_state.tasks_solved_for_reveal = 0
    st.session_state.start_time = None
    st.session_state.end_time = None
    st.session_state.final_report = None
    st.session_state.history = []
    st.session_state.game_started = False
    st.session_state.revealed_tiles = [False]*20
    st.session_state.tile_coords = []
    st.session_state.show_full_fairytale = False
    st.session_state.best_score = 0
    st.session_state.best_time = float('inf')
    st.session_state.current_cjl_task = None
    st.session_state._it_index = 0
    st.session_state._it_last_output = ""
    st.session_state._it_last_eval = ""
    st.session_state._cjl_index = 0
    st.session_state[f"topic_confirmed_{subject}_{vyber_tridy}"] = None
    st.rerun()

# Načti data pohádky + obrázek
band = _grade_band(vyber_tridy)
catalog = STORY_LIBRARY.get(band, {})
data = catalog.get(vyber, {})

text  = data.get("text", "")
moral = data.get("moral", "")



img_path_data = data.get("obrazek_path","")

image_path = None
base = os.path.splitext(img_path_data)[0] if img_path_data else ""
for ext in (".png",".jpg",".jpeg"):
    p = os.path.join("obrazky", base + ext)
    if p and os.path.exists(p):
        image_path = p
        break
st.session_state.diploma_image_path = image_path

# Nadpis → pak text (původní pořadí)
st.header(f"🧙 {vyber}")
if st.session_state.show_full_fairytale:
    st.markdown(text or "")
    if st.button("Skrýt celou pohádku"):
        st.session_state.show_full_fairytale=False; st.rerun()
else:
    prev = (text or "")[:300] + ("…" if text and len(text)>300 else "")
    st.markdown(prev)
    if st.button("Zobrazit celou pohádku"):
        st.session_state.show_full_fairytale=True; st.rerun()

st.markdown("---")
col_left, col_right = st.columns([1,1])

# =========================
# Téma – změna řádku "Vyber téma" resetuje hru.
# =========================

def topic_state_key(subject, grade):
    return f"topic_confirmed_{subject}_{grade}"

def render_topic_select(subject, grade):
    # dostupná témata
    if subject == "MA":
        opts = MA_TOPICS_BY_GRADE.get(grade, ["(bez tématu)"])
    elif subject == "ČJ":
        opts = CJL_TOPICS_BY_GRADE.get(grade, ["Doplň písmeno", "Spočítej slabiky"])
    elif subject == "IT":
        opts = IT_TOPICS_BY_GRADE.get(grade, ["(IT bez témat – úlohy podle ročníku)"])
    else:
        opts = ["(bez tématu)"]


    key_sel = f"sel_{subject}_{grade}"
    confirmed_key = topic_state_key(subject, grade)
    if st.session_state.get(confirmed_key) is None:
        st.session_state[confirmed_key] = opts[0]

    def _on_change():
        # potvrď nové téma
        st.session_state[confirmed_key] = st.session_state[key_sel]

        # reset hry při změně tématu
        st.session_state.game_started = False
        st.session_state.current_task = None
        st.session_state.current_cjl_task = None
        st.session_state.tasks_solved_for_reveal = 0
        st.session_state.revealed_tiles = [False]*TASKS_TO_REVEAL
        st.session_state.tile_coords = []
        st.session_state.start_time = None
        st.session_state.end_time = None
        st.session_state.final_report = None
        st.session_state.history = []
        st.session_state.feedback_message = ""
        st.session_state.feedback_type = ""
        st.session_state.show_full_fairytale = False

        # předvyplň „best“ pro nové téma (pokud používáš best_results)
        key_best = (subject, grade, st.session_state[confirmed_key])
        br = st.session_state.setdefault("best_results", {})
        best = br.get(key_best, {"score": 0, "time": float("inf")})
        st.session_state.best_score = best["score"]
        st.session_state.best_time = best["time"]

        
    st.selectbox(
        "Vyber téma:",
        options=opts,
        index=opts.index(st.session_state[confirmed_key]) if st.session_state[confirmed_key] in opts else 0,
        key=key_sel,
        on_change=_on_change
    )
    return st.session_state[confirmed_key]

def build_dynamic_notes(subject, grade, confirmed_topic):
    """Vrací seznam řádků k zobrazení v expanderu '📚 Poznámky' pro zvolené téma."""
    notes = []

    if subject == "MA":
        # Formát odpovědi + volitelné krátké hinty pro KONKRÉTNÍ téma
        fmt = MA_TOPIC_FORMAT.get(grade, {}).get(confirmed_topic, "celé číslo")
        notes.append(f"Téma: **{confirmed_topic}** · Formát odpovědi: **{fmt}**.")
        for line in MA_TOPIC_HINTS.get(grade, {}).get(confirmed_topic, []):
            notes.append(line)
        return notes

    elif subject == "ČJ":
        # Nadpis + obecná věta k ročníku (pokud existuje)
        notes.append(f"Téma: **{confirmed_topic}**.")
        base = cjl_notes_by_level.get(grade, [])
        if base:
            # zobraz celou sadu poznámek k ročníku (chceš-li jen první: notes.append(base[0]))
            notes.extend(base)

        # „taháky“ po ročnících (3.–9.) – pokud jsou nadefinované
        grade_to_var = {
            "3. třída": "CJL_TOPIC_NOTES_G3",
            "4. třída": "CJL_TOPIC_NOTES_G4",
            "5. třída": "CJL_TOPIC_NOTES_G5",
            "6. třída": "CJL_TOPIC_NOTES_G6",
            "7. třída": "CJL_TOPIC_NOTES_G7",
            "8. třída": "CJL_TOPIC_NOTES_G8",
            "9. třída": "CJL_TOPIC_NOTES_G9",
        }
        d = globals().get(grade_to_var.get(grade, ""), {})
        if isinstance(d, dict):
            extra = d.get(confirmed_topic)
            if extra:
                notes.append(extra)

        # 9. třída – mini-anotace (pokud máš helpery)
        if grade == "9. třída":
            try:
                if confirmed_topic == "Literární druhy a žánry":
                    notes.append("Mini-anotace:")
                    for x in _lit_items_normalized():
                        notes.append(f"{x['term']} – {x['note']}")
                elif confirmed_topic == "Figury a tropy":
                    notes.append("Mini-anotace:")
                    for x in _fig_items_normalized():
                        notes.append(f"{x['term']} – {x['note']}")
            except Exception:
                pass

        return notes

    else:
        notes = [f"Téma: **{confirmed_topic}**."]
        tnotes = IT_TOPIC_NOTES.get(grade, {}).get(confirmed_topic)
        if tnotes:
            notes.extend(tnotes)
        return notes


# =========================
# Generátory úloh – MA
# =========================
def generate_grade1_topic_problem(topic: str):
    topic = (topic or "").strip()
    if topic == "Počítání - do 10":
        op = random.choice(["+", "-"])
        if op == "+":
            a = random.randint(0, 10); b = random.randint(0, 10 - a)
        else:
            a = random.randint(0, 10); b = random.randint(0, a)
        q = f"${a} {op} {b}$"; ans = str(eval(f"{a}{op}{b}"))
        return q, ans, "int", None
    if topic == "Počítání - do 20 s přechodem přes 10":
        if random.random() < 0.5:
            a = random.randint(6, 10); b = random.randint(11 - a, 20 - a)
            q = f"${a} + {b}$"; ans = str(a + b)
        else:
            a = random.randint(12, 20); b = random.randint(1, a - 10)
            q = f"${a} - {b}$"; ans = str(a - b)
        return q, ans, "int", None
    # fallback pro „Množiny – základ“, kdyby JSON nebyl
    if random.random() < 0.5:
        n = random.randint(3, 6); elems = random.sample(range(1, 10), n)
        q = "Spočítej počet prvků množiny $A=\\{" + ", ".join(map(str, elems)) + "\\}$."
        return q, str(n), "int", None
    else:
        elems = sorted(random.sample(range(1, 12), random.randint(3, 6)))
        x = random.randint(0, 13)
        q = f"Patří číslo **{x}** do množiny $A=\\{{{', '.join(map(str, elems))}\\}}$? Odpověz **ano/ne**."
        ans = "ano" if x in elems else "ne"
        return q, ans, "yn", None

def generate_math_problem(level: str):
    lvl = (level or "").strip()
    if lvl == "1. třída":
        a = random.randint(0, 20); b = random.randint(0, 20)
        if b > a: a, b = b, a
        return f"${a} - {b}$", str(a - b), "int", None
    a = random.randint(10, 50); b = random.randint(10, 50)
    return f"${a} + {b}$", str(a + b), "int", None

# --- 2. třída: témata navázaná na úlohy ---
def generate_grade2_topic_problem(topic: str):
    t = (topic or "").strip().lower()

    # 2. třída – Sčítání / odčítání do 100
    if "sčítání" in t or "odčítání" in t:
        op = random.choice(["+", "-"])
        if op == "+":
            a = random.randint(0, 100)
            b = random.randint(0, 100 - a)  # aby nepřesáhlo 100
        else:
            a = random.randint(0, 100)
            b = random.randint(0, a)        # aby bylo nezáporné
        q = f"${a} \\, {op} \\, {b}$"
        ans = str(eval(f"{a}{op}{b}"))
        return q, ans, "int", None

    # 2. třída – Malá násobilka 2–9
    if "násobilka" in t:
        a = random.randint(2, 9)
        b = random.randint(2, 9)
        q = f"${a} \\times {b}$"
        ans = str(a * b)
        return q, ans, "int", None

    # Fallback pro neznámé téma: bezpečná volba do 100
    a = random.randint(0, 100)
    b = random.randint(0, 100 - a)
    q = f"${a} + {b}$"
    return q, str(a + b), "int", None

# --- 3. třída: témata navázaná na úlohy ---
def generate_grade3_sets_problem(topic: str):
    t = (topic or "").lower()
    if "množiny" in t and "1..20" in t:
        U = list(range(1, 21))
        A = [x for x in U if x % 2 == 0]      # sudá
        B = [x for x in U if x % 3 == 0]      # násobky 3
        q = "Nechť A= {sudá ≤20}, B= {násobky 3 ≤20}. Kolik prvků má **A ∩ B**?"
        ans = str(len(set(A).intersection(B)))
        return q, ans, "int", None
    # fallback
    return None

def generate_grade3_topic_problem(topic: str):
    t = (topic or "").strip().lower()

    # 3. třída – množiny (počty prvků)
    if "množiny" in t and "1..20" in t:
        U = list(range(1, 21))
        # definice A, B jako číselné vlastnosti (lze rozšiřovat)
        A = {x for x in U if x % 2 == 0}       # sudá
        B = {x for x in U if x % 3 == 0}       # násobky 3
        kind = random.choice(["A∩B", "A∪B", "A\\B"])
        if kind == "A∩B":
            q = "U={1..20}, A=sudá, B=násobky 3. Kolik prvků má **A ∩ B**?"
            ans = str(len(A & B))
        elif kind == "A∪B":
            q = "U={1..20}, A=sudá, B=násobky 3. Kolik prvků má **A ∪ B**?"
            ans = str(len(A | B))
        else:
            q = "U={1..20}, A=sudá, B=násobky 3. Kolik prvků má **A \\ B**?"
            ans = str(len(A - B))
    return q, ans, "int", None

    # 3. třída – Sčítání/odčítání do 1000
    if "sčítání" in t or "odčítání" in t or "1000" in t:
        op = random.choice(["+", "-"])
        if op == "+":
            a = random.randint(0, 1000)
            b = random.randint(0, 1000 - a)  # aby součet nepřesáhl 1000
        else:
            a = random.randint(0, 1000)
            b = random.randint(0, a)          # aby výsledek nebyl záporný
        q = f"${a} \\, {op} \\, {b}$"
        ans = str(eval(f"{a}{op}{b}"))
        # typ "int" = krátká číselná odpověď
        return q, ans, "int", None

    # 3. třída – Dělení se zbytkem
    if "dělení" in t or "zbytkem" in t:
        # dělitel 2–9, dělenec 0–1000
        divisor = random.randint(2, 9)
        dividend = random.randint(0, 1000)
        quotient, remainder = divmod(dividend, divisor)
        q = f"${dividend} : {divisor}$"
        # kanonický formát odpovědi (viz poznámky): "podíl zb. zbytek"
        ans = f"{quotient} zb. {remainder}"
        explain = f"Dělení {dividend} : {divisor} = {quotient} se zbytkem {remainder}."
        # typ "text" = porovnání textové odpovědi (viz níže normalizace)
        return q, ans, "text", explain

    # Fallback (kdyby přišlo neznámé téma): bezpečné sčítání do 1000
    a = random.randint(0, 1000); b = random.randint(0, 1000 - a)
    return f"${a} + {b}$", str(a + b), "int", None


# --- 4. třída: témata navázaná na úlohy ---
def generate_grade4_topic_problem(topic: str):
    t = (topic or "").strip().lower()

    if "kartézský" in t or "součin" in t:
        m = random.randint(2, 12)
        n = random.randint(2, 12)
        q = f"Měj |A|={m}, |B|={n}. Kolik prvků má **A×B**?"
        return q, str(m*n), "int", None

    # Násobení vícecifernými čísly (výsledek celé číslo)
    if "násobení" in t:
        a = random.randint(12, 999)   # víceciferné
        b = random.randint(2, 99)     # 1–2 cifry pro rozumnou obtížnost
        q = f"${a} \\times {b}$"
        ans = str(a * b)
        return q, ans, "int", None

    # Dělení vícecifernými čísly (bez zbytku → celé číslo)
    if "dělení" in t:
        divisor  = random.randint(12, 99)    # 2ciferný dělitel
        quotient = random.randint(10, 999)   # 2–3ciferný podíl
        dividend = divisor * quotient        # beze zbytku => celé číslo
        q = f"${dividend} : {divisor}$"
        ans = str(quotient)
        return q, ans, "int", None

    # Zaokrouhlování (na desítky / stovky → celé číslo)
    if "zaokrouhl" in t:
        base = random.choice([10, 100])     # 4. třída: desítky, stovky
        n = random.randint(10, 9999)
        rounded = _round_to(n, base)
        jednotka = "desítky" if base == 10 else "stovky"
        q = f"Zaokrouhli číslo **{n}** na **{jednotka}**."
        ans = str(rounded)
        return q, ans, "int", None

    # Fallback: bezpečné násobení
    a = random.randint(12, 999)
    b = random.randint(2, 99)
    return f"${a} \\times {b}$", str(a*b), "int", None

# --- 5. třída: témata navázaná na úlohy ---
def _fmt2(n):  # helper: na dvě desetinná místa jako string
    return f"{n:.2f}"

def generate_grade5_topic_problem(topic: str):
    t = (topic or "").strip().lower()

    if "inkluz" in t or "exkluz" in t or "∪" in t:
        # 2 množiny (bez pasti): zajisti konzistenci
        a = random.randint(6, 20)
        b = random.randint(6, 20)
        inter = random.randint(0, min(a, b) - 1)
        q = f"Je dáno |A|={a}, |B|={b}, |A∩B|={inter}. Urči **|A∪B|**."
        ans = str(a + b - inter)
        return q, ans, "int", None

    # Desetinná čísla (sčítání/odčítání, výsledek na 2 des. místa)
    if "desetinn" in t:
        # generujeme v "centech", ať je výsledek přesný a formátovatelný
        a = random.randint(0, 20000)   # 0.00–200.00
        b = random.randint(0, 20000)
        op = random.choice(["+", "-"])
        if op == "-":
            # pro nezáporný výsledek
            a, b = max(a, b), min(a, b)
        if op == "+":
            res = a + b
            q = f"${_fmt2(a/100)} + {_fmt2(b/100)}$"
        else:
            res = a - b
            q = f"${_fmt2(a/100)} - {_fmt2(b/100)}$"
        ans = _fmt2(res/100)           # string s přesně dvěma des. místy
        return q, ans, "decimal_2dp", None

    # Zlomky: krácení – zadej výsledek zkráceně a/b
    if "zlomky" in t and "krácen" in t:
        # vytvoř zlomek, který určitě půjde krátit
        k = random.randint(2, 12)          # společný dělitel
        a = random.randint(1, 12) * k
        b = random.randint(1, 12) * k
        from math import gcd
        g = gcd(a, b)
        # pro jistotu, kdyby náhodou g==1 (nemělo by nastat), přegeneruj b
        if g == 1:
            b *= random.randint(2, 5)
            g = gcd(a, b)
        q = f"Zkrať zlomek **{a}/{b}** na základní tvar."
        ans = f"{a//g}/{b//g}"             # kanonická správná odpověď
        return q, ans, "text", None

    # Zlomky: porovnání – odpověz jedním znakem <, >, =
    if "zlomky" in t and "porovn" in t:
        a = random.randint(1, 12); b = random.randint(1, 12)
        c = random.randint(1, 12); d = random.randint(1, 12)
        # občas vygeneruj rovnost
        if random.random() < 0.15:
            # nastav c/d = a/b
            k = random.randint(1, 9)
            c, d = a * k, b * k
        left = a * d
        right = b * c
        if left < right:   sign = "<"
        elif left > right: sign = ">"
        else:              sign = "="
        q = f"Porovnej zlomky **{a}/{b}** a **{c}/{d}**. Napiš `<`, `>` nebo `=`."
        ans = sign
        return q, ans, "text", None

    # Fallback: bezpečné desetinné sčítání
    a = random.randint(0, 20000); b = random.randint(0, 20000)
    return f"${_fmt2(a/100)} + {_fmt2(b/100)}$", _fmt2((a+b)/100), "decimal_2dp", None

from math import gcd

def _lcm(a: int, b: int) -> int:
    return abs(a*b) // gcd(a, b)

def _prime_factors(n: int):
    """Rozklad n>1 na prvočinitele (vzestupně)."""
    f = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            f.append(d)
            n //= d
        d += 1 if d == 2 else 2  # po 2 zkoušej jen lichá
    if n > 1:
        f.append(n)
    return f

def _gen_composite():
    """Zaručeně složené číslo ~ 30–999 (snadno faktorizovatelné)."""
    import random
    primes = [2,3,5,7,11,13]
    k = random.randint(2, 4)
    n = 1
    for _ in range(k):
        n *= random.choice(primes)
    return n

def _simplify_frac(a: int, b: int) -> str:
    g = gcd(a, b)
    return f"{a//g}/{b//g}"

# --- 6. třída: Rozklad na prvočinitele; NSD/NSN; Procenta; Zlomky se stejným jmenovatelem
def generate_grade6_topic_problem(topic: str):
    t = (topic or "").strip().lower()

    # Rozklad na prvočinitele
    if "rozklad" in t or "prvočinitel" in t:
        n = _gen_composite()
        fac = _prime_factors(n)
        # formát "2·2·3" (bez mezer; shodné s poznámkou)
        ans = "·".join(str(x) for x in fac)
        q = f"Rozlož číslo **{n}** na prvočinitele (např. `2·2·3`)."
        return q, ans, "text", None

    # NSD a NSN: náhodně se ptáme na jedno nebo druhé
    if "nsd" in t or "nsn" in t:
        import random
        a = random.randint(12, 120)
        b = random.randint(12, 120)
        ask_nsd = random.choice([True, False])
        if "nsd" in t and "nsn" not in t:
            ask_nsd = True
        if "nsn" in t and "nsd" not in t:
            ask_nsd = False

        if ask_nsd:
            q = f"Vypočti **NSD({a}, {b})**."
            ans = str(gcd(a, b))
        else:
            q = f"Vypočti **NSN({a}, {b})**."
            ans = str(_lcm(a, b))
        return q, ans, "int", None

    # Procenta: kolik je p % z N (výsledek na 2 des. místa)
    if "procent" in t:
        import random
        p = random.choice([5,10,12.5,15,20,25,30,35,40,50])
        N = random.randint(40, 500)
        val = round(N * (p/100), 2)
        q = f"Kolik je **{p}%** z **{N}**? (na 2 des. místa)"
        # odpověď jako string s 2 des. místy, ale kontrola už má numeric normalizaci
        ans = f"{val:.2f}"
        return q, ans, "decimal_2dp", None

    # Zlomky se stejným jmenovatelem: sčítání/odečítání, výsledek zkráceně a/b
    if "zlomky" in t and ("jmenovatel" in t or "stejn" in t):
        import random
        d = random.randint(3, 12)
        a = random.randint(1, d-1)
        b = random.randint(1, d-1)
        op = random.choice(["+", "-"])
        if op == "-" and a < b:
            a, b = b, a
        num = a + b if op == "+" else a - b
        q = f"Vypočti **{a}/{d} {op} {b}/{d}** a výsledek napiš **zkráceně a/b**."
        ans = _simplify_frac(num, d)  # textový tvar a/b
        return q, ans, "text", None

    # Fallback: jednoduché procento
    p, N = 10, 100
    return f"Kolik je **{p}%** z **{N}**?", f"{N*p/100:.2f}", "decimal_2dp", None

# --- 7. třída: Celá čísla; Lineární rovnice (základ); Poměr a úměrnost ---

def _fmt_int(n: int) -> str:
    return f"({n})" if n < 0 else str(n)

def generate_grade7_topic_problem(topic: str):
    t = (topic or "").strip().lower()

    if "kartézský" in t or "mřížka" in t or "mrizka" in t:
        m = random.randint(3, 15)  # počet x-ových hodnot
        n = random.randint(3, 15)  # počet y-ových hodnot
        q = f"Kolik bodů má mřížka se souřadnicemi x∈{{1..{m}}}, y∈{{1..{n}}}? (počet prvků A×B)"
        return q, str(m*n), "int", None

    # Celá čísla – sčítání/odčítání/násobení se zápornými
    if "celá" in t or "cela" in t:
        import random
        op = random.choice(["+", "-", "×"])
        a = random.randint(-30, 30)
        b = random.randint(-30, 30)
        if a == 0 and b == 0:
            b = 5
        if op == "+":
            ans = a + b
            expr = f"{_fmt_int(a)} + {_fmt_int(b)}"
        elif op == "-":
            ans = a - b
            expr = f"{_fmt_int(a)} - {_fmt_int(b)}"
        else:  # násobení
            ans = a * b
            expr = f"{_fmt_int(a)} \\times {_fmt_int(b)}"
        q = f"${expr}$"
        return q, str(ans), "int", None

    # Lineární rovnice (základ) – ax + b = c, řešení může být i desetinné
    if "rovnice" in t:
        import random
        # s pravděpodobností 1/2 celočíselné x, jinak racionální s koncem (2,4,5,10)
        if random.random() < 0.5:
            x_true = random.randint(-20, 20)
            d = 1
        else:
            d = random.choice([2, 4, 5, 10])
            num = random.randint(-40, 40)
            x_true = num / d  # např. 7/5 → 1.4

        # zvol a,b tak, aby c vyšlo celé (a dělitelné d)
        a = random.choice([k for k in range(-9, 10) if k != 0 and k % d == 0])
        b = random.randint(-30, 30)
        c = int(a * x_true + b)  # bude celé

        sign_b = "+" if b >= 0 else "-"
        q = f"Vyřeš rovnici: ${a}x \\, {sign_b} \\, {abs(b)} = {c}$"
        # správnou odpověď dáme na 2 desetinná místa (vyhodnocení má numeric normalizaci)
        ans = f"{x_true:.2f}"
        return q, ans, "decimal_2dp", None

    # Poměr a úměrnost – zkrať poměr a : b
    if "poměr" in t or "pomer" in t or "úměrnost" in t or "uměrnost" in t:
        from math import gcd
        import random
        k = random.randint(2, 12)
        a = random.randint(1, 20) * k
        b = random.randint(1, 20) * k
        g = gcd(a, b)
        q = f"Zkrať poměr **{a} : {b}** na základní tvar."
        ans = f"{a//g} : {b//g}"
        # typ 'ratio' – app ho umí zpracovat (parsování a/b normalizovaně)
        return q, ans, "ratio", None

    # Fallback: celá čísla
    a = random.randint(-20, 20); b = random.randint(-20, 20)
    return f"${_fmt_int(a)} + {_fmt_int(b)}$", str(a + b), "int", None

def generate_grade8_topic_problem(topic: str):
    t = (topic or "").strip().lower()

    # --- Mocniny a odmocniny ---
    if "mocnin" in t or "odmocnin" in t:
        # náhodně vyber podtému: "mocnina" (int) / "odmocnina" (2 dp)
        if random.random() < 0.5:
            # mocnina (celé číslo)
            a = random.randint(2, 25)
            power = random.choice([2, 3])  # druhá/třetí mocnina
            q = f"Vypočti: ${a}^{power}$"
            ans = str(a ** power)
            return q, ans, "int", None
        else:
            # odmocnina (na 2 dp)
            n = random.randint(10, 500)
            root = math.sqrt(n)
            q = f"Vypočti: $\\sqrt{{{n}}}$ (na 2 desetinná místa)"
            ans = f"{root:.2f}"
            return q, ans, "decimal_2dp", None

    # --- Pythagorova věta (přepona z odvěsen) ---
    if "pythagor" in t:
        a = random.randint(3, 30)
        b = random.randint(3, 30)
        c = math.sqrt(a*a + b*b)
        q = f"Pravouhlý trojúhelník má odvěsny **{a}** a **{b}**. Urči délku přepony **c** (na 2 desetinná místa)."
        ans = f"{c:.2f}"
        return q, ans, "decimal_2dp", None

    # --- Kruh: obvod / obsah ---
    if "kruh" in t:
        r = random.randint(2, 30)
        if random.random() < 0.5:
            # obvod
            L = 2 * math.pi * r
            q = f"Vypočti **obvod** kruhu o poloměru **r = {r}** (na 2 desetinná místa)."
            ans = f"{L:.2f}"
        else:
            # obsah
            S = math.pi * r * r
            q = f"Vypočti **obsah** kruhu o poloměru **r = {r}** (na 2 desetinná místa)."
            ans = f"{S:.2f}"
        return q, ans, "decimal_2dp", None

    # --- Fallback: bezpečná odmocnina na 2 dp ---
    n = random.randint(10, 500)
    return f"Vypočti: $\\sqrt{{{n}}}$ (na 2 desetinná místa)", f"{math.sqrt(n):.2f}", "decimal_2dp", None

def generate_grade9_topic_problem(topic: str):
    t = (topic or "").strip().lower()

    if "mocnina" in t or "2^" in t or "2²" in t:
        n = random.randint(1, 12)
        q = f"Kolik podmnožin má množina s **n={n}** prvky?"
        return q, str(2**n), "int", None


    # — Rovnice (obecněji): ax + b = cx + d  → x na 2 desetinná místa
    if "rovnic" in t and "x^2" not in t and "x²" not in t:
        # zvolíme tak, aby a != c
        a = random.randint(-9, 9) or 1
        c = random.randint(-9, 9) or -1
        if a == c:
            c += 1
        b = random.randint(-30, 30)
        d = random.randint(-30, 30)
        # (a - c) x = d - b
        denom = (a - c)
        x = (d - b) / denom
        q = f"Vyřeš rovnici: ${a}x \\, + \\, {b} = {c}x \\, + \\, {d}$"
        ans = f"{x:.2f}"
        return q, ans, "decimal_2dp", None

    # — Kvadratické rovnice x² = a  → uveď nezáporné řešení (2 dp)
    if "x^2" in t or "x²" in t:
        a = random.randint(1, 400)
        x = math.sqrt(a)
        q = f"Vyřeš rovnici **x² = {a}**. Uveď **nezáporné** řešení x (na 2 desetinná místa)."
        ans = f"{x:.2f}"
        return q, ans, "decimal_2dp", None

    # — Statistika (průměr / medián)  → 2 dp
    if "statistik" in t:
        nums = sorted([random.randint(-20, 60) for _ in range(random.choice([5,7,9]))])
        if random.random() < 0.5:
            # průměr
            mean = sum(nums) / len(nums)
            q = "Spočti **aritmetický průměr** čísel: " + ", ".join(map(str, nums)) + " (na 2 desetinná místa)."
            ans = f"{mean:.2f}"
        else:
            # medián (lichý počet prvků)
            mid = len(nums)//2
            median = nums[mid]
            q = "Urči **medián** čísel: " + ", ".join(map(str, nums)) + " (na 2 desetinná místa)."
            ans = f"{median:.2f}"
        return q, ans, "decimal_2dp", None

    # — Procenta / finance (zvýšení/snížení ceny)  → 2 dp
    if "procent" in t or "finance" in t:
        price = random.randint(200, 5000)
        rate = random.choice([5, 7.5, 10, 12.5, 15, 20, 25, 30])
        inc = random.choice([True, False])
        new_price = price * (1 + rate/100) if inc else price * (1 - rate/100)
        op = "zvýší" if inc else "sníží"
        q = f"Cena **{price} Kč** se {op} o **{rate}%**. Jaká bude **nová cena**? (na 2 desetinná místa)"
        ans = f"{new_price:.2f}"
        return q, ans, "decimal_2dp", None

    # Fallback: jednoduché procento
    N = random.randint(100, 900)
    p = random.choice([10, 12.5, 20, 25])
    return f"Kolik je **{p}%** z **{N}**? (na 2 desetinná místa)", f"{N*(p/100):.2f}", "decimal_2dp", None

# Mapování třídy → topic-generator (lze dál rozšiřovat)
MA_TOPIC_GENERATORS = {
    "1. třída": generate_grade1_topic_problem,
    "2. třída": generate_grade2_topic_problem,
    "3. třída": generate_grade3_topic_problem,
    "4. třída": generate_grade4_topic_problem,
    "5. třída": generate_grade5_topic_problem,
    "6. třída": generate_grade6_topic_problem,
    "7. třída": generate_grade7_topic_problem, 
    "8. třída": generate_grade8_topic_problem, 
    "9. třída": generate_grade9_topic_problem, # ⬅️ nově
    # ...
}
# =========================
# UI – levý/pr pravý sloupec
# =========================
with col_left:
    st.markdown("### 📘 Téma")
    confirmed_topic = render_topic_select(subject, vyber_tridy)

    # Poznámky (jen relevantní k tématu)
    notes = build_dynamic_notes(subject, vyber_tridy, confirmed_topic)
    if notes:
        with st.expander("📚 Poznámky"):
            for p in notes: st.markdown(f"- {p}")

    st.subheader("🧩 Úkoly")

    # Start hry / příprava dlaždic
    def prepare_tiles():
        if image_path and os.path.exists(image_path):
            img = _PILImage.open(image_path)
            w,h = img.size; tw,th = w//5, h//4
            st.session_state.tile_coords = [(c*tw, r*th, (c+1)*tw, (r+1)*th) for r in range(4) for c in range(5)]
        else:
            st.session_state.tile_coords = []

    if not st.session_state.get("game_started", False):
        st.info(f"Vyřešte {TASKS_TO_REVEAL} úkolů a odhalte obrázek!")
        if st.button("Začít novou hru", key="btn_new_game_top"):
            start_new_game()  # nastaví stavy, prepare_tiles(), st.rerun()
    else:
        if st.session_state.tasks_solved_for_reveal < TASKS_TO_REVEAL:
            

            # ————— MA —————
            if subject == "MA":
                # 1) Bezpečná inicializace slotu v session state
                if "current_task" not in st.session_state:
                    st.session_state.current_task = None

                # 2) Když není úloha připravená, vygeneruj ji podle třídy a tématu
                if st.session_state.current_task is None:
                    gen = globals().get("MA_TOPIC_GENERATORS", {}).get(vyber_tridy)
                    # 1) Zkus JSON blok dle mapy
                    json_key = MA_JSON_TOPICS.get((vyber_tridy, confirmed_topic))
                    if json_key:
                        tset = get_sets_block(vyber_tridy, json_key)  # uvnitř zkusí načíst z ma_tasks_sets.json
                        picked = pick_json_task(tset) if isinstance(tset, list) and tset else None
                        if picked:
                            st.session_state.current_task = picked
                        else:
                            # fallback na generator, pokud by byl blok prázdný
                            st.session_state.current_task = gen(confirmed_topic) if gen else generate_math_problem(vyber_tridy)
                    else:
                        # 2) Jinak běžným generátorem
                        st.session_state.current_task = gen(confirmed_topic) if gen else generate_math_problem(vyber_tridy)

                # 3) TEĎ teprve čti ct – bude jistě existovat (None nebo úloha)
                ct = st.session_state.current_task
                          
                  
                      
                # MCQ (z JSONu)
                if isinstance(ct, (tuple, list)) and len(ct) == 4 and ct[0] == "__MA_MCQ__":
                    _, norm, _, _ = ct
                    with st.form("ma_mcq_form", clear_on_submit=False):
                        c1, c2 = st.columns([4,1])
                        with c1: st.markdown(f"#### ✏️ {norm['text']}")
                        with c2: st.markdown(f"🏅 **Skóre:** {st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL}")
                        letters = ["a","b","c","d"][:len(norm["options"])]
                        choice = st.radio("Vyber odpověď:", options=letters, index=None,
                                          format_func=lambda x: norm["options"][ord(x)-97],
                                          key=f"ma_mcq_{hash(norm['text'])%10**8}")
                        ok = st.form_submit_button("Odeslat")
                    if st.session_state.feedback_message:
                        (st.success if st.session_state.feedback_type=="success" else st.error)(st.session_state.feedback_message)
                    if ok:
                        corr = norm["correct"]
                        if choice is None:
                            st.warning("Než odešleš, vyber prosím jednu možnost.")
                        else:
                            chosen_text = norm["options"][ord(choice)-97]
                            corr_text   = norm["options"][ord(corr)-97] if corr in ["a","b","c","d"] else "(neznámé)"
                            if choice == corr:
                                st.session_state.feedback_message = "Správně! 🎉"; st.session_state.feedback_type = "success"
                                st.session_state.tasks_solved_for_reveal += 1
                                st.session_state.history.append((norm["text"], chosen_text, corr_text, "✅ správně"))
                                idxs = [i for i,r in enumerate(st.session_state.revealed_tiles) if not r]
                                if idxs: st.session_state.revealed_tiles[random.choice(idxs)] = True
                            else:
                                st.session_state.feedback_message = f"Nesprávně. ❌ Správná odpověď byla: {corr_text}"
                                st.session_state.feedback_type = "error"
                                st.session_state.history.append((norm["text"], chosen_text, corr_text, "❌ špatně"))
                            st.session_state.current_task = None
                            st.rerun()
                else:
                    # Klasické krátké odpovědi
                    question, correct_answer, problem_type, explain = ensure_task4(ct)
                    with st.form("math_form", clear_on_submit=True):
                        c1,c2 = st.columns([4,1])
                        with c1:
                            st.markdown(f"#### ✏️ {question}")
                            if problem_type == "div_remainder":
                                st.caption("💡 Formát: `podíl zb. zbytek` (např. `5 zb. 2`).")
                            elif problem_type in ["decimal_2dp","decimal_2dp_number_only","decimal_or_int"]:
                                st.caption("💡 Zapiš na 2 desetinná místa. Tečka i čárka jsou povoleny.")
                            elif problem_type == "fraction_reduced":
                                st.caption("💡 Zlomky ve zkráceném tvaru `čitatel/jmenovatel`.")
                            elif problem_type == "ratio":
                                st.caption("💡 Poměr zapisuj `a : b` ve zkráceném tvaru.")
                            elif problem_type == "yn":
                                st.caption("💡 Odpověz **ano** nebo **ne**.")
                        with c2:
                            st.markdown(f"🏅 **Skóre:** {st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL}")
                        if problem_type == "yn":
                            ans = st.radio("Vyber:", ["ano","ne"], index=0, horizontal=True, key="yn_choice")
                        else:
                            ans = st.text_input("Tvoje odpověď:", key="math_answer_input",
                                                label_visibility="collapsed", placeholder="Sem napiš svou odpověď…")
                        ok = st.form_submit_button("Odeslat")
                    if st.session_state.feedback_message:
                        (st.success if st.session_state.feedback_type=="success" else st.error)(st.session_state.feedback_message)
                    if ok:
                        is_correct = False
                        user_disp = ans
                        corr_disp = correct_answer if not isinstance(correct_answer, tuple) else " nebo ".join(correct_answer)
                        try:
                            if problem_type == "int":
                                val = parse_int_answer(ans)
                                corr = parse_int_answer(str(correct_answer))
                                is_correct = (val is not None and corr is not None and val == corr)

                            elif problem_type == "float":
                                val = parse_float_answer(ans, decimals=2)
                                corr = parse_float_answer(str(correct_answer), decimals=2)
                                is_correct = (val is not None and corr is not None and abs(val - corr) < 1e-9)

                            elif problem_type == "div_remainder":
                                uq, ur = parse_div_remainder(ans); cq, cr = parse_div_remainder(correct_answer)
                                is_correct = (uq == cq and ur == cr)

                            elif problem_type in ["decimal_2dp","decimal_2dp_number_only","decimal_or_int"]:
                                u = normalize_decimal(ans); c = float(str(correct_answer).replace(",", "."))
                                is_correct = approx_equal(u, c, 1e-2)

                            elif problem_type == "fraction_reduced":
                                is_correct = fraction_equal_reduced(ans, correct_answer)

                            elif problem_type == "ratio":
                                ua, ub = parse_ratio(ans); ca, cb = parse_ratio(correct_answer)
                                is_correct = (ua == ca and ub == cb)

                            elif problem_type == "pfactors":
                                target_n = int(str(correct_answer).strip())
                                is_correct = pf_equal(ans, target_n)

                            elif problem_type == "yn":
                                is_correct = (normalize_yes_no(ans) == correct_answer)

                            else:  # "text" a jiné
                                is_correct = (str(ans).strip() == str(correct_answer).strip())

                        except Exception:
                            is_correct = False

                        # ... zbytek tvého feedbacku / historie / odhalení dlaždice beze změn

                        if is_correct:
                            st.session_state.feedback_message = "Správně! 🎉"; st.session_state.feedback_type="success"
                            st.session_state.tasks_solved_for_reveal += 1
                            st.session_state.history.append((question, user_disp if user_disp!="" else "—", corr_disp, "✅ správně"))
                            idxs = [i for i,r in enumerate(st.session_state.revealed_tiles) if not r]
                            if idxs: st.session_state.revealed_tiles[random.choice(idxs)] = True
                        else:
                            extra = f"  \nℹ️ Vysvětlení: {explain}" if explain else ""
                            st.session_state.feedback_message = f"Nesprávně. ❌ Správná odpověď: {corr_disp}.{extra}"
                            st.session_state.feedback_type="error"
                            st.session_state.history.append((question, user_disp if user_disp!="" else "—", corr_disp, "❌ špatně"))
                        st.session_state.current_task = None
                        st.rerun()

            # ————— ČJ —————
            elif subject == "ČJ":
                pool = build_cjl_pool(vyber_tridy, confirmed_topic)
                if not pool:
                    st.warning("Pro tuto třídu/téma zatím nejsou ČJ úlohy.")
                else:
                    if st.session_state.current_cjl_task is None:
                        st.session_state.current_cjl_task = random.choice(pool)
                    task = st.session_state.current_cjl_task

                    with st.form("cjl_form", clear_on_submit=False):
                        c1, c2 = st.columns([4,1])
                        with c1: st.markdown(f"#### ✏️ {task['text']}")
                        with c2: st.markdown(f"🏅 **Skóre:** {st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL}")
                        choice = st.radio(
                            "Vyber odpověď:",
                            options=["a","b","c"],
                            index=None,
                            format_func=lambda x: task["options"][ord(x)-97],
                            key=f"cjl_choice_{hash(task['text'])%10**8}"
                        )
                        ok_cjl = st.form_submit_button("Odeslat")

                    if st.session_state.feedback_message:
                        (st.success if st.session_state.feedback_type=="success" else st.error)(st.session_state.feedback_message)

                    if ok_cjl:
                        if choice is None:
                            st.warning("Než odešleš, vyber prosím jednu možnost.")
                        else:
                            corr = task["correct_option"]
                            chosen_text = task["options"][ord(choice)-97]
                            corr_text   = task["options"][ord(corr)-97]
                            if choice == corr:
                                st.session_state.feedback_message = "Správně! 🎉"; st.session_state.feedback_type = "success"
                                st.session_state.tasks_solved_for_reveal += 1
                                st.session_state.history.append((task["text"], chosen_text, corr_text, "✅ správně"))
                                idxs = [i for i,r in enumerate(st.session_state.revealed_tiles) if not r]
                                if idxs: st.session_state.revealed_tiles[random.choice(idxs)] = True
                            else:
                                st.session_state.feedback_message = f"Nesprávně. ❌ Správná odpověď byla: {corr_text}"
                                st.session_state.feedback_type = "error"
                                st.session_state.history.append((task["text"], chosen_text, corr_text, "❌ špatně"))
                            st.session_state.current_cjl_task = None
                            st.rerun()


            # ————— IT —————
            else:
                tasks = IT_TASKS_BY_TOPIC.get(vyber_tridy, {}).get(confirmed_topic, [])
                if not tasks:
                    st.warning("Pro tuto třídu zatím nejsou IT úlohy.")
                else:
                    idx = st.session_state._it_index % len(tasks)
                    task = tasks[idx]
                    st.markdown(f"#### 💻 {task['prompt']}")
                    code_key = f"it_code_{idx}"
                    code = st.text_area("Tvůj Python kód:",
                                        value=st.session_state.get(code_key, task.get("starter","")),
                                        height=160, key=code_key, placeholder="Sem napiš svůj kód…")
                    c_run_out = st.columns([1,3])
                    run = c_run_out[0].button("Spustit kód")
                    if run:
                        ok_run, out = run_user_code_capture_stdout(code)
                        st.session_state._it_last_output = out if ok_run else out
                    with c_run_out[1]:
                        st.caption("Výstup programu:"); st.code(st.session_state._it_last_output or "(žádný výstup)")
                    c_eval = st.columns([1,3])
                    eval_btn = c_eval[0].button("Vyhodnotit")
                    if eval_btn:
                        ok_run, out = run_user_code_capture_stdout(code)
                        st.session_state._it_last_output = out if ok_run else out
                        expected = task["expected_stdout"].strip()
                        if not ok_run:
                            st.session_state._it_last_eval = f"Chyba běhu: {out}"
                            st.session_state.feedback_message = out
                            st.session_state.feedback_type = "error"
                            st.session_state.history.append((task["prompt"], out, expected, "❌ chyba běhu"))
                        else:
                            if out.strip() == expected:
                                st.session_state._it_last_eval = "Správně! 🎉"
                                st.session_state.feedback_message = "Správně! 🎉"
                                st.session_state.feedback_type = "success"
                                st.session_state.tasks_solved_for_reveal += 1
                                st.session_state.history.append((task["prompt"], out, expected, "✅ správně"))
                                st.session_state._it_index += 1
                                idxs = [i for i,r in enumerate(st.session_state.revealed_tiles) if not r]
                                if idxs: st.session_state.revealed_tiles[random.choice(idxs)] = True
                            else:
                                st.session_state._it_last_eval = f"Nesprávně. Očekáváno: `{expected}`; tvůj výstup: `{out}`"
                                st.session_state.feedback_message = f"Nesprávně. ❌ Očekáváno: `{expected}`; tvůj výstup: `{out}`"
                                st.session_state.feedback_type = "error"
                                st.session_state.history.append((task["prompt"], out, expected, "❌ špatně"))
                        st.rerun()
                    with c_eval[1]:
                        st.caption("Hodnocení:")
                        if st.session_state._it_last_eval:
                            if "Správně" in st.session_state._it_last_eval: st.success(st.session_state._it_last_eval)
                            elif "Chyba" in st.session_state._it_last_eval: st.error(st.session_state._it_last_eval)
                            else: st.error(st.session_state._it_last_eval)
                        else:
                            st.info("Zatím nevyhodnoceno.")
                    st.markdown(f"🏅 **Skóre:** {st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL}")

        else:
            st.snow()
            if st.session_state.end_time is None:
                st.session_state.end_time = time.time()
                st.session_state.achievement_date = datetime.datetime.now()
                total = st.session_state.end_time - st.session_state.start_time
                correct = sum(1 for *_, status in st.session_state.history if status == "✅ správně")
                incorrect = len(st.session_state.history) - correct

                is_best = False
                if correct > st.session_state.best_score:
                    st.session_state.best_score = correct
                    is_best = True
                if total < st.session_state.best_time:
                    st.session_state.best_time = total
                    is_best = True

                report = (
                    f"#### ✨ Skvěle!\n"
                    f"- Správně: **{correct}**\n"
                    f"- Nesprávně: **{incorrect}**\n"
                    f"- Čas (20 úkolů): **{total:.2f}** s\n"
                )
                if is_best:
                    report += "\n**🏆 Nový osobní rekord!**"

                st.session_state.final_report = report
                st.session_state.score = st.session_state.tasks_solved_for_reveal
            st.success("Vyřešil/a jsi všech 20 úkolů!")


  
    # Historie
    if st.checkbox("📜 Zobrazit historii odpovědí"):
        st.markdown("---"); st.subheader("Historie řešení")
        if not st.session_state.history:
            st.info("Zatím žádné odpovědi.")
        else:
            for i, item in enumerate(reversed(st.session_state.history), 1):
                q, a_user, a_correct, status = item
                st.markdown(f"{i}. **{q}** → tvoje: `{a_user}` | správně: `{a_correct}` — {status}")

    # Diplom
    if st.session_state.final_report:
        # 🔧 fix: definuj db_level
        db_level = class_to_db_level.get(vyber_tridy, vyber_tridy)

        st.subheader("🏆 Výsledková listina")
        st.info(st.session_state.final_report)
        st.subheader("📜 Vytvořit diplom")
        diploma_name = st.text_input("Jméno na diplom:", value="")

        if diploma_name and st.session_state.best_score > 0:
            subject_display = {"MA":"Matematikou","ČJ":"Češtinou","IT":"Informatikou (Python)"}.get(subject, "")
            topic_line = confirmed_topic or ""  # zvolené téma se propíše do PDF

            pdf_bytes = generate_diploma_pdf(
                username=diploma_name,
                score=st.session_state.best_score,
                time_s=st.session_state.best_time,
                fairytale_title=vyber,
                achievement_date=st.session_state.achievement_date,
                level=db_level,
                subject_display=subject_display,
                topic_line=topic_line,
                image_path=st.session_state.diploma_image_path,
                crop_mode="auto",
            )
            st.download_button("Stáhnout diplom PDF", data=pdf_bytes,
                            file_name=f"diplom_{diploma_name}.pdf", mime="application/pdf")
            
    if st.session_state.game_started and st.session_state.tasks_solved_for_reveal >= TASKS_TO_REVEAL:
        if st.button("Začít novou hru", key="restart_game_final"):
            ss = st.session_state
            ss.game_started = False
            ss.tasks_solved_for_reveal = 0
            ss.start_time = None
            ss.end_time = None
            ss.current_task = None
            ss.current_cjl_task = None
            ss.history = []
            ss.feedback_message = ""
            ss.feedback_type = ""
            ss.final_report = None
            ss.revealed_tiles = [False] * TASKS_TO_REVEAL
            ss.tile_coords = []
            # best_score, best_time, achievement_date nechávám – jsou to „osobní rekordy“
            st.rerun()

    
with col_right:
    st.subheader("🖼️ Obrázek")
    if image_path and os.path.exists(image_path):
        if st.session_state.tasks_solved_for_reveal>=TASKS_TO_REVEAL:
            st.image(image_path, use_container_width=True, caption=f"Gratuluji! ({st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL})")
        else:
            img = _PILImage.open(image_path); draw = ImageDraw.Draw(img)
            if not st.session_state.tile_coords:
                w,h = img.size; tw,th = w//5, h//4
                st.session_state.tile_coords = [(c*tw, r*th, (c+1)*tw, (r+1)*th) for r in range(4) for c in range(5)]
                st.session_state.revealed_tiles = [False]*20
            tiles_to_cover = [i for i, r in enumerate(st.session_state.revealed_tiles) if not r]
            for i in tiles_to_cover:
                x1,y1,x2,y2 = st.session_state.tile_coords[i]
                draw.rectangle([x1,y1,x2,y2], fill="black")
            buf = io.BytesIO(); img.save(buf, format="PNG")
            st.image(buf, use_container_width=True, caption=f"Odhaleno {st.session_state.tasks_solved_for_reveal}/{TASKS_TO_REVEAL}")
    else:
        st.warning("Obrázek nenalezen v ./obrazky/.")

# =========================
# Ponaučení
# =========================
st.markdown("---")
st.subheader("⭐ Mravní ponaučení")
if moral: st.info(moral)
else:     st.warning("Ponaučení není zadáno.")

