#!/usr/bin/env python3
"""Hand-written lines about a listed headline: default FLAG (rule set M; run 2026-11-18T1428Z, part 3; written blind to
any red team of this rule, before its adversary ran — see runs/2026-11-18T1428Z/README.md).

Why (runs 2026-11-18T0228Z, 0828Z, `runs/2026-11-18T0828Z/t5/READERS.md`): one hand-written sentence in STATE.md
withdrawing a valid listed headline (W′) made 9/9 blind readers withhold citation, whatever generated line stood
beside it (kernel status, fidelity record, "open fidelity objections: none"). Readers take dated author prose as
later than any generated line. So an objection to a listed headline must not exist in prose unless it is registered
in `scripts/trust/objections.txt` (then CLAIMS.md / CLAIMS_READER.md print it, which is correct). Run 0228Z's word
rule against withdrawals (S3) fell ≈ 40 ways (synonyms, name forms, clause splitting, markup, Unicode); this check
therefore has the opposite default: a NEW line that is about a listed headline is flagged unless every word in it is
in a closed, classified vocabulary and every status word in it sits inside a registered status template, or every
headline it is about has an open objection registered with this file as its path.

Files: STATE.md, README.md, BLUEPRINT.md and the front page (above the first `## ` heading) of every
  runs/<run>/README.md (run record).
New line: a line whose normalized text occurs in no scanned file at the base commit (moving a line is not new).
About H: H's name key (its last name component, or the last component of its Checked module, letters and digits
  only, at least six) occurs in the normalized letters-and-digits skeleton of the line with the two non-blank lines
  before and after it, the line's heading chain, or, for a heading, its whole section. Normalization: NFKC, Unicode
  format characters and combining marks dropped, look-alike letters folded to Latin, HTML entities and tags removed,
  lower case — so `gelfand_extrema`, gelfand extrema, Gelfand-<br>Extrema, GelfandExtrema.lean and a Cyrillic і are
  one name.
Words of a new about-line (code spans that are a listed headline, a repository path or a module name, hexadecimal
  commit ids and numbers removed; camelCase and snake_case split):
  M1 every word is in `scripts/trust/mention_vocab.txt` (unknown words are flagged: add a word only with a LEDGER line
     naming the file; M4 refuses status words there);
  M2 no STATUS word (negators, statuses, withdrawal, evaluation, citation and trust words: `STATUS` below) outside a
     template of `TEMPLATES` below (CI-run-backed PROVED forms, "promoted to Checked", "in Work", "referee STANDS",
     "Not claimed:", …);
  M3 escape: every headline the line is about has an open entry in objections.txt whose path is this file.
  M4 (--base) mention_vocab.txt grows only with a LEDGER line naming it and never gains a STATUS word; TEMPLATES and
     STATUS change only with a LEDGER line naming this script.
Limits (recorded, measured by the red team of this run): a headline described without any form of its name; a
status stated with ordinary words in vocabulary (the vocabulary is the attack surface: it is seeded from the
existing records minus STATUS); files outside the list (LEDGER.md, CHANGELOG.md, referee reports).

Usage: check_headline_mentions.py --base SHA      check lines new since SHA (CI: base of the push)
       check_headline_mentions.py --selftest      controls (W′ of run 0228Z and its S3 bypass shapes must fail)
       check_headline_mentions.py --seed-vocab    (maintenance) print the vocabulary of the current records minus STATUS
"""
import functools
import html
import re
import subprocess
import sys
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
VOCAB = "scripts/trust/mention_vocab.txt"
OBJ = "scripts/trust/objections.txt"
HEADS = "scripts/trust/headlines.txt"
READER = "CLAIMS_READER.md"

# Latin look-alikes (Cyrillic, Greek, others) folded to Latin before matching names and words
FOLD = str.maketrans({
    "а": "a", "в": "b", "е": "e", "ё": "e", "к": "k", "м": "m", "н": "h", "о": "o", "р": "p", "с": "c", "т": "t",
    "у": "y", "х": "x", "і": "i", "ї": "i", "ј": "j", "ѕ": "s", "ԁ": "d", "ԛ": "q", "ԝ": "w", "ɡ": "g", "һ": "h",
    "ӏ": "l", "ο": "o", "α": "a", "ν": "v", "ρ": "p", "τ": "t", "ι": "i", "κ": "k", "υ": "u", "χ": "x", "ε": "e",
    "β": "b", "η": "n", "Ꭺ": "a", "ı": "i", "ȷ": "j", "ℓ": "l", "ſ": "s", "ꞵ": "b", "ɑ": "a", "ᴀ": "a", "ʀ": "r",
})

STATUS = re.compile(r"(?x)^(?:"
    r"not|no|non|never|nor|neither|none|nothing|nowhere|without|cannot|can't|cant|isn't|isnt|doesn't|doesnt|don't|dont|"
    r"won't|wont|aren't|arent|wasn't|wasnt|weren't|shouldn't|mustn't|mustnt|longer|anymore|lacks?|lacking|"
    r"proved|proven|audited|stated|refuted|blocked|informal|unproved|unproven|unaudited|unverified|unchecked|"
    r"withdr[ae]wn?|withdraw\w*|retract\w*|revok\w*|revoc\w*|rescind\w*|supersed\w*|obsolete\w*|deprecat\w*|"
    r"retir\w*|invalid\w*|flaw\w*|wrong\w*|incorrect\w*|false\w*|falsif\w*|error\w*|erroneous\w*|mistak\w*|bugs?|buggy|"
    r"broken|unsound\w*|refut\w*|disprov\w*|fell|fall\w*|fail\w*|misread\w*|mislead\w*|misled|misstat\w*|"
    r"mistranslat\w*|misrepresent\w*|overstat\w*|understat\w*|overclaim\w*|doubt\w*|dubious|questionabl\w*|suspect\w*|"
    r"suspicious|unreliabl\w*|untrust\w*|distrust\w*|mistrust\w*|caution\w*|warn\w*|beware|avoid\w*|objection\w*|"
    r"object|objects|objected|concern\w*|issues?|defect\w*|weak\w*|narrow\w*|vacuous\w*|trivial\w*|junk|"
    r"stale|outdated|pending|correction\w*|replac\w*|review\w*|hold|pulled|demot\w*|downgrad\w*|reject\w*|"
    r"contradict\w*|inconsist\w*|disagree\w*|mismatch\w*|discrepan\w*|cite|cites|cited|citing|citation\w*|rely|"
    r"relies|relied|reliance|reliable|trust|trusts|trusted|trustworthy|trustworthiness|valid|validity|sound|"
    r"soundness|correct|correctly|correctness|faithful\w*|unfaithful\w*|fidelity|meaning|say|says|said|"
    r"claimed|differ\w*|unlike|deviat\w*|wrongly|inaccura\w*|imprecis\w*|unclear|ambiguous\w*|"
    r"misses|missed|miss|omit\w*|drops|dropped|ignor\w*|loses|lost|unsupported|unjustified|unwarranted|caveat\w*|"
    r"careful|carefully|instead|rather|but|however|although|though|yet|only|merely|just|actually|really|"
    r"apparent\w*|seemingly|allegedly|supposed\w*|purported\w*|flagged|flag|undo\w*|undone|reverted|revert\w*|"
    r"removed|remove|strike|struck|annul\w*|void|voided|cancel\w*|suspend\w*|frozen|refrozen|re-frozen|refreeze|"
    r"stands|standing|fixed|fix|repair\w*|amend\w*|erratum|errata|bogus|spurious|fake|fabricat\w*|unsafe|risky|risk|"
    r"less|fewer|smaller|weaker|stronger|beyond|outside|except|excluding|excludes?|unless|until|later|"
    r"earlier|previous\w*|former\w*|old|older|newer|current\w*|no-longer"
    r")$")

# status templates: the forms a record may use; matched on the normalized line, removed before M2 (not M1)
TEMPLATES = [
    r"\bproved \(ci \d{6,} of [0-9a-f]{7,40}(?:, a descendant(?: of [^,)]*)?,)? green on every job[^)]*\)",
    r"\bproved once (?:a main run|ci) is green on every job(?: \(read next run\))?",
    r"\bci \d{6,} \([0-9a-f]{7,40}\)(?:'s checked job)? (?:pending|in progress)(?: behind \d{6,} \([0-9a-f]{7,40}\))?",
    r"\bpromoted to checked(?: \+ audited)?",
    r"\bproved in work(?: \+ audited)?",
    r"\breferee stands\b(?!-)",
    r"^\W*not claimed\b",
    r"\bfrozen [0-9a-f]{7,40}\b",
    r"\bre-frozen [0-9a-f]{7,40}\b",
    r"\bproved [0-9a-f]{7,40}\b",
    r"\bstatement unchanged\b",
    r"\bnon-vacuity\b",
    r"\bnot vacuous\b",
    # the front-page lines every run record must carry (PROMPT instruction 9, goal guard)
    r"\bwhat can a scientist now trust without checking it themselves, that they could not before\?",
    r"\bweakest unchecked step\b",
    r"\bopen fidelity objections\b",
    r"\bno new certificates?\b",
    r"^last updated:",
    r"\bgreen on every job for [0-9a-f]{7,40} or a descendant\s*(?:→|->)\s*\S+ proved\b",
    r"^previous update:",
]
TEMPLATE_RE = [re.compile(t) for t in TEMPLATES]
NOT_CLAIMED = r"^\W*not claimed\b"
assert NOT_CLAIMED in TEMPLATES

# M0 (after red team M, A1): a word mixing ASCII letters with other letters left after folding ('radiał') is flagged
# on every new line of a scanned file, so a look-alike missing from FOLD cannot hide a name.
# M5 (after red team M, A2): withdrawal words are flagged on every new line of a scanned file, about a named headline
# or not, unless an open objection is registered with that file as its path (a deny-list layer under the default flag).
HARD = re.compile(r"(?x)^(?:withdr[ae]wn?|withdraw\w*|retract\w*|revok\w*|revoc\w*|rescind\w*|supersed\w*|"
                  r"obsolete\w*|deprecat\w*|invalidat\w*|annul\w*|flaw\w*|disown\w*|repudiat\w*|recant\w*)$")


BANNERS = ["a withdrawn headline is not listed", "statuses written here (proved, withdrawn, …)"]  # banner sentences


def mixed(line):
    t = norm(line)
    return sorted({w for w in re.findall(r"[^\W\d_]+", t)
                   if re.search(r"[a-z]", w) and re.search(r"[^\x00-\x7f\u0370-\u03ff]", w)})

FILES_FIXED = ["STATE.md", "README.md", "BLUEPRINT.md"]
RUN_README = re.compile(r"^runs/[^/]+/README\.md$")


def norm(s):
    s = html.unescape(html.unescape(s))
    s = re.sub(r"<[^>]*>", "", s)  # red team M2 A1: with<b></b>drawn
    s = unicodedata.normalize("NFKD", unicodedata.normalize("NFKC", s))
    s = "".join(ch for ch in s if unicodedata.category(ch) not in ("Cf", "Mn", "Me", "Cc") or ch in "\n\t")
    return s.lower().translate(FOLD)


def unmark(t):
    """markdown emphasis characters deleted outside code spans (red team M2 A1: n*o*t, **With**drawn, with_drawn_)"""
    parts = re.split(r"(`+[^`]+`+)", t)
    return "".join(x if x.startswith("`") else re.sub(r"[*_~]", "", x) for x in parts)


def skel(s):
    return re.sub(r"[^a-z0-9]", "", norm(s))


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True).stdout


def scanned(paths):
    return [p for p in paths if p in FILES_FIXED or RUN_README.match(p)]


def files_at(rev):
    if rev is None:
        names = git("ls-files").split("\n")
        return {p: (ROOT / p).read_text(encoding="utf-8", errors="replace") for p in scanned(names) if (ROOT / p).exists()}
    names = git("ls-tree", "-r", "--name-only", rev).split("\n")
    return {p: git("show", f"{rev}:{p}") for p in scanned(names)}


@functools.lru_cache(maxsize=None)
def headlines():
    """name keys -> set of full headline names; full names -> module"""
    heads = [l.strip() for l in (ROOT / HEADS).read_text(encoding="utf-8").splitlines()
             if l.strip() and not l.startswith("#")]
    reader = (ROOT / READER).read_text(encoding="utf-8")
    full_mod = {}
    cur = None
    for line in reader.splitlines():
        m = re.match(r"^#+ .*?`(Checked\.[A-Za-z0-9_.']+)`", line)
        if m:
            cur = m.group(1)
        m = re.search(r"proved in module `(Checked\.[A-Za-z0-9_.']+)`", line)
        if m and cur:
            full_mod[cur] = m.group(1)
    keys = {}
    fulls = {}
    for h in heads:
        full = next((f for f in full_mod if f == h or f.endswith("." + h)), h)
        fulls[full] = h
        for k in {skel(full.split(".")[-1]), skel(full_mod.get(full, "").split(".")[-1])}:
            if len(k) >= 6:
                keys.setdefault(k, set()).add(full)
    return keys, fulls, set(full_mod.values())


@functools.lru_cache(maxsize=None)
def name_tokens():
    """full name -> its word set (snake_case, camelCase and digits split), for headlines of three or more words"""
    _, fulls, _ = headlines()
    out = {}
    for f in fulls:
        last = f.split(".")[-1]
        parts = re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|\d+", last.replace("'", ""))
        toks = frozenset(norm(x) for x in parts if len(x) >= 2 and not x.isdigit())
        if len(toks) >= 3:
            out[f] = toks
    return out


def loose(text):
    """headlines whose name words all occur, but at most one, as words of the text (A5: 'Gelfand radial many centre')"""
    ws = set(re.findall(r"[a-z0-9]+", norm(text)))
    return {f for f, toks in name_tokens().items()
            if len(toks - ws) <= (1 if len(toks) >= 5 else 0) and len(toks & ws) >= 3}


def blocks_of(lines):
    """block index per line (blank-line separated) and heading chain per line"""
    bidx, b, chain, chains, stack = [], 0, [], [], []
    for i, l in enumerate(lines):
        if not l.strip():
            b += 1
        bidx.append(b)
        m = re.match(r"^(#{1,6})\s", l)
        if m:
            lvl = len(m.group(1))
            stack = [(lv, j) for lv, j in stack if lv < lvl]
            chains.append([j for _, j in stack])
            stack.append((lvl, i))
        else:
            chains.append([j for _, j in stack])
    return bidx, chains


def about(lines, i, bidx, chains, keys):
    near = [j for j in range(max(0, i - 6), min(len(lines), i + 7)) if lines[j].strip()]
    k = near.index(i)
    ctx = [lines[j] for j in near[max(0, k - 2):k + 3]] + [lines[j] for j in chains[i]]
    m = re.match(r"^(#{1,6})\s", lines[i])
    if m:
        lvl = len(m.group(1))
        for l in lines[i + 1:]:
            mm = re.match(r"^(#{1,6})\s", l)
            if mm and len(mm.group(1)) <= lvl:
                break
            ctx.append(l)
    s = skel("\n".join(ctx))
    return {f for k, fs in keys.items() if k in s for f in fs} | loose("\n".join(ctx))


_NAMECACHE = {}


def _names(fulls, modules):
    k = (id(fulls), id(modules))
    if k not in _NAMECACHE:
        nf = {norm(f) for f in fulls}
        short = {norm(f.split(".")[-1]) for f in fulls} | {norm(h) for h in fulls.values()}
        _NAMECACHE[k] = (nf, short, {norm(m) for m in modules})
    return _NAMECACHE[k]


def _exists(c):
    try:
        return len(c) < 200 and (ROOT / c).exists()
    except OSError:
        return False


def words(line, fulls, modules):
    """the line's prose: code spans naming a headline, module, path or dotted Lean name removed"""
    nf, short, nm = _names(fulls, modules)
    t = unmark(norm(line))

    def drop_code(m):
        c = m.group(1).strip()
        if c in nf or c in short or c in nm or any(c.endswith("." + x) for x in short):
            return " "
        if _exists(c) or re.fullmatch(r"(checked|work|scripts|runs)[\w./-]*", c):
            return " "
        if re.fullmatch(r"[\w.'{}, ]+", c) and "." in c:
            return " "  # dotted Lean name(s): identifiers, not prose
        return " " + c + " "
    t = re.sub(r"`+([^`]+)`+", drop_code, t)
    t = re.sub(r"\b[0-9a-f]{7,40}\b", " ", t)
    return t


def tokens(t):
    out = []
    for w in re.findall(r"[^\W\d_]+(?:['’][^\W\d_]+)?(?:-[^\W\d_]+)*", t):
        for part in w.replace("’", "'").split("-"):
            if part:
                out.append(part)
    return out


def check_line(line, fulls, modules, vocab, open_obj, path, ab):
    errs = []
    keys = headlines()[0]
    s = skel(line)
    direct = {f for k, fs in keys.items() if k in s for f in fs} | loose(line)
    lic = {f for f in ab if path in open_obj.get(f, set())}
    if lic and all(path in open_obj.get(f, set()) for f in direct):
        return errs  # M3: every headline the line names has an open objection with this path, or it names none and
        # one headline it is about has one
    n = norm(line)
    stripped = n
    for r in TEMPLATE_RE:
        if direct and r.pattern == NOT_CLAIMED:
            continue  # red team M A8/A9: "Not claimed: `<headline>`" disowns a headline
        stripped = r.sub(" ", stripped)
    # identifiers in the original (camelCase split) before lower-casing
    raw = re.sub(r"`+([^`]+)`+", lambda m: " " + m.group(1) + " ", line)
    del raw
    t_all = words(n, fulls, modules)
    t_stat = words(stripped, fulls, modules)
    unknown = sorted({w for w in tokens(t_all) if len(w) > 1 and w not in vocab and not STATUS.match(w)})
    status = sorted({w for w in tokens(t_stat) if STATUS.match(w)})
    if unknown:
        errs.append(f"M1 words not in {VOCAB}: {', '.join(unknown[:12])}")
    if status:
        errs.append(f"M2 status words outside a template: {', '.join(status[:12])}")
    return errs


def load_vocab(text=None):
    text = text if text is not None else (ROOT / VOCAB).read_text(encoding="utf-8")
    return {l.strip() for l in text.splitlines() if l.strip() and not l.startswith("#")}


def load_obj():
    out = {}
    keys, fulls, _ = headlines()
    for l in (ROOT / OBJ).read_text(encoding="utf-8").splitlines():
        if l.startswith("#") or "|" not in l:
            continue
        parts = [p.strip() for p in l.split("|")]
        for f in fulls:
            if f == parts[0] or f.endswith("." + parts[0]):
                out.setdefault(f, set()).add(parts[2])
    return out


def ident(line):
    """identity of a line for 'new': the STATE.md update prefixes are dropped, so moving the last update line to
    'Previous update' is no new line"""
    return re.sub(r"^(last updated|previous update):\s*", "", norm(line).strip())


def run(base_files, head_files, vocab=None, obj=None):
    keys, fulls, modules = headlines()
    vocab = vocab if vocab is not None else load_vocab()
    obj = obj if obj is not None else load_obj()
    old = {ident(l) for txt in base_files.values() for l in txt.splitlines()}
    errors = []
    for path, txt in sorted(head_files.items()):
        lines = txt.splitlines()
        bidx, chains = blocks_of(lines)
        front = len(lines)
        if RUN_README.match(path):  # run records: the front page (above the first level-2 heading)
            # the first standard section heading (red team M2 A4: an inserted "## Correction" moved the boundary)
            std = [i for i, l in enumerate(lines) if re.match(r"^## (Start|Bottleneck|What we did)\b", l)]
            front = std[0] if std else next((i for i, l in enumerate(lines) if l.startswith("## ")), len(lines))
        for i, l in enumerate(lines):
            if i >= front:
                break
            if not l.strip() or ident(l) in old:
                continue
            mx = mixed(l)
            if mx:
                errors.append(f"{path}:{i + 1}: M0 mixed-script words: {', '.join(mx[:6])}")
            nl = unmark(norm(l))
            for b in BANNERS:
                nl = nl.replace(b, " ")
            hard = sorted({w for w in tokens(nl) if HARD.match(w)})
            if hard and not any(path in v for v in obj.values()):
                errors.append(f"{path}:{i + 1}: M5 withdrawal words with no objection registered for this file: "
                              f"{', '.join(hard)}")
            ab = about(lines, i, bidx, chains, keys)
            if not ab:
                continue
            for e in check_line(l, fulls, modules, vocab, obj, path, ab):
                short = ", ".join(sorted(f.split(".")[-1] for f in ab)[:4])
                errors.append(f"{path}:{i + 1}: about {short}: {e}")
    return errors


def m4(base):
    errs = []
    diff = git("diff", f"{base}..HEAD", "--", VOCAB)
    added = [l[1:].strip() for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++")]
    added = [w for w in added if w and not w.startswith("#")]
    if added:
        ledger = git("diff", f"{base}..HEAD", "--", "LEDGER.md")
        if not any(l.startswith("+") and "mention_vocab" in l for l in ledger.splitlines()):
            errs.append(f"M4 {VOCAB} grew ({len(added)} words) without an added LEDGER line naming mention_vocab")
        bad = [w for w in added if STATUS.match(w)]
        if bad:
            errs.append(f"M4 status words may never enter {VOCAB}: {', '.join(bad)}")
    sdiff = git("diff", f"{base}..HEAD", "--", "scripts/trust/check_headline_mentions.py")
    if any(l.startswith("-") and not l.startswith("---") and ("r\"" in l or "r'" in l) for l in sdiff.splitlines()):
        ledger = git("diff", f"{base}..HEAD", "--", "LEDGER.md")
        if not any(l.startswith("+") and "check_headline_mentions" in l for l in ledger.splitlines()):
            errs.append("M4 STATUS/TEMPLATES of check_headline_mentions.py changed without an added LEDGER line naming it")
    return errs


def selftest():
    """controls: each defect line, appended under the Gelfand multiplicity section of STATE.md, must be flagged;
    each correct line must pass"""
    head = files_at(None)
    st = head["STATE.md"]
    anchor = "## Mathematics: multiplicity of radial solutions of the Gelfand problem"
    assert anchor in st, "selftest anchor missing"

    def ins(text, line):
        i = text.index(anchor)
        j = text.index("\n", i)
        return text[:j + 1] + line + "\n" + text[j + 1:]
    defects = [
        "- **Withdrawn (2026-11-18, after the CI read):** a referee found a fidelity flaw in the frozen statement; "
        "`gelfand_pde_radial_many_centre` is no longer PROVED and must not be cited until it is re-frozen and re-proved.",
        "- Gelfand PDE radial many centre: invalid, under review.",
        "- `gelfand_pde_radial_many_centre` &#8212; dep&shy;recated.",
        "- GelfandPDEManyCentre.lean is not to be relied upon.",
        "- `gelfand_pde_radial_many_​centre` does not say what its source says.",
        "- Note: the multiplicity result above is under a cloud; see the next line.",
        "- `gelfand_pde_radial_many_centre` (Gelfand, multiplicity) — retracted",
        "- `gelfand_pdе_radial_many_centre` superseded.",  # Cyrillic е
        # red team M (run 2026-11-18T1428Z), class-A defects that passed 6f2918f3
        "**Withdrawn:** a referee found a fidelity flaw; `gelfand_pde_radiał_many_centre` is no longer PROVED and must "
        "not be cited.",
        "The Gelfand radial multiplicity theorem in the ball was withdrawn by a referee; do not cite it.",
        "Gelfand radial many centre theorem is replaced by a weaker one",
        "Gelfand radial many centre: older theorem, the newer one is stronger.",
        "Not claimed: `gelfand_pde_radial_many_centre`.",
        "Not claimed: the multiplicity count of `gelfand_pde_radial_many_centre`, which is the statement of the paper.",
        "- `gelfand_pde_radial_many_centre`: the quantifiers are the other way round from the paper theorem.",
        # red team M2 (run 2026-11-18T1428Z), against aa07d9ee
        "- **With**drawn: a referee found a f*law* in `gelfand_pde_radial_many_centre`; do n*o*t ci*te* it.",
        "- `gelfand_pde_radial_many_centre` is with_drawn_ from the list.",
        "- `gelfand_pde_radial_many_centre` is with<b></b>drawn.",
        "- `gelfand_pde_radial_many_centre` is a lie.",
        "- `gelfand_pde_radial_many_centre` is gone.",
        "- `gelfand_pde_radial_many_centre` is out of date.",
        "- `gelfand_pde_radial_many_centre`: off the table, drop it.",
    ]
    # known limit (recorded, not a control): a status in ordinary in-vocabulary words, e.g.
    # "`gelfand_pde_radial_many_centre`: the quantifiers are the other way round from the paper's theorem." passes
    goods = [
        "- Not claimed: exact counts for λ in [λ₁, λ₂] other than at the ends.",
        "- Promoted to Checked + AUDITED; PROVED (CI 44261574038 of adcb9a6 green on every job incl. the checked job).",
    ]
    fails = 0
    base = dict(head)
    for d in defects:
        new = dict(head)
        new["STATE.md"] = ins(st, d)
        e = run(base, new)
        if not e:
            print(f"selftest FAIL: defect passed: {d}")
            fails += 1
    for g in goods:
        new = dict(head)
        new["STATE.md"] = ins(st, g)
        e = run(base, new)
        if e:
            print(f"selftest FAIL: correct line flagged: {g}: {e}")
            fails += 1
    # M3: a registered objection with this file as its path licenses the line
    keys, fulls, _ = headlines()
    full = next(f for f in fulls if f.endswith("gelfand_pde_radial_many_centre"))
    new = dict(head)
    new["STATE.md"] = ins(st, defects[0])
    if run(base, new, obj={full: {"STATE.md"}}):
        print("selftest FAIL: registered objection did not license the line (M3)")
        fails += 1
    print(f"check_headline_mentions selftest: {len(defects)} defects, {len(goods)} correct lines, M3; "
          f"{'FAIL' if fails else 'ok'}")
    return 1 if fails else 0


def seed():
    head = files_at(None)
    keys, fulls, modules = headlines()
    vocab = set()
    for txt in head.values():
        for l in txt.splitlines():
            vocab |= {w for w in tokens(words(norm(l), fulls, modules)) if len(w) > 1 and not STATUS.match(w)}
    print("\n".join(sorted(vocab)))


def main(argv):
    if "--selftest" in argv:
        return selftest()
    if "--seed-vocab" in argv:
        seed()
        return 0
    if "--base" in argv:
        base = argv[argv.index("--base") + 1]
        # the rule binds from the commit that introduced this script: lines older than it are not new to the rule
        intro = git("log", "--diff-filter=A", "--format=%H", "--", "scripts/trust/check_headline_mentions.py").split()
        if intro and subprocess.run(["git", "merge-base", "--is-ancestor", base, intro[-1]], cwd=ROOT).returncode == 0:
            base = intro[-1]
        if selftest():
            return 1
        errors = run(files_at(base), files_at(None)) + m4(base)
        for e in errors:
            print(e)
        print(f"check_headline_mentions (base {base[:12]}): {len(errors)} finding(s); {'FAIL' if errors else 'ok'}")
        if errors:
            print("A new line about a listed headline uses only words of scripts/trust/mention_vocab.txt and states a "
                  "status only in a template of this script; an objection is entered in scripts/trust/objections.txt "
                  "with this file as its path (then CLAIMS pages print it).")
        return 1 if errors else 0
    return selftest()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
