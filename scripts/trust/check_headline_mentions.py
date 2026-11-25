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
       check_headline_mentions.py --words LINE    (authoring aid) the words of a draft line outside the vocabulary
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
    r"\bproved \(ci \d{6,} of [0-9a-f]{7,40}(?:, a descendant(?: of [^,)]*)?,)? green on every job"
    r"(?: incl\. the checked job(?: and nanoda \d/\d)?)?(?:; read run \d{4}-\d\d-\d\dt\d{4}z)?[^)]*\)",
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


def _literal_words(pat):
    """the words a template spells out literally (escapes and character classes removed)"""
    p = re.sub(r"\\[A-Za-z]", " ", pat)
    p = re.sub(r"\[[^\]]*\]", " ", p)
    return frozenset(re.findall(r"[a-z]+", p))


TEMPLATE_LIT = {t: _literal_words(t) for t in TEMPLATES}
NOT_CLAIMED = r"^\W*not claimed\b"
assert NOT_CLAIMED in TEMPLATES

# M0 (after red team M, A1): a word mixing ASCII letters with other letters left after folding ('radiał') is flagged
# on every new line of a scanned file, so a look-alike missing from FOLD cannot hide a name.
# M5 (after red team M, A2): withdrawal words are flagged on every new line of a scanned file, about a named headline
# or not, unless an open objection is registered with that file as its path (a deny-list layer under the default flag).
HARD = re.compile(r"(?x)^(?:withdr[ae]wn?|withdraw\w*|retract\w*|revok\w*|revoc\w*|rescind\w*|supersed\w*|"
                  r"obsolete\w*|deprecat\w*|invalidat\w*|annul\w*|flaw\w*|disown\w*|repudiat\w*|recant\w*)$")


BANNERS = ["a withdrawn headline is not listed", "statuses written here (proved, withdrawn, …)"]  # banner sentences


MIXED_OK = {"λcdm"}  # ΛCDM: the one mixed Greek–Latin word of the records (run 2026-11-18T2028Z)


def mixed(line):
    """red team M3 (run 2026-11-18T2028Z) A5: 'manγ_ϲentre' hid a name with Greek look-alikes, which M0 exempted;
    a word mixing Latin with any other letter (Greek included) is flagged, except MIXED_OK"""
    t = norm(line)
    return sorted({w for w in re.findall(r"[^\W\d_]+", t)
                   if re.search(r"[a-z]", w) and re.search(r"[^\x00-\x7f]", w) and w not in MIXED_OK})

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


def canon(t):
    """spelling and abbreviation variants of name words (red team M3, run 2026-11-18T2028Z: 'many center',
    'third maximum of the Bonnor–Ebert mass' named `gelfand_pde_radial_many_centre`, `bonnor_ebert_third_max`)"""
    t = re.sub(r"(?<![a-z])cent(?:er|re)(?=s?(?![a-z]))", "centre", t)
    t = re.sub(r"(?<![a-z])maxim(?:um|a|al)(?![a-z])", "max", t)
    return re.sub(r"(?<![a-z])minim(?:um|a|al)(?![a-z])", "min", t)


def skel(s):
    # red team M4 (run 2026-11-19T0228Z): names inside HTML comments and attributes count (m6_text reads them)
    return re.sub(r"[^a-z0-9]", "", canon(norm(m6_text(s))))


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
    # red team M3 (run 2026-11-18T2028Z) A2: a distinctive part of a name ('radial many centre', `radial_many_centre`,
    # 'many-centre') names the headline: every run of two or more consecutive name words whose skeleton has at least
    # nine letters and occurs in no other headline's or module's name is a key too
    others = {f: {skel(x.split(".")[-1]) for x in [f, full_mod.get(f, "")] if x} for f in fulls}
    for f in fulls:
        parts = [canon(norm(x)) for x in re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|\d+", f.split(".")[-1].replace("'", ""))]
        for i in range(len(parts)):
            for j in range(i + 2, len(parts) + 1):
                k = "".join(parts[i:j])
                if len(k) >= 9 and not any(k in o for g, os in others.items() if g != f for o in os):
                    keys.setdefault(k, set()).add(f)
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
    ws = set(re.findall(r"[a-z0-9]+", canon(norm(text))))
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


def check_line(line, fulls, modules, vocab, open_obj, path, ab, m6_on=True, m8_on=True):
    errs = []
    keys = headlines()[0]
    s = skel(line)
    direct = {f for k, fs in keys.items() if k in s for f in fs} | loose(line)
    lic = {f for f in ab if path in open_obj.get(f, set())}
    if lic and all(path in open_obj.get(f, set()) for f in direct):
        return errs  # M3: every headline the line names has an open objection with this path, or it names none and
        # one headline it is about has one
    n = norm(line)
    # Each template match is reduced to its words that are NOT literal words of that template; M1 and M2 read the
    # rest (run 2026-11-18T2028Z: before, M2 read nothing of a match, so a STATUS word inside a template's free part —
    # "green on every job, but … do not cite it)" — passed M2, and M1 skips STATUS words; and M1 read the template's
    # own words, which the rebuilt vocabulary does not hold).
    free = n
    for r in TEMPLATE_RE:
        if direct and r.pattern == NOT_CLAIMED:
            continue  # red team M A8/A9: "Not claimed: `<headline>`" disowns a headline
        lit = TEMPLATE_LIT[r.pattern]
        free = r.sub(lambda m: " " + " ".join(w for w in re.findall(r"[^\W_]+", m.group(0))
                                              if w not in lit and not re.search(r"\d", w)
                                              and not re.fullmatch(r"[0-9a-f]{7,40}", w)) + " ", free)
    t_free = words(free, fulls, modules)
    unknown = sorted({w for w in tokens(t_free) if len(w) > 1 and w not in vocab and not STATUS.match(w)})
    status = sorted({w for w in tokens(t_free) if STATUS.match(w)})
    if unknown:
        errs.append(f"M1 words not in {VOCAB}: {', '.join(unknown[:12])}")
    if status:
        errs.append(f"M2 status words outside a template: {', '.join(status[:12])}")
    if m6_on:
        errs += m6(line, t_free, m8_on=m8_on)
    return errs


# M6 (run 2026-11-19T0228Z, part 3; pre-registered in runs/2026-11-19T0228Z/t5/M6_BRIEF.md before its red team ran).
# Why (reader test L2, run 2026-11-18T2028Z): three in-vocabulary lines relating a listed headline to its source ("the
# statement is the dual of the theorem of Joseph and Lundgren 1973, with the inverse order of the quantifiers") passed
# M1/M2 and put a false doubt about fidelity to the source into 3/3 readers' answers. What a statement says relative
# to its source is a fidelity verdict; the program's records of such verdicts are the generated ones (docstrings read
# by check_prose / check_source_names, blind restatements and literal readings, objections.txt printed on CLAIMS pages).
# Rule: a new about-line that NAMES A SOURCE (SRC_RE: a year 1800-2099 that is not part of a date or run id, 'et al',
# paper, literature, printed, published, article, preprint, journal, textbook, author, a numbered table / equation /
# figure / section / theorem / lemma, or a registered source name of source_names.txt) may say nothing else: after its
# templates, name and path code spans, commit ids and CITATION spans (capitalised author names with a year) are
# removed, every word must be in SRC_OK, and no formula character may remain. Detail goes in the run-README body;
# a dispute goes in objections.txt (M3 then licenses the line).
SRC_OK = frozenset("""
and the of in on et al table tables eq eqs equation equations fig figure figures sec section sections appendix
theorem lemma proposition corollary data source sources statement statements headline headlines run see readme
lean checked module modules
""".split())
_DATE = re.compile(r"\b\d{4}-\d\d(?:-\d\d)?(?:t\d{4}z)?\b|\b\d{6,}\b")
_YEAR = r"(?<![\w.\-])(?:18|19|20)\d\d[a-z]?(?![\w\-])"
SRC_RE = re.compile(r"(?x)" + _YEAR + r"|\bet\.?\s+al\b|\b(?:papers?|literature|printed|published|publications?|"
                    r"articles?|preprints?|journals?|textbooks?|authors?|monographs?)\b|"
                    r"\b(?:tables?|tab|eqs?|equations?|fig|figures?|sec|sections?|theorems?|lemmas?|propositions?|"
                    r"corollar(?:y|ies)|appendix)\.?\s*[(\[]?(?:[0-9]|[ivx]+\b|[a-z]\d)")
FORMULA = re.compile(r"[=<>^±∓×÷≤≥≠≈∼~+−∑∫√|]")


@functools.lru_cache(maxsize=None)
def source_names_re():
    """registered source names (scripts/trust/source_names.txt rows whose backing includes 'source')"""
    pats = []
    p = ROOT / "scripts/trust/source_names.txt"
    if p.exists():
        for l in p.read_text(encoding="utf-8").splitlines():
            if l.startswith("#") or "|" not in l:
                continue
            parts = [x.strip() for x in l.split(" | ")]
            if len(parts) >= 3 and re.search(r"(?:^|\+|\|\|\s*)source\b", " | ".join(parts[2:])):
                pats.append(parts[1].replace("(?i)", ""))
    return re.compile("|".join(f"(?:{x})" for x in pats), re.I) if pats else None


@functools.lru_cache(maxsize=None)
def surnames():
    p = ROOT / "scripts/trust/source_surnames.txt"
    return frozenset(norm(l.strip()) for l in p.read_text(encoding="utf-8").splitlines()
                     if l.strip() and not l.startswith("#")) if p.exists() else frozenset()


def m6_text(line):
    """the line as M6 reads it (red team M4, run 2026-11-19T0228Z): HTML comments and tags are read as text, not
    deleted (a citation in a title attribute or a comment hid from norm())"""
    s = html.unescape(html.unescape(line))
    return re.sub(r"<!--|-->|[<>]|=[\"']", " ", s)


DIGIT_WORD = r"(?:zero|oh|one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|thirteen|fourteen|fifteen|" \
             r"sixteen|seventeen|eighteen|nineteen|twenty|thirty|forty|fifty|sixty|seventy|eighty|ninety|hundred)"
NUMWORD_RE = re.compile(r"(?x)\b(?:tables?|tab|eqs?|equations?|figs?|figures?|secs?|sections?|theorems?|lemmas?|"
                        r"propositions?|corollar(?:y|ies)|appendix|rows?|columns?)\s+" + DIGIT_WORD + r"\b|"
                        r"\b(?:" + DIGIT_WORD + r"[\s-]+){2,}" + DIGIT_WORD + r"\b|\b(?:eighteen|nineteen|twenty)[\s-]+"
                        + DIGIT_WORD + r"\b")
INITIAL_RE = re.compile(r"(?<![^\W\d_])[A-Z]\.(?=\s*(?:and\b|&|,|[A-Z]\.|\d|\(?(?:18|19|20)))")
_DATE2 = re.compile(r"\b20[2-9]\d-\d\d-\d\d(?:t\d{4}z)?\b|\b\d{7,}\b")


# M8 (run 2026-11-19T1428Z, part 3; pre-registered in runs/2026-11-19T1428Z/t5/M8_BRIEF.md before its red teams ran).
# Why: M6 reads a source only through a year, a source word, a numbered table/equation, a listed surname or a
# registered source name. M1 confines an about-line to the closed vocabulary of scripts/trust/mention_vocab.txt, so the
# ways to point at a document WITHOUT those are the vocabulary words that denote a document, its parts or its authors.
# They were read off the whole vocabulary (1,626 words) by hand: a document or its part (article, page, paper,
# paragraph, footnote, table, tabulated, text, title, typeset, documentation, arxiv, wikipedia, source), the authors
# (author, they, them, their, themselves, who, whose), software whose output a statement is compared with (Cantera,
# DWSIM, pychemqt) and a journal (PRD). An about-line holding one of them names a source for M6. Also: 'the theorem /
# lemma / proposition / corollary' not followed by a code span (a result that is not one of ours, named by its kind).
# The vocabulary's personal names that were missing from source_surnames.txt were added (M8 also keeps the list
# closed for new vocabulary words: m8_vocab_names in m4).
M8_DOC_RE = re.compile(r"(?x)(?<![\w'’])(?:articles?|arxiv|authors?(?:['’]s)?|documentation|footnotes?|pages?|"
                       r"papers?(?:['’]s)?|paragraphs?|tables?(?:['’]s)?|tabulated|tabulations?|tbl|texts?|titles?|"
                       r"wikipedia|their|theirs|them|themselves|they|who|whose|typeset|sources?|"
                       r"cantera(?:['’]s)?|dwsim|pychemqt|prd|software)(?![\w'’])")
# hardened after red team M6r (run 2026-11-19T1428Z, not blind): a determiner (the, this, that, these, those) with up
# to two words between it and the kind, markup and punctuation between them read as spaces, and only a listed
# headline's own code span right after the kind exempts it (any code span did)
M8_KIND_RE = re.compile(r"(?<![\w'’])(?:the|this|that|these|those)\s+(?:[^\W\d_]+\s+){0,2}?"
                        r"(?:theorems?|lemmas?|propositions?|corollar(?:y|ies))(?![\w'’])(?!\s*zzheadlinespan\b)")
M8_HEAD_SPAN = "zzheadlinespan"
# M9 (run 2026-11-19T2028Z, part 3; decision rule pre-registered in runs/2026-11-19T2028Z/t5/reader_brief_EF.md before
# its readers ran). Reader test EF (nine blind Sonnet readers, blind grader, runs/2026-11-19T2028Z/t5/READERS_EF.md):
# lines that compare a statement with 'the formula' (a reference the reader cannot see) left an unrejected fidelity
# doubt in 2 of 3 readers ("the sentences do not say which 'formula' they mean, and I could not check them"); the same
# lines with no reference 0 of 3 (and 0 of 3 in test LN); with a model eponym ('to Gelfand') 1 of 3. So a determiner
# (the, this, that, these, those) with up to two words before one of the nouns that denote a formula or result outside
# the statement names a source for M6, unless a code span follows the noun (the content is shown) or the noun is the
# statement's own ('the equation in the statement', 'the formula of the statement'). Binds from its own commit.
M9_REF_RE = re.compile(r"(?<![\w'’])(?:the|this|that|these|those)\s+(?:[^\W\d_]+\s+){0,2}?"
                       r"(?:formulas?|formulae|equations?|expressions?|results?|versions?|derivations?|definitions?|"
                       r"notations?|specifications?|glossar(?:y|ies))(?![\w'’])"
                       r"(?!\s*(?:zzheadlinespan|zzcodespan)\b)"
                       r"(?!\s+(?:in|of|from)\s+(?:the|this|its|our)\s+(?:lean\s+)?(?:statements?|claims?|zzheadlinespan)\b)")


# M10 (run 2026-11-20T0228Z, part 3; decision rule pre-registered in runs/2026-11-20T0228Z/t5/BRIEF_EP2_M9h.md before its
# readers ran, as written in the LEDGER experiment of run 2026-11-19T2028Z). Reader test EP2 (nine blind Sonnet readers,
# blind grader, runs/2026-11-20T0228Z/t5/READERS_EP2.md): lines that compare a statement with a model eponym used as the
# reference ("the inverse order of the quantifiers to Gelfand", "the inverse of Falkner–Skan") left an unrejected
# fidelity doubt in 5 of 6 readers ("I would check the sign conventions against the source before citing"); the same
# lines with no reference 1 of 3 (blind grader; 0 of 3 by the run). So on a line about a listed headline, a model eponym
# (one name or a hyphenated pair, Falkner–Skan, Bonnor–Ebert) that is not directly followed by a noun of M10_NOUNS (the
# eponym used as a model's name: "the Gelfand problem", "the Falkner–Skan equation") names a source for M6. Names joined
# by 'and', 'or' or a slash are one group, judged by the word after the last ("the Hiemenz and Homann problems").
# Binds from its own commit.
M10_EPONYMS = frozenset("""bonnor ebert gelfand gel'fand peng robinson redlich kwong soave waals maxwell hartree eddington
falkner skan lane emden blasius michaelis menten duffing friedmann einstein sitter thomas fermi bratu liouville robertson
homann hiemenz joseph lundgren kamenetskii frank townes chandrasekhar banach chebyshev clenshaw crocco gibbs gronwall
hubble jordan lindelof lipschitz lyapunov milne picard radau ricci riemann rolle sylvester taylor volterra euclidean
gaussian hamiltonian jacobian laplacian""".split())
M10_JOIN = frozenset("de van der von and or".split())  # inside a group: de Sitter, van der Waals; joined names
M10_NOUNS = frozenset("""equation equations problem problems model models branch branches mass masses function functions
constant constants solution solutions polytrope polytropes sphere spheres flow flows layer layers boundary wall shear
row rows count counts critical coexistence rate rates field fields state states parameter parameters polynomial
polynomials expansion expansions prior soliton solitons oscillator oscillators mechanism network family families law
laws integral integrals inequality inequalities bound bounds transformation transformations variable variables step
steps recursion construction gluing argument arguments method methods iteration estimate estimates norm norms series
cell cells certificate certificates chain chains stack stacks integrator integrators factor factors coefficient
coefficients acentric value values number numbers quantity quantities radius radii temperature temperatures pressure
pressures profile profiles centre density densities energy case cases setting type separation extrema extremum turning
uniqueness existence window windows spiral cosmology universe metric fluid fluids kinetics reaction reactions
approximation limit limits point points stagnation initial slope gas isotherm isotherms inverse operator operators matrix matrices space spaces measure
measures domain domains condition conditions sequence sequences curve curves invariant invariants test tests system
systems pair pairs trio core cores atom atoms ansatz scale exponent exponents index""".split())
M10_GREEK = re.compile(r"[α-ωΑ-Ω]")
# M11 (run 2026-11-20T0828Z, part 3; decision rule pre-registered in runs/2026-11-20T0828Z/t5/BRIEF_DN.md before its
# readers ran). Held-out red team M10h (runs/2026-11-20T0828Z/t5/READERS_ND_M10h.md) got nine lines past M1-M10 that
# point at an unnamed reference by a determiner and a noun ('as in the model', 'the inverse of the theory', 'of the
# method', 'the dual of the physical problem', 'the rows of the data'); reader test DN (nine blind Sonnet readers,
# blind grader, runs/2026-11-20T0828Z/t5/READERS_DN.md): test EP2's lines with 'to the model' in place of the eponym
# left an unrejected fidelity doubt in 4 of 6 readers ("I would still check the models (the sign of e^w, the β term,
# the quantifier order) before citing"), a control with no line 0 of 3. So on a line about a listed headline, a
# determiner (the, this, that, these, those), optionally one qualifier of M11_QUAL, and a noun of M11_NOUNS (or
# 'problem(s)' after a qualifier) names a source for M6, unless a code span follows or the noun is the statement's own
# ('the model in the statement'). A named model ('the Gelfand model', 'the de Sitter model') is M10's case and passes
# here. Binds from its own commit.
# hardened after red team M11h (same run, not blind): 'the real problem' passed M11 in 4 of 20 unnamed-reference lines
M11_QUAL = r"(?:physical|original|standard|usual|classical|underlying|textbook|published|reference|common|known|real|actual|true)"
M11_REF_RE = re.compile(r"(?<![\w'’])(?:the|this|that|these|those)\s+(?:" + M11_QUAL + r"\s+)?"
                        r"(?:models?|theor(?:y|ies)|methods?|data|literature|textbooks?|references?|conventions?|"
                        r"physics)(?![\w'’])"
                        r"|(?<![\w'’])(?:the|this|that|these|those)\s+" + M11_QUAL + r"\s+(?:problems?|forms?|cases?)"
                        r"(?![\w'’])")
M11_OWN_RE = re.compile(r"\s*(?:zzheadlinespan|zzcodespan)\b"
                        r"|\s+(?:in|of|from)\s+(?:the|this|its|our)\s+(?:lean\s+)?(?:statements?|claims?|zzheadlinespan)\b")


def m11_ref(k):
    """M11 on a reduced line (as M9 reads it): True if a determiner + reference noun points at an unnamed model,
    theory, method, data or convention outside the statement"""
    return any(not M11_OWN_RE.match(k, m.end()) for m in M11_REF_RE.finditer(k))


def m10_eponym_ref(k):
    """M10 on a reduced line (code spans as marker words, markup and punctuation as spaces, lower case): True if a
    model eponym group is not directly followed by a noun of M10_NOUNS (or a Greek letter or one-letter symbol)"""
    ws = k.split()
    i, n = 0, len(ws)
    while i < n:
        w = ws[i][:-2] if ws[i].endswith(("'s", "’s")) else ws[i]
        if w not in M10_EPONYMS:
            i += 1
            continue
        j = i + 1  # extend the group over names, possessives and joiners followed by a name
        while j < n:
            x = ws[j][:-2] if ws[j].endswith(("'s", "’s")) else ws[j]
            if x in M10_EPONYMS:
                j += 1
            elif x in M10_JOIN and j + 1 < n and any(
                    (y[:-2] if y.endswith(("'s", "’s")) else y) in M10_EPONYMS for y in ws[j + 1:j + 4]
                    if y not in M10_JOIN) and all(y in M10_JOIN or (y[:-2] if y.endswith(("'s", "’s")) else y)
                                                  in M10_EPONYMS for y in ws[j + 1:j + 2]):
                j += 1
            else:
                break
        nxt = ws[j] if j < n else ""
        if not (nxt in M10_NOUNS or (len(nxt) == 1 and nxt.isalpha()) or M10_GREEK.fullmatch(nxt or "x")):
            return True
        i = j
    return False


def _m8_texts(line):
    """the two readings of a line M8 checks: HTML read as text (m6_text) and HTML removed (red team M6r: a word split
    by an empty comment or tag, 'ta<!---->ble', is one word on the rendered page and to M1)"""
    joined = re.sub(r"<!--.*?-->|<[^>]*>", "", html.unescape(html.unescape(line)), flags=re.S)
    return [m6_text(line), joined]


def m8_names(line, m9=True, m10=True, m11=True):
    """M8: the line points at a document, its parts or its authors by a vocabulary word, or at a result by its kind;
    M9 (m9=True): or at a formula or result outside the statement by a determiner and its kind;
    M10 (m10=True): or at a model by its eponym used as the reference (not followed by a noun of the model);
    M11 (m11=True): or at an unnamed model, theory, method, data or convention by a determiner and its noun"""
    keys, fulls, modules = headlines()
    for raw in _m8_texts(line):
        t = words(unmark(norm(raw)), fulls, modules)
        if M8_DOC_RE.search(t):
            return True
        # code spans that are a listed headline become one marker word; markup and punctuation become spaces
        k = re.sub(r"`([^`]*)`", lambda m: f" {M8_HEAD_SPAN} " if any(
            f == m.group(1).strip() or f.endswith("." + m.group(1).strip()) for f in fulls) else f" {m.group(1)} ", raw)
        k = re.sub(r"[^\w'’]+", " ", unmark(norm(k)).replace("`", " "))
        if M8_KIND_RE.search(k):
            return True
        if m9:
            # M9: every code span becomes a marker word (a listed headline's its own marker)
            k9 = re.sub(r"`([^`]*)`", lambda m: f" {M8_HEAD_SPAN} " if any(
                f == m.group(1).strip() or f.endswith("." + m.group(1).strip()) for f in fulls) else " zzcodespan ",
                re.sub(r"\bTHE RESULT\b", " zzprogram ", raw))  # the program's own plan (TARGETS.md), in capitals
            k9 = re.sub(r"[^\w'’]+", " ", unmark(norm(k9)).replace("`", " "))
            if M9_REF_RE.search(k9):
                return True
            if m10 and m10_eponym_ref(k9):
                return True
            if m10 and m11 and m11_ref(k9):
                return True
    return False


def names_source(line, m8_on=True):
    """M6's detector on both readings of the line (run 2026-11-19T1428Z, red team M6r: 'pa<span></span>per')"""
    joined = re.sub(r"<!--.*?-->|<[^>]*>", "", html.unescape(html.unescape(line)), flags=re.S)
    return _names_source(line, m8_on) or (joined != line and _names_source(joined, m8_on))


def _names_source(line, m8_on=True):
    """M6's source detector (run 2026-11-19T0228Z; hardened after red team M4 the same run, not blind): code spans that
    are not a headline, module or path are read; separators inside a digit run are dropped before the year test;
    initials, number words after 'table' etc. and spelled-out years name a source too"""
    raw = m6_text(line)
    if INITIAL_RE.search(raw):
        return True
    keys, fulls, modules = headlines()
    t = words(unmark(norm(raw)), fulls, modules)
    t = _DATE2.sub(" ", t)
    t2 = re.sub(r"(?<=\d)[\s.·'’_-]+(?=\d)", "", t)
    if re.search(r"(?<!\d)(?:1[89]|20)\d\d(?!\d)", t2):
        return True
    if SRC_RE.search(t) or NUMWORD_RE.search(t):
        return True
    ws = {w.replace("’", "'") for w in re.findall(r"[^\W\d_]+(?:['’][^\W\d_]+)?", t)}
    if {w[:-2] if w.endswith("'s") else w for w in ws} & surnames():
        return True
    r = source_names_re()
    if r and r.search(raw):
        return True
    return bool(m8_on) and m8_names(line, m9=(m8_on not in ("m8only",)), m10=(m8_on in (True, "m10only")),
                                     m11=(m8_on is True))


CITE = re.compile(r"(?:[A-ZÀ-Þ][\w'’\-–]+(?:\s*(?:,|and|&)\s*[A-ZÀ-Þ][\w'’\-–]+)*(?:\s+et\.?\s+al\.?)?,?\s*[(\[]?"
                  r"(?:18|19|20)\d\d[a-z]?[)\]]?)")


def m6(line, t_free, m8_on=True):
    if not names_source(line, m8_on):
        return []
    # citation spans are read from the raw line (capitals; inside code spans too), then the line goes through the same
    # reduction as M1, with code spans that are not names kept as words and HTML read as text
    raw = CITE.sub(" ", m6_text(line))
    keys, fulls, modules = headlines()
    n = unmark(norm(raw))
    for r in TEMPLATE_RE:
        n = r.sub(" ", n)
    t = _DATE2.sub(" ", words(n, fulls, modules))
    t = re.sub(r"\b\d+(?:\.\d+)*\b", " ", t)
    extra = sorted({w for w in tokens(t) if (len(w) > 1 or w.isupper()) and w not in SRC_OK and w not in surnames()
                    and not (w.endswith("'s") and w[:-2] in surnames())})
    sym = sorted(set(FORMULA.findall(t)))
    if INITIAL_RE.search(m6_text(line)):
        extra = sorted(set(extra) | {"(initials)"})
    errs = []
    if extra:
        errs.append(f"M6 a line naming a source and a listed headline carries words beyond the citation: "
                    f"{', '.join(extra[:12])}")
    if sym:
        errs.append(f"M6 formula characters on a line naming a source and a listed headline: {' '.join(sym)}")
    return errs


# M7 (run 2026-11-19T0828Z, part 3; runs/2026-11-19T0828Z/t5/READERS_LN.md, READERS_L2R.md, READERS_L2S.md): a line
# relating a headline to a NAMED source left a fidelity doubt in 9/9 blind readers, the same line with no source in 0/3,
# and no page-side evidence (the blind readings printed on the claims page) moved them. M6 is the guard; its detector
# reads a year-less source only through source_surnames.txt ("the sign of Ganapol's table"). M7 keeps that list closed:
# an author-year citation on a new line of any scanned record (whole run READMEs included) whose author surname is not
# in source_surnames.txt fails; add the surname (grow-only, with a LEDGER line naming source_surnames).
M7_NOT_NAMES = frozenset("""run runs ledger the on one see table tables eq equation section fig figure theorem lemma
appendix and et al jan feb mar apr may jun jul aug sep sept oct nov dec january february march april june july august
september october november december
bonnor ebert gelfand gel'fand peng robinson redlich kwong soave van der waals maxwell hartree eddington falkner skan
lane emden blasius michaelis menten duffing friedmann einstein sitter thomas fermi bratu liouville robertson
alexander""".split())
M7_YEAR = re.compile(r"(?<![\w.\-])(?:18|19|20)\d\d[a-z]?(?![\w\-])")
M7_LINK = frozenset("and & , et al al. et. ( [ – - of".split())


def m7_missing(line):
    """surnames of the author-year citations of LINE that source_surnames.txt lacks (acronyms, tokens with digits and
    month or record words are not surnames)"""
    raw = re.sub(r"\b20[2-9]\d-\d\d-\d\d(?:T\d{4}Z)?\b", " ", m6_text(line))
    raw = re.sub(r"`[^`]*`", " ", raw)
    out = []
    for m in M7_YEAR.finditer(raw):
        # the citation is the run of capitalised words (joined by and, &, commas, dashes, et al.) right before the year
        toks = re.findall(r"[^\s,()\[\]–]+|[,()\[\]–]", raw[max(0, m.start() - 160):m.start()])[::-1]
        names = []
        for t in toks[:12]:
            if t.lower() in M7_LINK or t in ",()[]–":
                continue
            if re.fullmatch(r"[A-ZÀ-Þ][^\W\d_]*(?:['’][^\W\d_]+)?(?:-[A-ZÀ-Þ][^\W\d_]*)*", t):
                names.append(t)
                continue
            break
        for tok in names:
            for part in tok.split("-"):
                base = re.sub(r"['’]s$", "", part)
                if len(base) < 2 or base.isupper() or base.lower() in M7_NOT_NAMES or norm(base) in M7_NOT_NAMES:
                    continue
                if base.lower() in surnames() or norm(base) in surnames():
                    continue
                out.append(base)
    return out


def m7(base_files, head_files):
    old = {ident(l) for txt in base_files.values() for l in txt.splitlines()}
    errs = []
    for path, txt in sorted(head_files.items()):
        for i, l in enumerate(txt.splitlines()):
            if not l.strip() or ident(l) in old:
                continue
            miss = sorted(set(m7_missing(l)))
            if miss:
                errs.append(f"{path}:{i + 1}: M7 an author-year citation names a surname not in "
                            f"scripts/trust/source_surnames.txt (add it with a LEDGER line naming source_surnames): "
                            f"{', '.join(miss)}")
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
    # red team M4 (run 2026-11-19T0228Z): norm() deletes HTML, so a line that is one HTML comment had the identity of a
    # blank line and was never new; the identity reads tags and comments as text
    return re.sub(r"^(last updated|previous update):\s*", "", norm(m6_text(line)).strip())


def run(base_files, head_files, vocab=None, obj=None, grand=None, m6_pre=None, m8_pre=None, m9_pre=None, m10_pre=None,
        m11_pre=None):
    """grand = (idents of lines that existed before the last vocabulary rebuild, the vocabulary they were written
    under): such a line, new since a base older than the rebuild, is read by M1 with that vocabulary too"""
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
            v = vocab | grand[1] if grand and gident(l) in grand[0] else vocab
            for e in check_line(l, fulls, modules, v, obj, path, ab,
                                m6_on=not (m6_pre and ident(l) in m6_pre),
                                m8_on=(False if (m8_pre and ident(l) in m8_pre) else
                                       "m8only" if (m9_pre and ident(l) in m9_pre) else
                                       "m9only" if (m10_pre and ident(l) in m10_pre) else
                                       "m10only" if (m11_pre and ident(l) in m11_pre) else True)):
                short = ", ".join(sorted(f.split(".")[-1] for f in ab)[:4])
                errors.append(f"{path}:{i + 1}: about {short}: {e}")
    return errors


def gident(line):
    """identity for the vocabulary grandfather rule: the line with its status-template spans removed, so a heading
    whose only change is its status template (pending -> judged) keeps the vocabulary it was written under"""
    t = ident(line)
    for r in TEMPLATE_RE:
        t = r.sub(" ", t)
    return re.sub(r"\s+", " ", t).strip()


REBUILD_MARK = "# Rebuilt run 2026-11-18T2028Z"  # header line of the vocabulary's last rebuild (update on a rebuild)


def grandfathered(base):
    """lines written before the last vocabulary rebuild keep the vocabulary they were written under (run
    2026-11-18T2028Z: the rebuild must not make records of earlier runs, never judged by CI under it, fail)"""
    r = git("log", "--format=%H", "-S", REBUILD_MARK, "--", VOCAB).split()
    if not r:
        return None
    rebuild = r[-1]
    if subprocess.run(["git", "merge-base", "--is-ancestor", rebuild, base], cwd=ROOT).returncode == 0:
        return None  # the base already has the rebuilt vocabulary
    before = files_at(rebuild + "^")
    idents = {gident(l) for txt in before.values() for l in txt.splitlines()}
    return idents, load_vocab(git("show", f"{rebuild}^:{VOCAB}"))


def m6_grandfathered(base):
    """M6 binds from the commit that introduced it (run 2026-11-19T0228Z): lines that existed in its parent are not
    read by M6 (they were written, and judged by CI, before the rule)"""
    r = git("log", "--format=%H", "-S", "def m6(", "--", "scripts/trust/check_headline_mentions.py").split()
    if not r:
        return None
    intro = r[-1]
    if subprocess.run(["git", "merge-base", "--is-ancestor", intro, base], cwd=ROOT).returncode == 0:
        return None
    return {ident(l) for txt in files_at(intro + "^").values() for l in txt.splitlines()}


def m8_grandfathered(base):
    """M8 binds from the commit that introduced it (run 2026-11-19T1428Z): lines that existed in its parent are not
    read by M8"""
    r = git("log", "--format=%H", "-S", "def m8_names(", "--", "scripts/trust/check_headline_mentions.py").split()
    if not r:
        return None
    intro = r[-1]
    if subprocess.run(["git", "merge-base", "--is-ancestor", intro, base], cwd=ROOT).returncode == 0:
        return None
    return {ident(l) for txt in files_at(intro + "^").values() for l in txt.splitlines()}


def m9_grandfathered(base):
    """M9 binds from the commit that introduced it (run 2026-11-19T2028Z): lines that existed in its parent are not
    read by M9 (M8 still reads them)"""
    r = git("log", "--format=%H", "-S", "M9_REF_RE = re.compile(", "--", "scripts/trust/check_headline_mentions.py").split()
    if not r:
        return None
    intro = r[-1]
    if subprocess.run(["git", "merge-base", "--is-ancestor", intro, base], cwd=ROOT).returncode == 0:
        return None
    return {ident(l) for txt in files_at(intro + "^").values() for l in txt.splitlines()}


def m10_grandfathered(base):
    """M10 binds from the commit that introduced it (run 2026-11-20T0228Z): lines that existed in its parent are not
    read by M10 (M8 and M9 still read them as before)"""
    r = git("log", "--format=%H", "-S", "M10_EPONYMS = frozenset(", "--", "scripts/trust/check_headline_mentions.py").split()
    if not r:
        return None
    intro = r[-1]
    if subprocess.run(["git", "merge-base", "--is-ancestor", intro, base], cwd=ROOT).returncode == 0:
        return None
    return {ident(l) for txt in files_at(intro + "^").values() for l in txt.splitlines()}


def m11_grandfathered(base):
    """M11 binds from the commit that introduced it (run 2026-11-20T0828Z): lines that existed in its parent are not
    read by M11 (M8, M9 and M10 still read them as before)"""
    r = git("log", "--format=%H", "-S", "M11_REF_RE = re.compile(", "--", "scripts/trust/check_headline_mentions.py").split()
    if not r:
        return None
    intro = r[-1]
    if subprocess.run(["git", "merge-base", "--is-ancestor", intro, base], cwd=ROOT).returncode == 0:
        return None
    return {ident(l) for txt in files_at(intro + "^").values() for l in txt.splitlines()}


def m7_binds(base):
    """M7 binds from the commit that introduced it: for an older base, lines written before it are not re-read"""
    r = git("log", "--format=%H", "-S", "def m7(", "--", "scripts/trust/check_headline_mentions.py").split()
    if not r:
        return True  # uncommitted: the working tree introduces it
    return subprocess.run(["git", "merge-base", "--is-ancestor", r[-1], base], cwd=ROOT).returncode == 0


# M8 (vocabulary names): a word that enters mention_vocab.txt and is written as a name in the records (capitalised
# inside a sentence, not an acronym) must be a listed source surname or one of these eponyms of a concept, model or
# method (classified by hand, run 2026-11-19T1428Z; grow with a LEDGER line naming check_headline_mentions)
M8_EPONYMS = frozenset("""banach chebyshev clenshaw crocco frank gibbs gronwall hiemenz hubble jordan lindelof lipschitz
lyapunov milne picard radau ricci riemann rolle sylvester taylor townes volterra euclidean gaussian hamiltonian jacobian
laplacian eddington greek latin
claude github lean mathlib opus python sonnet webfetch commonmark gui ici lt pi pr prop quot sec en eds ch apoly cq
eqs""".split())


def m8_vocab_names(added, files):
    """added vocabulary words written as names in FILES (capitalised mid-sentence at least twice and at least four
    times as often as in lower case, never all capitals) that are neither listed surnames nor M8_EPONYMS"""
    cap, low = {}, {}
    want = set(added)
    for txt in files.values():
        t = re.sub(r"`[^`]*`", " ", txt)
        for m in re.finditer(r"(?<![\w.\-/])([^\W\d_][\w'’]*)", t):
            w = m.group(1)
            if w.isupper() or any(c.isupper() for c in w[1:]) or not w.isascii() or re.search(r"[.!?:#*\-]\s*$|^\s*$|\n", t[max(0, m.start() - 2):m.start()]):
                continue
            k = re.sub(r"'s$", "", norm(w).replace("’", "'"))
            if k in want or k + "'s" in want:
                d = cap if w[0].isupper() else low
                d[k] = d.get(k, 0) + 1
    return sorted(k for k in cap if cap[k] >= 2 and cap[k] >= 4 * low.get(k, 0) and k not in surnames()
                  and k not in M7_NOT_NAMES and k not in M8_EPONYMS and not M8_DOC_RE.fullmatch(k))


def m4(base):
    errs = []
    diff = git("diff", f"{base}..HEAD", "--", VOCAB)
    added = [l[1:].strip() for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++")]
    added = [w for w in added if w and not w.startswith("#")]
    if added:
        ledger = git("diff", f"{base}..HEAD", "--", "LEDGER.md")
        if not any(l.startswith("+") and "mention_vocab" in l for l in ledger.splitlines()):
            errs.append(f"M4 {VOCAB} grew ({len(added)} words) without an added LEDGER line naming mention_vocab")
        names = m8_vocab_names(added, files_at(None))
        if names:
            errs.append(f"M8 words written as names entered {VOCAB} without a listing in "
                        f"scripts/trust/source_surnames.txt or M8_EPONYMS: {', '.join(names)}")
        bad = [w for w in added if STATUS.match(w)]
        if bad:
            errs.append(f"M4 status words may never enter {VOCAB}: {', '.join(bad)}")
    sdiff = git("diff", f"{base}..HEAD", "--", "scripts/trust/check_headline_mentions.py")
    if any(l.startswith("-") and not l.startswith("---") and ("r\"" in l or "r'" in l) for l in sdiff.splitlines()):
        ledger = git("diff", f"{base}..HEAD", "--", "LEDGER.md")
        if not any(l.startswith("+") and "check_headline_mentions" in l for l in ledger.splitlines()):
            errs.append("M4 STATUS/TEMPLATES of check_headline_mentions.py changed without an added LEDGER line naming it")
    return errs


# red team M4 (run 2026-11-19T0228Z, runs/2026-11-19T0228Z/t5/m4_lines.txt): the lines that passed a75aa502 and are
# flagged after the hardening of the same run (not blind); each is a defect control under the Gelfand heading
M4_LINES = [
    "`gelfand_pde_radial_many_centre` has the inverse order of the quantifiers of the theorem of J. and L. 19 73.",
    "`gelfand_extrema` has the inverse order of the quantifiers of the theorem of J. and L.",
    "`gelfand_extrema` has the inverse order of the quantifiers of the theorem of J. and L. 1 973.",
    "`gelfand_extrema` has the inverse order of the quantifiers of the theorem of J. and L. 19·73.",
    "`gelfand_extrema` has the reverse sign of the constant of the theorem of `Joseph and Lundgren 1973`.",
    "`gelfand_extrema` has the inverse order of the quantifiers of the theorem of `Joseph` and `Lundgren`.",
    "`gelfand_extrema` has the inverse order of the quantifiers of the theorem of J. and L. 1973-74.",
    "`gelfand_extrema` has the inverse order of the quantifiers of the theorem of J. and L.1973.",
    "`gelfand_extrema` has the inverse order of the quantifiers of the theorem of J. and L. 1973ab.",
    "`gelfand_extrema` has the inverse order of the quantifiers of the theorem of J. and L. one nine seven three.",
    "`fs_neg_reversed_wall_shear_3_exists` has the inverse sign of the wall shear of table seven.",
    "`fs_neg_reversed_wall_shear_3_exists` has the inverse sign of the wall shear of `Ganapol 2010 Table 7`.",
    "`fs_neg_reversed_wall_shear_3_exists` has the inverse sign of the wall shear of `Ganapol` 20 10.",
    "`table5_oL_aicc_unattainable` has the reverse order of the data of table five of `Moresco 2016`.",
    "`fr13_minval68` has the inverse sign of the value of F. and R. 20 13.",
    "The constant of `fr13_minval68` is the inverse of the constant of `Farooq and Ratra 2013`.",
    "`fr13_minval68` has the inverse sign of the value of the `Farooq` data.",
    '<span title="Joseph and Lundgren 1973">`gelfand_pde_radial_many_centre` has the inverse order of the quantifiers '
    'of the theorem.</span>',
    "<!-- `gelfand_extrema` has the inverse order of the quantifiers of the theorem of Joseph and Lundgren 1973 -->",
    "`gelfand_extrema` has a strictly positive upper bound where the theorem of `Joseph and Lundgren 1973` has the dual.",
]
# M8 (run 2026-11-19T1428Z, written before its red teams): sources pointed at without a name, year or numbered part;
# each passed M1-M7 at 73af250a
M8_LINES = [
    "- `gelfand_extrema`: the statement has the inverse sign of the exponent of the Gidas Nirenberg theorem.",
    "- `gelfand_extrema`: the statement has the inverse sign of the exponent in their table.",
    "- `fs_neg_reversed_wall_shear_3_exists`: the tabulated wall shear has the inverse sign.",
    "- `gelfand_extrema`: the statement is the dual of the theorem, with the inverse order of the quantifiers.",
]
# red teams M5 (held-out, against 73af250a: 16 of its 17 class-A lines flagged by M8 as committed in 6140a8b8) and
# M6r (against 6140a8b8; 22 detector gaps closed after the report, not blind); runs/2026-11-19T1428Z/t5/
M8_RT_LINES = [
    "`laneEmden4_constants`: the Python code of the software has the inverse constant.",
    "`gelfand_extrema` sign in tension with that lemma.",
    "`gelfand_pde_radial_many_centre` values in tension with this theorem.",
    "`bonnor_ebert_count` in tension with the above theorem.",
    "`laneEmden4_constants` constant in tension with the first lemma.",
    "`fr13_minval68` value in tension with the **theorem**.",
    "`gelfand_extrema` sign in tension with the <b>theorem</b>.",
    "`gelfand_extrema` sign in tension with the (theorem).",
    "`gelfand_extrema` sign in tension with the/theorem.",
    "`gelfand_extrema` sign in tension with the theo<!---->rem.",
    "`gelfand_extrema` sign in tension with the ta<!---->ble.",
    "`gelfand_extrema` sign in tension with the<!---->ir values.",
    "`gelfand_extrema` sign in tension with Cant<!---->era.",
    "`gelfand_extrema` sign in tension with the pa<span></span>per.",
    "`gelfand_extrema` sign in tension with the &theorem.",
    "`gelfand_extrema` sign in tension with the [theorem](x).",
    "`gelfand_extrema` sign in tension with the theorem `lam`.",
    "`gelfand_extrema`: the order of the quantifiers is the inverse of the Wikipedia statement.",
    "`fs_neg_reversed_wall_shear_3_exists`: <!-- Wikipedia --> the sign of the shear at the wall is the inverse of the "
    "table.",
]
# M9 (run 2026-11-19T2028Z): reader test EF arm F (2 of 3 blind readers kept an unrejected fidelity doubt), and the
# markup forms red team M6r found for M8, applied to the M9 nouns
M9_LINES = [
    "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers of the formula.",
    "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent of the formula.",
    "- `fs_neg_reversed_wall_shear_3_exists`: the sign of the pressure gradient term in the equation is the inverse of "
    "the formula.",
    "`gelfand_extrema` sign in tension with the definition.",
    "`gelfand_extrema` sign in tension with the <b>formula</b>.",
    "`gelfand_extrema` sign in tension with the fo<!---->rmula.",
    "`gelfand_extrema` sign in tension with the original result.",
]
# M10 (run 2026-11-20T0228Z): reader test EP2 arm EP (5 of 6 blind readers kept an unrejected fidelity doubt), and the
# same shape with another model eponym, a possessive and markup inside the name
M10_LINES = [
    "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers to Gelfand.",
    "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent to Gelfand.",
    "- `fs_neg_reversed_wall_shear_3_exists`: the sign of the pressure gradient term in the equation is the inverse of "
    "Falkner–Skan.",
    "`gelfand_extrema` sign in tension with Bonnor–Ebert.",
    "`gelfand_extrema` sign in tension with Gelfand's.",
    "`gelfand_extrema` sign in tension with Gel<!---->fand.",
    "`gelfand_extrema` sign in tension with Emden and Chandrasekhar.",
]
# M11 (run 2026-11-20T0828Z): reader test DN arm DN (4 of 6 blind readers kept an unrejected fidelity doubt), and the
# nine determiner + noun lines of held-out red team M10h that passed M1-M10
M11_LINES = [
    "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers to the model.",
    "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent to the model.",
    "- `fs_neg_reversed_wall_shear_3_exists`: the pressure gradient term has the inverse sign to the model.",
    "- `gelfand_pde_radial_many_centre` is the dual of the physical problem, with radius rescaled.",
    "- `gelfand_pde_radial_many_centre` is the inverse of the model, in a ball of radius two.",
    "- `gelfand_pde_radial_many_centre` is a ball of dimension two, as in the theory.",
    "- In `gelfand_pde_radial_many_centre` the parameter is scaled by two, as in the model.",
    "- `gelfand_pde_radial_many_centre` has the reverse sign of the exponential nonlinearity in the model.",
    "- `gelfand_extrema` has the first branch of the method, in ball dimension three.",
    "- `fs_neg_reversed_wall_shear_3_exists` has wall shear of the model with inverse sign.",
    "- `fs_neg_reversed_wall_shear_3_exists` has the rows of the data.",
    # red team M11h (same run): the qualifier 'real'
    "- `gelfand_pde_radial_many_centre` has the inverse order of the quantifiers of the real problem.",
    "- `gelfand_pde_radial_many_centre` has the sign of the derivative inverse to the real problem.",
    "- `gelfand_extrema` has half the solutions of the real problem.",
    "- `fs_neg_reversed_wall_shear_3_exists` has half the parameter of the real problem.",
]
# recorded limits of M8 (red team M6r, not controls): eponyms of models in headline names used as a source
# ("in tension with Gelfand / Emden / Kamenetskii / Eddington's") and words that are not document words ("in tension
# with the formula / the equation / the definition / the notation / the specification / the glossary"); the last kind
# names no source a reader cannot see (reader test LN, class b: 0/3 misled)
# recorded limits of M6 (red team M4; not controls): a source described generically ("of the table", "of the Gelfand
# theorem"), a name outside source_surnames.txt ("the Falkner and Skan solution"), the citation on a neighbouring line,
# and every line that names no source (class b), e.g. "`gelfand_extrema` has the inverse sign of the exponent."
# Measured (run 2026-11-19T0828Z, runs/2026-11-19T0828Z/t5/READERS_LN.md, nine blind readers, blind grader): class b
# left a fidelity doubt in 0/3 readers (each refuted the line from the generated statement), the source-naming lines in
# 3/3, a control 0/3: the named source, which the reader cannot see, carries the harm; the generic description of a
# source ("of the table") is in that class and stays open here.


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
        # run 2026-11-18T2028Z (found by the author while rebuilding the vocabulary, not by a red team): STATUS words
        # inside the free part of a template passed M2, and M1 skips STATUS words
        "- PROVED (CI 44261574038 of adcb9a6 green on every job, but do not cite it).",
        "- `gelfand_pde_radial_many_centre`: PROVED (CI 44261574038 of adcb9a6, a descendant of a commit that is not to "
        "be cited, green on every job).",
        # red team M3 (run 2026-11-18T2028Z), against cd66956b; mechanism 4 (in-vocabulary dispute) is a recorded limit
        "The third maximum of the Bonnor–Ebert mass result is no longer to be cited: a referee found that it does not "
        "say what the paper says.",
        "The radial many centre theorem is struck off by the referee; do not cite it.",
        "The `radial_many_centre` theorem is dead and must not be relied on.",
        "The many-centre theorem is wrong: do not cite or rely on it; it does not say what the paper says.",
        "The Gelfand radial many center theorem is no longer to be cited.",
        "The `pde_radial_manγ_ϲentre` theorem (Gelfand PDE) is no longer to be cited: a referee found a fault.",
        # reader test L2 (run 2026-11-18T2028Z: a false doubt about fidelity in 3/3 readers), closed by M6 (run
        # 2026-11-19T0228Z); under the Gelfand multiplicity heading, so each is about a listed headline
        "- `gelfand_pde_radial_many_centre`: the statement is the dual of the theorem of Joseph and Lundgren 1973, with "
        "the inverse order of the quantifiers.",
        "- `gelfand_extrema`: the equation in the statement is the equation of Joseph and Lundgren 1973 with the inverse "
        "sign of the exponent.",
        "- `fs_neg_reversed_wall_shear_3_exists`: the sign of the pressure gradient term in the equation is the inverse "
        "of the sign in Table 7 of Ganapol 2010.",
        "- `gelfand_pde_radial_many_centre`: the statement is the dual of the theorem of Joseph and Lundgren.",
        "- `gelfand_extrema`: Joseph and Lundgren (1973) have `+e^w` in the equation of the statement.",
    ] + M4_LINES + M8_LINES + M8_RT_LINES + M9_LINES + M10_LINES + M11_LINES
    # known limit (recorded, not a control; red team M3 mechanism 4, reader test L of run 2026-11-18T2028Z misled 0/3):
    # "`gelfand_pde_radial_many_centre`: the statement is the dual of the paper theorem, with the inverse order of the
    # quantifiers." passes. Earlier recorded limit: a status in ordinary in-vocabulary words, e.g.
    # "`gelfand_pde_radial_many_centre`: the quantifiers are the other way round from the paper's theorem." passes
    goods = [
        "- Not claimed: the number of radial solutions for λ between λ₁ and λ₂.",  # run 2026-11-18T2028Z: vocabulary rebuilt
        "- Promoted to Checked + AUDITED; PROVED (CI 44261574038 of adcb9a6 green on every job incl. the checked job).",
        # M6 (run 2026-11-19T0228Z): a bare citation of the source passes
        "- `gelfand_pde_radial_many_centre` (Joseph and Lundgren 1973, Theorem 2).",
        # M8 (run 2026-11-19T1428Z): a bare pointer at the source passes; a theorem named by its code span is ours
        "- `gelfand_pde_radial_many_centre` (table).",
        "- `gelfand_extrema`: the theorem `gelfand_extrema` is in Lean.",
        # M9 (run 2026-11-19T2028Z): the statement's own equation, and a formula shown as a code span, are not a source
        "- `gelfand_extrema`: the sign of the exponent in the equation of the statement is positive.",
        "- `gelfand_extrema`: the sign is the inverse of the result `lam`.",
        # M10 (run 2026-11-20T0228Z): an eponym used as the name of a model, followed by its noun or a symbol
        "- `gelfand_extrema`: the Gelfand problem in the 3-D ball, Falkner–Skan β = 1/2.",
        "- `gelfand_extrema`: the de Sitter model and the van der Waals equation.",
        # M11 (run 2026-11-20T0828Z): a named model, and the statement's own model, are not an unnamed reference
        "- `gelfand_extrema`: the Gelfand model in the 3-D ball.",
        "- `gelfand_extrema`: the sign of the exponent in the model of the statement is positive.",
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
    # red team M3 (run 2026-11-18T2028Z): the same lines appended at the end of README.md, away from any name context
    for d in defects[-6:]:
        new = dict(head)
        new["README.md"] = head["README.md"].rstrip("\n") + "\n\n" + d + "\n"
        if not run(base, new):
            print(f"selftest FAIL: defect passed at the end of README.md: {d}")
            fails += 1
    # M3: a registered objection with this file as its path licenses the line
    keys, fulls, _ = headlines()
    full = next(f for f in fulls if f.endswith("gelfand_pde_radial_many_centre"))
    new = dict(head)
    new["STATE.md"] = ins(st, defects[0])
    if run(base, new, obj={full: {"STATE.md"}}):
        print("selftest FAIL: registered objection did not license the line (M3)")
        fails += 1
    # M7 (run 2026-11-19T0828Z): an author-year citation with a surname outside source_surnames.txt fails anywhere in a
    # scanned record (a run README body too); listed surnames, record dates and model names pass
    m7_bad = ["- The reversed-flow rows agree with Quixote and Panza 1999 to eight digits.",
              "- Detail: the constants follow Sancho et al. (2003), Table 2.",
              "- The sign is the one of Rocinante-Dulcinea 2011."]
    m7_good = ["- The rows agree with Ganapol 2010 Table 7 and Joseph and Lundgren 1973.",
               "- Run 2026-11-19T0828Z read CI 44478483601 on 2026-11-19.",
               "- The Peng–Robinson 1976 form and the Lane–Emden equation (Chandrasekhar 1939)."]
    rr = "runs/2026-11-19T0828Z/README.md"
    for d in m7_bad:
        new = dict(head)
        new[rr] = head.get(rr, "# Run\n").rstrip("\n") + "\n\n## Start\n" + d + "\n"
        if not m7(head, new):
            print(f"selftest FAIL: M7 defect passed in a run README body: {d}")
            fails += 1
    for g in m7_good:
        new = dict(head)
        new[rr] = head.get(rr, "# Run\n").rstrip("\n") + "\n\n## Start\n" + g + "\n"
        if m7(head, new):
            print(f"selftest FAIL: M7 flagged a correct line: {g}: {m7(head, new)}")
            fails += 1
    # M8 vocabulary names: a new vocabulary word written as a name must be listed
    if m8_vocab_names(["zzquixote", "zzpanza"], {"x.md": "We read Zzquixote here and Zzquixote there; zzpanza, zzpanza."}) \
            != ["zzquixote"]:
        print("selftest FAIL: M8 vocabulary names")
        fails += 1
    print(f"check_headline_mentions selftest: {len(defects)} defects, {len(goods)} correct lines, M3, "
          f"M7 {len(m7_bad)}+{len(m7_good)}; "
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
    if "--words" in argv:  # (authoring aid, run 2026-11-18T2028Z) words of a draft line outside the vocabulary / STATUS
        keys, fulls, modules = headlines()
        t = words(norm(" ".join(argv[argv.index("--words") + 1:])), fulls, modules)
        print("not in vocabulary:", " ".join(sorted({w for w in tokens(t) if len(w) > 1 and w not in load_vocab()
                                                      and not STATUS.match(w)})) or "-")
        print("STATUS words:", " ".join(sorted({w for w in tokens(t) if STATUS.match(w)})) or "-")
        return 0
    if "--seed-vocab" in argv:
        seed()
        return 0
    if "--base" in argv:
        base = argv[argv.index("--base") + 1]
        green_base = base  # the newest green ancestor as given (check_stale_status needs it unmoved)
        # the rule binds from the commit that introduced this script: lines older than it are not new to the rule
        intro = git("log", "--diff-filter=A", "--format=%H", "--", "scripts/trust/check_headline_mentions.py").split()
        if intro and subprocess.run(["git", "merge-base", "--is-ancestor", base, intro[-1]], cwd=ROOT).returncode == 0:
            base = intro[-1]
        if selftest():
            return 1
        bf, hf = files_at(base), files_at(None)
        errors = run(bf, hf, grand=grandfathered(base), m6_pre=m6_grandfathered(base),
                     m8_pre=m8_grandfathered(base), m9_pre=m9_grandfathered(base),
                     m10_pre=m10_grandfathered(base), m11_pre=m11_grandfathered(base)) + m4(base)
        errors += m7(bf, hf) if m7_binds(base) else []
        # run 2026-11-18T2028Z: stale pending statuses in STATE.md headings (check_stale_status.py; called from here so
        # the workflow file, and with it the nanoda/leanchecker memo hash, need not change)
        import check_stale_status
        if "--no-stale" in argv:  # authoring aid for scripts/check_commit_msg.py --final (run 2026-11-25T0228Z): the
            # base there is origin/main, not the newest green ancestor, so the stale-status rule would misfire; CI
            # never passes this flag and always runs the stale rule
            pass
        elif check_stale_status.selftest():
            errors.append("check_stale_status selftest failed")
        heads_reg = check_stale_status.registered()
        stale = [] if "--no-stale" in argv else check_stale_status.findings((ROOT / "STATE.md").read_text(encoding="utf-8"), heads_reg,
                                            functools.lru_cache(maxsize=None)(check_stale_status.intro_commit),
                                            lambda c: check_stale_status.is_ancestor(c, green_base))
        errors += [f"STATE.md:{n}: STALE pending status (check_stale_status.py): {', '.join(h.split('.')[-1] for h in hs)} "
                   f"entered the registry in an ancestor of the green base {green_base[:12]}: write the judged template "
                   f"'PROVED (CI <run> of <sha>, a descendant, green on every job …)'" for n, _, hs in stale]
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
