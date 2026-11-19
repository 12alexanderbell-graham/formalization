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


def check_line(line, fulls, modules, vocab, open_obj, path, ab, m6_on=True):
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
        errs += m6(line, t_free)
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


def names_source(line):
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
    return bool(r and r.search(raw))


CITE = re.compile(r"(?:[A-ZÀ-Þ][\w'’\-–]+(?:\s*(?:,|and|&)\s*[A-ZÀ-Þ][\w'’\-–]+)*(?:\s+et\.?\s+al\.?)?,?\s*[(\[]?"
                  r"(?:18|19|20)\d\d[a-z]?[)\]]?)")


def m6(line, t_free):
    if not names_source(line):
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


def run(base_files, head_files, vocab=None, obj=None, grand=None, m6_pre=None):
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
                                m6_on=not (m6_pre and ident(l) in m6_pre)):
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
# recorded limits of M6 (red team M4; not controls): a source described generically ("of the table", "of the Gelfand
# theorem"), a name outside source_surnames.txt ("the Falkner and Skan solution"), the citation on a neighbouring line,
# and every line that names no source (class b), e.g. "`gelfand_extrema` has the inverse sign of the exponent."


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
    ] + M4_LINES
    # known limit (recorded, not a control; red team M3 mechanism 4, reader test L of run 2026-11-18T2028Z misled 0/3):
    # "`gelfand_pde_radial_many_centre`: the statement is the dual of the paper theorem, with the inverse order of the
    # quantifiers." passes. Earlier recorded limit: a status in ordinary in-vocabulary words, e.g.
    # "`gelfand_pde_radial_many_centre`: the quantifiers are the other way round from the paper's theorem." passes
    goods = [
        "- Not claimed: the number of radial solutions for λ between λ₁ and λ₂.",  # run 2026-11-18T2028Z: vocabulary rebuilt
        "- Promoted to Checked + AUDITED; PROVED (CI 44261574038 of adcb9a6 green on every job incl. the checked job).",
        # M6 (run 2026-11-19T0228Z): a bare citation of the source passes
        "- `gelfand_pde_radial_many_centre` (Joseph and Lundgren 1973, Theorem 2).",
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
        errors = run(files_at(base), files_at(None), grand=grandfathered(base), m6_pre=m6_grandfathered(base)) + m4(base)
        # run 2026-11-18T2028Z: stale pending statuses in STATE.md headings (check_stale_status.py; called from here so
        # the workflow file, and with it the nanoda/leanchecker memo hash, need not change)
        import check_stale_status
        if check_stale_status.selftest():
            errors.append("check_stale_status selftest failed")
        heads_reg = check_stale_status.registered()
        stale = check_stale_status.findings((ROOT / "STATE.md").read_text(encoding="utf-8"), heads_reg,
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
