#!/usr/bin/env python3
"""Phrases of pinned definitions in generated claims (trust track T2c/T5, run 2026-11-04T2228Z).

`CLAIMS.md` is generated from the Lean statements by `scripts/trust/Claims.lean`; the only
hand-written words in it are the phrases of pinned definitions (`scripts/trust/phrases.txt`).
This script guards them:

  check_claims.py            lint: a phrase may use a glossary term (scripts/trust/glossary.txt)
                             only if the glossary attributes that term to the phrase's own
                             definition or to a pinned definition it rests on
                             (reads .lake/phrases.jsonl written by Claims.lean)
                             P1 (run 2026-11-08T1828Z): a phrase contains no formula (no operator or
                             relation character, no hyphen-minus except between letters): Claims.lean
                             prints each pinned definition's body from Lean right after its phrase, so
                             every formula in a generated claim is printed by Lean, never by the author
                             U1: no two pinned definitions share a phrase
                             U2 (run 2026-11-08T1828Z): the first glossary term of a phrase is attributed
                             by the glossary to the phrase's own definition
                             P2 (same run, after blind red team Y, not blind): every word and number of
                             a phrase occurs in its pinning specification's text (or that of a pinned
                             definition it rests on) or is a function word: a phrase quotes the blind spec
                             P3 (run 2026-11-08T2228Z, designed before blind round Z): the first occurrence of
                             every placeholder {x} is immediately preceded by the role of x written by a
                             blind role reader (scripts/trust/phrase_roles.txt, copied verbatim from the
                             reader's file under runs/); every placeholder has a registered role
                             P4 (same): every SIGN convention the reader registered for the definition occurs
                             word for word in its phrase
                             P6 (same run, after reading round Z: not blind): the definition's NAME, written
                             with its restricting qualifiers by a blind name reader (same registry), occurs
                             in its phrase word for word (Z d04 deleted "flat")
                             P5 (same run, after reading round Z: not blind): number, sign, order and
                             comparison words (one, two, first, positive, below, equals, exceeds, …) are not
                             function words for P2: they must be quoted from the specification, the roles
                             or the sign conventions
                             P7 (run 2026-11-09T0228Z, designed and stated in the clause reader's brief dd48d82
                             before blind red team AA ran): COVERAGE. Every token of a phrase (words, numbers, Greek
                             letters, subscripts, brackets and other marks) lies inside a blind text of its own
                             definition, read word for word: the NAME, a ROLE immediately followed by its argument
                             {x}, a SIGN convention, or a CLAUSE (third blind reader); a binder's symbol inside a blind
                             text is matched by that argument {x}; outside blind texts only the connectives of
                             P7_CONNECT and at most one template verb (P7_VERBS) may occur. A phrase is a sequence of blind texts, nothing the author wrote in between
                             can state a relation, a number, a direction or a domain
                             (after adversary AB, not blind: connectives restricted to the a an and with , ; ( ),
                             since "at"/"for"/"from … to" between role texts carried relations; marks are tokens,
                             since parentheses regrouped a clause; the verb must touch the NAME)
                             P9 (same run, after adversary AB: not blind): every CLAUSE line in the registry occurs in
                             its phrase (omitting a clause made the rest false); reader lines not shown are listed in
                             the shrink-only phrase_clause_baseline.txt and may not be in the registry
                             P8 (same run, after blind red team AA d03/d04: not blind): the registry cannot lose a
                             line: every NAME and SIGN line of each reader file it cites is in the registry while its
                             definition has a phrase (lint), and no `# source:` line and no registry line is removed
                             since the base commit unless its definition's phrase was removed (--base)
                             P10 (run 2026-11-09T1428Z, stated in the shape reader's brief d48a572 before blind
                             red team AC ran): the subject, verb and article of every property's phrase come from a
                             blind SHAPE reader (registry SHAPE lines); a quantity gets no verb
                             P11 (same, stated before AC): every phrase is exactly the fixed template's output from the
                             blind registry (`generate`; rewrite with `check_claims.py --generate`): no word,
                             connective, order or mark is the author's. After AC, not blind: P11a no control or
                             invisible character in the phrase file or registry, and the file reads the same split on
                             "\n" (as Claims.lean reads it) and on every line end (AC d01); P11b the registry keeps each
                             reader file's line order, and "divided by" joins only consecutive reader lines (AC d03)
                             P12 (--base, after AC d02, not blind): a reader line excluded at the base commit
                             (phrase_clause_baseline.txt) never enters the registry: an exclusion is final
  check_claims.py --generate rewrite every phrase of phrases.txt from the registry (P11)
  check_claims.py --base B   a phrase changed or removed since commit B needs a LEDGER.md line
                             added since B naming the definition (as check_relock.py does for
                             frozen fingerprints)

Why: a wrong phrase would put false meaning into every generated claim that uses the definition
(e.g. calling `angDist` a luminosity distance), exactly the class the generated claims remove.
"""
import json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PHR = "scripts/trust/phrases.txt"


def git(*args):
    return subprocess.run(["git", *args], capture_output=True, text=True, cwd=ROOT)


def parse_phrases(text):
    out = {}
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("#") or " | " not in s:
            continue
        d, p = s.split(" | ", 1)
        out[d.strip()] = p.strip()
    return out


def glossary():
    rules = []
    for line in (ROOT / "scripts/trust/glossary.txt").read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#") or "=>" not in line:
            continue
        rx, names = line.rsplit("=>", 1)
        rules.append((re.compile(rx.strip()), set(names.split())))
    return rules


def duplicate_phrases(phr):
    """U1 (blind red team W, run 2026-11-08T1428Z, d04): two different pinned definitions may not carry the same
    phrase (placeholders and case ignored): `expansionRate := |hubble|` was registered with the phrase of `hubble`,
    so every generated claim using it said "the Hubble rate a′(t)/a(t)" of a different function."""
    seen, bad = {}, []
    for d, p in sorted(phr.items()):
        key = re.sub(r"\{[^}]*\}", "{}", p).lower().strip()
        if key in seen:
            bad.append(f"{d}: phrase identical to that of {seen[key]} (U1: a reader of the generated claims could not "
                       f"tell the two definitions apart)")
        else:
            seen[key] = d
    return bad


FORMULA_CHARS = set("=+/·*√′″^²³⁴⁵⁽⁾ⁿ<>≤≥−×")


def formula_in_phrase(phr):
    """P1 (run 2026-11-08T1828Z, after blind round W d04): a phrase is the only hand-written text inside a generated
    claim; a formula written in it (W d04: "the Hubble rate a′(t)/a(t)" on `|hubble|`) is an author transcription of the
    body that no check compares with Lean. Claims.lean now prints the body itself next to the phrase, so phrases carry
    no formula at all: no operator or relation character, no hyphen-minus except inside a word."""
    bad = []
    for d, p in sorted(phr.items()):
        q = re.sub(r"\{[^}]*\}", "x", p)
        chars = sorted({c for c in q if c in FORMULA_CHARS})
        hy = [m.start() for m in re.finditer("-", q)
              if not (m.start() > 0 and q[m.start() - 1].isalpha() and m.start() + 1 < len(q) and q[m.start() + 1].isalpha())]
        if chars or hy:
            what = ", ".join([f"'{c}'" for c in chars] + (["a hyphen-minus outside a word"] if hy else []))
            bad.append(f"{d}: phrase contains formula characters ({what}) (P1: formulas are printed by Lean from the "
                       f"definition's body, not written in the phrase)")
    return bad


def head_noun(entries, rules):
    """U2 (run 2026-11-08T1828Z, after blind round W d04): the first glossary term of a phrase names what the definition
    is; it must be attributed by the glossary to the definition itself. `expansionRate := |hubble|` with the phrase
    "the Hubble rate ..." used a term of a definition it rests on (allowed by the attribution lint) as its own name.
    `entries`: dicts with `name`, `short`, `phrase`."""
    bad = []
    for e in entries:
        first = None
        for rx, names in rules:
            m = rx.search(e["phrase"])
            if m and (first is None or m.start() < first[0].start()):
                first = (m, names)
        if first and e["short"] not in first[1]:
            bad.append(f"{e['name']}: the first glossary term '{first[0].group(0)}' is attributed to {sorted(first[1])}, "
                       f"not to {e['short']} (U2: a phrase names its own definition first)")
    return bad


sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_claim_vocab import FUNCTION, WORD, norm, forms  # noqa: E402

NUM = re.compile(r"\d+(?:\.\d+)?")


P2_BASE = "scripts/trust/phrase_vocab_baseline.txt"
P5_BASE = "scripts/trust/phrase_polar_baseline.txt"


def p5_baseline(text=None):
    """P5 grandfathered (definition, word) pairs (run 2026-11-08T2228Z): number, sign and comparison words the phrases
    carried when P5 was introduced that neither the specification nor the blind readings contain ("units in which
    the speed of light is one", "two B turn into B and C"). Shrink-only (`--base`), like the P2 baseline."""
    if text is None:
        try:
            text = (ROOT / P5_BASE).read_text(encoding="utf-8")
        except FileNotFoundError:
            return set()
    return p2_baseline(text)


def p2_baseline(text=None):
    """(definition short name, word or number) pairs grandfathered for P2 when it was introduced (run 2026-11-08T1828Z):
    words of the formula-free phrases that the thin docstrings of their specifications do not contain (argument roles
    such as "curvature constant", units, citations). Shrink-only (`--base`): a blind writer adding them to the spec's
    docstrings, or a rewording, removes a line; nothing may be added."""
    if text is None:
        try:
            text = (ROOT / P2_BASE).read_text(encoding="utf-8")
        except FileNotFoundError:
            return set()
    out = set()
    for l in text.splitlines():
        l = l.split("#")[0].strip()
        if l:
            d, w = l.split()
            out.add((d, w))
    return out


ROLES = "scripts/trust/phrase_roles.txt"
# P5 (run 2026-11-08T2228Z, after blind round Z d05/d06: not blind): words of check_claim_vocab.FUNCTION that state a
# number, a sign, an order or a comparison carry content ("κ is two", "its integral exceeds"): P2 no longer exempts them.
POLAR = set("""one two three four five six seven eight nine ten first second third fourth fifth sixth not no nor
below above positive negative nonnegative nonpositive nonzero zero lower upper equals equal more less larger smaller
greater exceeds exceed least most strictly both same other""".split())


def load_roles(text=None):
    roles, signs, _clauses, bad = load_registry(text)
    return roles, signs, bad


def load_registry(text=None):
    """The blind role registry (P3/P4/P6/P7). Lines `ROLE | <full Lean name> | <binder> | <role>` and
    `SIGN | <full Lean name> | <convention>`, copied verbatim from a blind role reader's file named by a
    `# source: runs/<run>/roles/<file>` comment above them. Returns (roles, signs, problems)."""
    if text is None:
        try:
            text = (ROOT / ROLES).read_text(encoding="utf-8")
        except FileNotFoundError:
            return {}, {}, {}, [f"{ROLES} missing (P3)"]
    roles, signs, clauses, bad = {}, {}, {}, []
    src, src_lines = None, set()
    for raw in text.splitlines():
        l = raw.strip()
        m = re.match(r"#\s*source:\s*(\S+)", l)
        if m:
            src = m.group(1)
            f = ROOT / src
            if not (src.startswith("runs/") and f.is_file() and (f.parent / "BRIEF.md").is_file()) or f.name == "BRIEF.md":
                # (run 2026-11-09T0228Z, red team AA's untried route note: a brief cannot be its own reading)
                bad.append(f"{ROLES}: source {src} is not a reader file under runs/ next to its BRIEF.md (P3)")
                src_lines = set()
            else:
                src_lines = {x.strip() for x in f.read_text(encoding="utf-8").splitlines()}
            continue
        if not l or l.startswith("#"):
            continue
        if src is None or l not in src_lines:
            bad.append(f"{ROLES}: line not found verbatim in its reader file {src}: {l} (P3: roles are blind readings)")
            continue
        parts = [x.strip() for x in l.split(" | ")]
        if parts[0] == "ROLE" and len(parts) == 4:
            roles.setdefault(parts[1], {})[parts[2]] = parts[3]
        elif parts[0] in ("SIGN", "NAME") and len(parts) == 3:
            # NAME lines (P6) are kept with the sign conventions: both must occur in the phrase word for word
            signs.setdefault(parts[1], []).append(parts[2])
        elif parts[0] == "CLAUSE" and len(parts) == 3:
            # CLAUSE lines (P7) may be used by a phrase, word for word; they are not required
            clauses.setdefault(parts[1], []).append(parts[2])
        elif parts[0] == "SHAPE" and (parts[2:] == ["quantity"] or (len(parts) == 6 and parts[2] == "property")):
            pass  # P10 (run 2026-11-09T1428Z): read by registry_shapes
        else:
            bad.append(f"{ROLES}: malformed line: {l}")
    return roles, signs, clauses, bad


def _full(d, table):
    """The registry key (full Lean name) whose dotted suffix is the phrases.txt key `d`."""
    hits = [k for k in table if k == d or k.endswith("." + d)]
    return hits[0] if len(hits) == 1 else None


def _seq(text):
    return [norm(w) for w in WORD.findall(text)]


def role_binding(phr, roles, signs):
    """P3, P4 (run 2026-11-08T2228Z; designed and committed in the reader brief 5dfc17e before blind round Z ran).
    Rounds X and Y left one class open: a phrase built from words its spec contains can put them in the wrong place
    (X d01: observation and emission time swapped; Y d02: "minus" deleted). A blind role reader, given only the
    specification, the pin theorem and the definition's Lean body, wrote the role of every binder and the sign
    conventions (`phrase_roles.txt`). P3: the first occurrence of each placeholder {x} is immediately preceded by the
    words of x's role (a role swap or a missing role fails); P4: each registered sign convention occurs in the phrase
    word for word (deleting or changing a sign word fails)."""
    bad = []
    for d, p in sorted(phr.items()):
        key = _full(d, roles) or _full(d, signs)
        rmap = roles.get(key, {}) if key else {}
        seen = set()
        for m in re.finditer(r"\{([^}]*)\}", p):
            x = m.group(1)
            if x in seen:
                continue
            seen.add(x)
            if x not in rmap:
                bad.append(f"{d}: placeholder {{{x}}} has no role in {ROLES} (P3: every argument's role is read blind)")
                continue
            want = _seq(rmap[x])
            # words since the previous placeholder: a role cannot be read across another argument
            before = _seq(re.split(r"\{[^}]*\}", p[:m.start()])[-1])
            if not want or before[-len(want):] != want:
                bad.append(f"{d}: placeholder {{{x}}} is not immediately preceded by its blind role '{rmap[x]}' "
                           f"(P3: roles are bound slot by slot)")
        ps = " ".join(_seq(re.sub(r"\{[^}]*\}", " ", p)))
        for c in (signs.get(key, []) if key else []):
            if " " + " ".join(_seq(c)) + " " not in " " + ps + " ":
                bad.append(f"{d}: blind sign convention or name '{c}' does not occur word for word in the phrase (P4/P6)")
    return bad


# P7 (run 2026-11-09T0228Z): coverage of a phrase by blind texts.
# Connectives carry no relation (after adversary AB d01/d02: "at"/"for" and "from … to" between role texts stated which
# time is evaluated and the direction of an integral): only articles, "and", "with", and as marks , ; ( ).
P7_CONNECT = set("the a an and with , ; ( )".split())
P7_VERBS = set("is are obeys holds satisfies solves".split())
P7_PUNCT = set()  # marks are tokens (AB d04 regrouped a clause with parentheses): a blind text's own marks must match
CLAUSE_BASE = "scripts/trust/phrase_clause_baseline.txt"


def clause_baseline(text=None):
    """P9 (run 2026-11-09T0228Z, after adversary AB d03/d05: not blind): reader lines NOT used, shrink-only. Every other
    line of every reader file the registry cites is in the registry, and every CLAUSE line in the registry occurs in
    its definition's phrase word for word (as NAME and SIGN): the author no longer chooses which blind texts to show."""
    if text is None:
        try:
            text = (ROOT / CLAUSE_BASE).read_text(encoding="utf-8")
        except FileNotFoundError:
            return set()
    return {l.strip() for l in text.splitlines() if l.strip() and not l.startswith("#")}
_TOK = re.compile(r"\{[^}]*\}|[^\W_]+|\S")


def _ntok(t):
    import unicodedata
    return t if t.startswith("{") else unicodedata.normalize("NFKC", t).lower()


def p7_tokens(text, binders=()):
    """Tokens of a text: placeholders {x} kept whole; words, numbers and letters NFKC-normalised and lowercased (so a
    subscript is a digit or a letter, never invisible); every other non-space character is its own token. In a blind
    text, a token equal to a binder symbol x is a slot matched by {x} (or by the same literal token)."""
    out = []
    for t in _TOK.findall(text):
        if t in P7_PUNCT:
            continue
        out.append(("slot", t, _ntok(t)) if t in binders else ("tok", _ntok(t)))
    return out


def _match(blind, toks, i):
    for j, b in enumerate(blind):
        if i + j >= len(toks):
            return False
        t = toks[i + j]
        if b[0] == "slot":
            if t[0] == "tok" and t[1] in ("{" + b[1] + "}", b[2]):
                continue
            return False
        if t[0] != "tok" or t[1] != b[1]:
            return False
    return True


def registry_names(text=None):
    """NAME lines of the registry (P6), by full Lean name."""
    if text is None:
        text = (ROOT / ROLES).read_text(encoding="utf-8")
    out = {}
    for l in text.splitlines():
        parts = [x.strip() for x in l.strip().split(" | ")]
        if len(parts) == 3 and parts[0] == "NAME":
            out.setdefault(parts[1], []).append(parts[2])
    return out


def _verb_ok(toks, i, name_seqs):
    """A template verb must touch the definition's NAME: '<args> obeys the NAME', 'the NAME holds at …'."""
    art = {"the", "a", "an"}
    j = i + 1
    while j < len(toks) and toks[j][1] in art:
        j += 1
    k = i
    while k > 0 and toks[k - 1][1] in art:
        k -= 1
    for n in name_seqs:
        if toks[j:j + len(n)] == n or (k >= len(n) and toks[k - len(n):k] == n):
            return True
    return False


def coverage(phr, roles, signs, clauses, names=None):
    """P7 (designed before blind red team AA ran; stated in runs/2026-11-09T0228Z/clauses/BRIEF.md, dd48d82). Round Z
    d01 deleted "minus" from a relation sentence that no blind text covered; AA d01 swapped a Greek symbol, d02 and d05
    permuted words after the first placeholder, d06 changed interval brackets: all in author text between blind texts.
    A phrase is now a sequence of blind texts of its own definition joined by connectives."""
    bad = []
    for d, p in sorted(phr.items()):
        key = _full(d, roles) or _full(d, signs) or _full(d, clauses)
        if key is None:
            bad.append(f"{d}: no blind texts in {ROLES} (P7)")
            continue
        rmap = roles.get(key, {})
        binders = set(rmap)
        blind = [p7_tokens(r, ()) + [("tok", "{" + x + "}")] for x, r in rmap.items()]
        blind += [p7_tokens(c, binders) for c in signs.get(key, []) + clauses.get(key, [])]
        blind = [b for b in blind if b]
        toks = [("tok", t[1]) for t in p7_tokens(p, ())]
        for c in signs.get(key, []) + clauses.get(key, []):
            ct = p7_tokens(c, binders)
            if not any(_match(ct, toks, i) for i in range(len(toks))):
                bad.append(f"{d}: blind text '{c}' does not occur in the phrase word for word, marks and numbers included "
                           f"(P4/P6/P9: NAME, SIGN and CLAUSE lines are all required)")
        name_seqs = [[("tok", t[1]) for t in p7_tokens(n, ())] for n in (names or {}).get(key, [])]
        # longest-first greedy cover; on failure report the first uncovered stretch
        i, verbs, gaps = 0, 0, []
        reach = [False] * (len(toks) + 1)
        reach[0] = True
        how = [None] * (len(toks) + 1)
        for i in range(len(toks)):
            if not reach[i]:
                continue
            for b in blind:
                if _match(b, toks, i) and not reach[i + len(b)]:
                    reach[i + len(b)], how[i + len(b)] = True, ("blind", i)
            w = toks[i][1]
            if (w in P7_CONNECT or (w in P7_VERBS and (names is None or _verb_ok(toks, i, name_seqs)))) and not reach[i + 1]:
                reach[i + 1], how[i + 1] = True, ("conn", i)
        if not reach[len(toks)]:
            last = max(k for k in range(len(toks) + 1) if reach[k])
            gaps = " ".join(t[1] for t in toks[last:last + 8])
            bad.append(f"{d}: words not inside a blind text (NAME, ROLE before its argument, SIGN, CLAUSE) and not "
                       f"connectives, from: '{gaps}' (P7: a phrase is a sequence of blind texts)")
            continue
        k = len(toks)
        while k > 0:
            kind, j = how[k]
            if kind == "conn" and toks[j][1] in P7_VERBS:
                verbs += 1
            k = j
        if verbs > 1:
            bad.append(f"{d}: {verbs} template verbs outside blind texts (P7: at most one of {sorted(P7_VERBS)})")
    return bad


def registry_complete(phr, text=None, excl=None):
    """P8 (run 2026-11-09T0228Z, after blind red team AA d03/d04: not blind). AA deleted the NAME line of FriedmannEq and
    the SIGN line of curvK from the registry, which switched P6 and P4 off for them. Every NAME and SIGN line of a reader
    file the registry cites must be in the registry while its definition has a phrase."""
    if text is None:
        text = (ROOT / ROLES).read_text(encoding="utf-8")
    have = {l.strip() for l in text.splitlines()}
    excl = clause_baseline() if excl is None else excl
    keys = [k for k in phr]
    bad = []
    for l in sorted(have & excl):
        bad.append(f"{ROLES}: a line of the exclusion baseline {CLAUSE_BASE} is in the registry: {l} (P9: an excluded "
                   f"reader line cannot be shown)")
    for src in sorted(set(re.findall(r"#\s*source:\s*(\S+)", text))):
        f = ROOT / src
        if not f.is_file():
            continue
        for l in f.read_text(encoding="utf-8").splitlines():
            l = l.strip()
            parts = [x.strip() for x in l.split(" | ")]
            if len(parts) in (3, 4, 6) and parts[0] in ("NAME", "SIGN", "CLAUSE", "ROLE", "SHAPE") and l not in have \
                    and l not in excl:
                if any(parts[1] == k or parts[1].endswith("." + k) for k in keys):
                    bad.append(f"{ROLES}: blind line of {src} missing from the registry: {l} (P8: the registry cannot lose a line)")
    return bad


# P10/P11 (run 2026-11-09T1428Z; both stated in the blind shape reader's brief d48a572 before blind red team AC ran).
# After P7–P9 the author still chose, for a property, which arguments are the subject, the verb and the article
# (`PRED` of the run-0228Z generator, not CI-checked), and every connective and the order of blind texts was free within
# P7. P10: the shape of every phrase comes from a blind SHAPE reader (`SHAPE | <def> | quantity` or
# `SHAPE | <def> | property | <subject binders or none> | <verb> | <article>`). P11: CI regenerates every phrase from the
# registry with the fixed template below and fails unless the phrase file is exactly that output.
P11_VERBS = {"is", "are", "obeys", "satisfies", "solves", "holds"}
P11_ARTICLES = {"a", "the"}
# Characters Python's str.splitlines() treats as line ends besides "\n", and other invisible controls (red team AC d01:
# a U+000B in phrases.txt hid text from check_claims.py, whose parser used splitlines(), while Claims.lean, which splits
# on "\n" only, printed it into CLAIMS.md).
_BAD_CHARS = re.compile("[\x00-\x09\x0b-\x1f\x7f-\x9f  ​-‏‪-‮⁠-⁤﻿]")


def invisible_chars(path_texts):
    """P11a: no control, line-separator or invisible formatting character in the phrase file or the registry."""
    bad = []
    for path, text in path_texts:
        for n, l in enumerate(text.split("\n"), 1):
            m = _BAD_CHARS.search(l)
            if m:
                bad.append(f"{path}:{n}: character U+{ord(m.group(0)):04X} (P11: a phrase file line is what Claims.lean "
                           f"prints; no control or invisible characters)")
    return bad


def registry_entries(text=None):
    """Registry lines in order, with the reader file and the line's index in it: [(kind, key, parts, src, idx)]."""
    if text is None:
        text = (ROOT / ROLES).read_text(encoding="utf-8")
    out, src, src_lines = [], None, []
    for raw in text.split("\n"):
        l = raw.strip()
        m = re.match(r"#\s*source:\s*(\S+)", l)
        if m:
            src = m.group(1)
            f = ROOT / src
            src_lines = [x.strip() for x in f.read_text(encoding="utf-8").split("\n")] if f.is_file() else []
            continue
        if not l or l.startswith("#"):
            continue
        parts = [x.strip() for x in l.split(" | ")]
        idx = src_lines.index(l) if l in src_lines else -1
        out.append((parts[0], parts[1] if len(parts) > 1 else "", parts, src, idx))
    return out


def registry_order(text=None):
    """P11b (after blind red team AC d03, not blind): inside each `# source:` block the registry keeps the reader file's
    line order. AC d03 swapped two cosmoCoeff clauses in the registry; the generator then glued "divided by the n-th
    power of the Hubble rate" to "orders 0 and 1 coefficients are one". The order of blind texts is the reader's."""
    bad, last = [], {}
    for kind, key, parts, src, idx in registry_entries(text):
        if idx < 0:
            continue  # load_registry reports lines not in their reader file
        if idx < last.get(src, -1):
            bad.append(f"{ROLES}: line out of its reader file's order ({src}): {' | '.join(parts)} (P11: blind texts keep "
                       f"the reader's order)")
        last[src] = max(idx, last.get(src, -1))
    return bad


def registry_shapes(text=None):
    """P10: SHAPE lines by full Lean name -> ('quantity',) or ('property', [subject binders], verb, article)."""
    out = {}
    for kind, key, parts, src, idx in registry_entries(text):
        if kind != "SHAPE":
            continue
        if parts[2:] == ["quantity"]:
            out.setdefault(key, []).append(("quantity",))
        elif len(parts) == 6 and parts[2] == "property":
            subj = [] if parts[3] == "none" else parts[3].split()
            out.setdefault(key, []).append(("property", subj, parts[4], parts[5]))
    return out


def _slots(text, binders):
    """A binder symbol inside a blind text becomes its placeholder (two fixed exceptions: 'curv of a' is the only use of
    the binder a as a word, and 'F of R gravity' names the theory, not the binder F)."""
    for x in sorted(binders, key=len, reverse=True):
        if x == "a":
            text = re.sub(r"\bcurv of a$", "curv of {a}", text)
            continue
        pat = r"(?<![\w{])" + re.escape(x) + r"(?![\w}])"
        if x == "F":
            pat += r"(?! of R gravity)"
        text = re.sub(pat, "{" + x + "}", text)
    return text


def _listing(items):
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def generate(keys, text=None):
    """P11: the phrase of every definition in `keys` (phrases.txt keys), from the registry alone. Template:
    quantity: 'the NAME with the ROLE {x}, … and the ROLE {z} (SIGN; …; CLAUSE; …)';
    property: 'the ROLE {s}[, … and the ROLE {s'}] VERB ARTICLE NAME with the ROLE {x}, … (…)', or with subject none
    'the NAME holds with …'. Blind texts in registry order (= reader order, P11b), SIGN lines before CLAUSE lines; a
    blind text contained word for word in one already shown is not repeated; a CLAUSE starting 'divided by ' is joined
    to the previous text only if that is the line just above it in the same reader file (the reader split one quotient
    in two). Returns ({key: phrase}, problems)."""
    if text is None:
        text = (ROOT / ROLES).read_text(encoding="utf-8")
    roles, signs, clauses, _ = load_registry(text)
    names = registry_names(text)
    shapes = registry_shapes(text)
    ents = registry_entries(text)
    out, bad = {}, []
    for d in keys:
        key = _full(d, roles)
        if key is None:
            bad.append(f"{d}: no ROLE lines in {ROLES} (P11)")
            continue
        rmap = roles[key]
        if not names.get(key):
            bad.append(f"{d}: no NAME line (P11)")
            continue
        name = names[key][0]
        sh = shapes.get(key, [])
        if len(sh) != 1:
            bad.append(f"{d}: {len(sh)} SHAPE lines in {ROLES}, need exactly one from a blind shape reader (P10)")
            continue
        sh = sh[0]
        texts = [(e[2][2], e[3], e[4]) for e in ents if e[1] == key and e[0] == "SIGN" and e[2][2] != name]
        texts += [(e[2][2], e[3], e[4]) for e in ents if e[1] == key and e[0] == "CLAUSE"]
        par, prev = [], None
        for raw, src, idx in texts:
            x = _slots(raw, rmap)
            if any(f" {x} " in f" {y} " for y in par):
                prev = (src, idx)
                continue
            if par and x.startswith("divided by ") and prev == (src, idx - 1):
                par[-1] += " " + x
            else:
                par.append(x)
            prev = (src, idx)
        tail = f" ({'; '.join(par)})" if par else ""
        if sh[0] == "property":
            subj, verb, art = sh[1], sh[2], sh[3]
            if verb not in P11_VERBS or art not in P11_ARTICLES or any(b not in rmap for b in subj) or \
                    (verb == "holds") != (not subj) or (verb == "are") != (len(subj) > 1):
                bad.append(f"{d}: SHAPE line not usable: subject {subj}, verb {verb}, article {art} (P10)")
                continue
            rest = [b for b in rmap if b not in subj]
            s = _listing([f"the {rmap[b]} {{{b}}}" for b in subj]) + " " if subj else ""
            ph = f"{s}{verb} {art} {name}" if subj else f"the {name} {verb}"
            if rest:
                ph += " with " + _listing([f"the {rmap[b]} {{{b}}}" for b in rest])
        else:
            ph = f"the {name} with " + _listing([f"the {rmap[b]} {{{b}}}" for b in rmap])
        out[d] = ph + tail
    return out, bad


def phrase_lines(text):
    """phrases.txt as Claims.lean reads it: lines split on '\\n' only."""
    out = {}
    for line in text.split("\n"):
        s = line.strip()
        if not s or s.startswith("#") or " | " not in s:
            continue
        d, p = s.split(" | ", 1)
        out[d.strip()] = p.strip()
    return out


def generated(phr_text=None, reg_text=None):
    """P10/P11 lint: every phrase equals the template's output from the registry, byte for byte."""
    if phr_text is None:
        phr_text = (ROOT / PHR).read_text(encoding="utf-8")
    if reg_text is None:
        reg_text = (ROOT / ROLES).read_text(encoding="utf-8")
    bad = invisible_chars([(PHR, phr_text), (ROLES, reg_text)])
    bad += registry_order(reg_text)
    phr = phrase_lines(phr_text)
    if phr != parse_phrases(phr_text):
        bad.append(f"{PHR}: the file reads differently split on newlines and on all line ends (P11)")
    gen, gbad = generate(list(phr), reg_text)
    bad += gbad
    for d, p in phr.items():
        if d in gen and gen[d] != p:
            bad.append(f"{d}: phrase is not the template's output from the blind registry (P11); generated: {gen[d]}")
    return bad


def write_generated():
    """`check_claims.py --generate`: rewrite every phrase of phrases.txt from the registry (P11)."""
    text = (ROOT / PHR).read_text(encoding="utf-8")
    phr = phrase_lines(text)
    gen, bad = generate(list(phr))
    if bad:
        print("\n".join(bad))
        return 1
    out = []
    for line in text.split("\n"):
        s = line.strip()
        if s and not s.startswith("#") and " | " in s:
            d = s.split(" | ", 1)[0].strip()
            line = f"{d} | {gen[d]}"
        out.append(line)
    (ROOT / PHR).write_text("\n".join(out), encoding="utf-8")
    return 0


def baseline_reentry(base, old_excl_text=None, old_reg_text=None, new_reg_text=None):
    """P12 (--base; after blind red team AC d02, not blind): a reader line excluded at `base` (phrase_clause_baseline.txt:
    false at junk values, a hypothesis rather than a property, true only under extra hypotheses, ambiguous parse) cannot
    enter the registry later. AC d02 deleted 'equivalent to equal chemical potential in both phases' from the baseline,
    added it to the registry and showed it: an exclusion is a correctness judgment, not a display preference."""
    if old_excl_text is None or old_reg_text is None:
        ob = git("show", f"{base}:{CLAUSE_BASE}")
        orr = git("show", f"{base}:{ROLES}")
        if ob.returncode or orr.returncode:
            return []
        old_excl_text, old_reg_text = ob.stdout, orr.stdout
    if new_reg_text is None:
        new_reg_text = (ROOT / ROLES).read_text(encoding="utf-8")
    old_excl = clause_baseline(old_excl_text)
    old_reg = {l.strip() for l in old_reg_text.split("\n")}
    new_reg = {l.strip() for l in new_reg_text.split("\n")}
    return [f"{ROLES}: line excluded at {base} now in the registry: {l} (P12: exclusions are final)"
            for l in sorted((new_reg - old_reg) & old_excl)]


def spec_vocabulary(entries, base=frozenset(), roles=None, signs=None, clauses=None):
    """P2 (run 2026-11-08T1828Z, after blind red team Y: not blind): a phrase may use only words and numbers that occur
    in the text of its own pinning specification or in that of a pinned definition it rests on (docstrings and field
    names of the SPEC structure or blind formulation the pin theorem uses, exported by Claims.lean as `spec_text`; the
    specs were written by blind spec writers), plus the function words of check_claim_vocab.py. Y put "conformal"
    on `hubble`, "fitted value 0.3, as verified" on `IsFlatLCDM`, "no claim is made there" on `decel` and swapped
    equation numbers between `FriedmannEq` and `MasterEq`: words and numbers no check read. A quotation rule, not a
    deny-list (PROMPT working notes 145, 164)."""
    by_short = {e["short"]: e for e in entries}
    bad = []
    for e in entries:
        text = " ".join([e.get("spec_text", "")] + [by_short[r].get("spec_text", "") for r in e.get("rests_on", [])
                                                    if r in by_short])
        # P3/P4 texts are blind readings too: a phrase may quote the role and sign words of its own definition
        k = _full(e["name"], roles or {}) or _full(e["name"], signs or {})
        if k:
            text += " " + " ".join((roles or {}).get(k, {}).values()) + " " + " ".join((signs or {}).get(k, []))
        k = k or _full(e["name"], clauses or {})
        if k:
            text += " " + " ".join((clauses or {}).get(k, []))
        allowed = {norm(w) for w in WORD.findall(text)}
        nums = set(NUM.findall(text))
        ph = re.sub(r"\{[^}]*\}", " ", e["phrase"])
        extra = {w for (s, w) in base if s == e["short"]}
        miss = sorted({norm(w) for w in WORD.findall(ph)
                       if not (forms(norm(w)) & (allowed | (FUNCTION - POLAR) | extra))})
        miss += sorted({n for n in NUM.findall(ph) if n not in nums and n not in extra})
        if miss:
            bad.append(f"{e['name']}: phrase words not in its pinning specification's text or in a function word list: "
                       f"{miss} (P2: a phrase quotes the blind spec)")
    return bad


def _controls():
    ok = not duplicate_phrases({"A.f": "the rate of {a} at {t}", "A.g": "the size of {a}"})
    bad = duplicate_phrases({"A.f": "the rate of {a} at {t}", "A.g": "The rate of {b} at {s}"})
    if not ok or len(bad) != 1:
        print("::error::check_claims U1 controls failed")
        return 1
    ok = not formula_in_phrase({"A.f": "the angular-diameter distance of {a} at time {t₀} (Eq. (11.6))"})
    bad = formula_in_phrase({"A.f": "the rate a′({t})/a({t}) of {a}"})
    bad2 = formula_in_phrase({"A.f": "the rate of {a} minus -1"})
    if not ok or len(bad) != 1 or len(bad2) != 1:
        print("::error::check_claims P1 controls failed")
        return 1
    gl = [(re.compile(r"(?i)hubble (rate|parameter|function)"), {"hubble", "IsFlatLCDM"}),
          (re.compile(r"(?i)\bredshift"), {"redshift"})]
    ok = not head_noun([{"name": "A.hubble", "short": "hubble", "phrase": "the Hubble rate of {a}"},
                        {"name": "A.IsFlatLCDM", "short": "IsFlatLCDM", "phrase": "{a} obeys a law with a Hubble rate and a redshift"},
                        {"name": "A.g", "short": "g", "phrase": "the size of {a}"}], gl)
    bad = head_noun([{"name": "A.expansionRate", "short": "expansionRate", "phrase": "the Hubble rate of {a}"},
                     {"name": "A.h", "short": "hubble", "phrase": "the rate of {a} at the redshift of {t}, a Hubble rate"}], gl)
    if not ok or len(bad) != 2:
        print("::error::check_claims U2 controls failed")
        return 1
    sp = [{"name": "A.hubble", "short": "hubble", "rests_on": [], "spec_text": "Specification of the Hubble rate of a scale factor at time t, Eq. (11.6)",
           "phrase": "the Hubble rate of the scale factor {a} at time {t} (Eq. (11.6))"}]
    ok = not spec_vocabulary(sp)
    bad = spec_vocabulary([dict(sp[0], phrase="the conformal Hubble rate of the scale factor {a} at time {t} (Eq. (11.5))")])
    if not ok or len(bad) != 1 or "conformal" not in bad[0] or "11.5" not in bad[0]:
        print("::error::check_claims P2 controls failed")
        return 1
    rl = {"A.f": {"a": "scale factor", "t₀": "observation time", "t": "emission time"}}
    sg = {"A.f": ["minus the curvature density parameter"]}
    ok = not role_binding({"f": "the distance at the observation time {t₀} of a source at the emission time {t} "
                                "(scale factor {a}; it is minus the curvature density parameter)"}, rl, sg)
    bad = role_binding({"f": "the distance at the observation time {t} of a source at the emission time {t₀} "
                             "(scale factor {a}; it is minus the curvature density parameter)"}, rl, sg)
    bad2 = role_binding({"f": "the distance at the observation time {t₀} of a source at the emission time {t} "
                              "(scale factor {a}; it is the curvature density parameter)"}, rl, sg)
    bad3 = role_binding({"f": "the distance at the observation time {t₀} of a source at {t} (scale factor {a}; it "
                              "is minus the curvature density parameter)"}, rl, sg)
    if not ok or len(bad) != 2 or len(bad2) != 1 or len(bad3) != 1:
        print("::error::check_claims P3/P4 controls failed")
        return 1
    rl7 = {"A.f": {"a": "scale factor", "t₀": "observation time", "t": "emission time"}}
    cl7 = {"A.f": ["order 2 coefficient is minus the deceleration parameter", "holds on a neighbourhood of t₀",
                   "minus six times second derivative over scale factor plus squared Hubble rate"]}
    nm7 = {"A.f": ["cosmographic coefficient"]}
    nmd = {"A.f": ["cosmographic coefficient"]}
    good7 = {"f": "the cosmographic coefficient with the scale factor {a}, the observation time {t₀} and the emission "
                  "time {t} (order 2 coefficient is minus the deceleration parameter; holds on a neighbourhood of {t₀}; "
                  "minus six times second derivative over scale factor plus squared Hubble rate)"}
    if coverage(good7, rl7, nm7, cl7, nmd):
        print("::error::check_claims P7 controls failed (good phrase rejected)", coverage(good7, rl7, nm7, cl7, nmd))
        return 1
    g = good7["f"]
    for mut in (g.replace("is minus the", "is the"),                     # Z d01: relation word deleted
                g.replace("of {t₀};", "of {t};"),                        # slot filled by the wrong argument
                g.replace("(order", "(Ωₘ is one; order"),                # AA d01: Greek/number outside blind text
                g.replace("{t₀} and the", "{t₀}, is not the"),           # a verb and a negation between blind texts
                g.replace("of {t₀};", "of [0, {t₀}];"),                  # AA d06: brackets
                g.replace("with the scale factor {a}, the observation", "of the scale factor {a} at the observation"),  # AB d01
                g.replace("over scale factor plus squared", "over (scale factor plus squared") + ")",                 # AB d04
                g.replace("; holds on a neighbourhood of {t₀}", ""),     # AB d03: a required clause omitted
                g.replace("emission time {t} (", "emission time {t} is (")):  # verb not touching the NAME
        if not coverage({"f": mut}, rl7, nm7, cl7, nmd):
            print("::error::check_claims P7/P9 controls failed (mutant accepted):", mut)
            return 1
    reg_old = "# source: runs/x/r.txt\nNAME | A.f | flat law\nSIGN | A.f | minus one\nROLE | A.f | a | scale factor\n"
    if registry_removals("B", reg_old, reg_old, {"f": "x"}) or len(registry_removals(
            "B", reg_old, reg_old.replace("SIGN | A.f | minus one\n", ""), {"f": "x"})) != 1 or len(registry_removals(
            "B", reg_old, reg_old.replace("# source: runs/x/r.txt\n", ""), {"f": "x"})) != 1 or registry_removals(
            "B", reg_old, "", {}) != ["scripts/trust/phrase_roles.txt: source line removed since B: # source: runs/x/r.txt (P8)"]:
        print("::error::check_claims P8 controls failed")
        return 1
    if _controls_p10_p12():
        return 1
    sp5 = [dict(sp[0], spec_text="Specification of the Hubble rate of a scale factor at time t; units in which c is one",
                phrase="the Hubble rate of the scale factor {a} at time {t} (units in which c is one)")]
    if spec_vocabulary(sp5) or len(spec_vocabulary([dict(sp5[0], phrase=sp5[0]["phrase"].replace("is one", "is two"))])) != 1:
        print("::error::check_claims P5 controls failed")
        return 1
    return 0


def _controls_p10_p12():
    """Controls for P10, P11, P11a, P11b, P12 on a synthetic registry whose reader file is this repository's real
    second shape reading and clause reading (the generator needs line positions in reader files)."""
    cl = "runs/2026-11-09T0228Z/clauses/CLAUSES.txt"
    sh = "runs/2026-11-09T1428Z/shapes2/SHAPES.txt"
    nm = "runs/2026-11-08T2228Z/names/NAMES.txt"
    ro = "runs/2026-11-08T2228Z/roles/ROLES.txt"
    if not all((ROOT / f).is_file() for f in (cl, sh, nm, ro)):
        return 0  # a scratch tree without the readings (judges): controls run in the repository
    c = "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | "
    reg = (f"# source: {ro}\nROLE | Checked.Cosmography.Aviles.cosmoCoeff | n | derivative order of the coefficient\n"
           f"ROLE | Checked.Cosmography.Aviles.cosmoCoeff | a | scale factor\n"
           f"ROLE | Checked.Cosmography.Aviles.cosmoCoeff | t | time of evaluation\n"
           f"ROLE | Checked.Sim.Duffing.IsDuffingSolution | x | position as function of time\n"
           f"# source: {nm}\nNAME | Checked.Cosmography.Aviles.cosmoCoeff | cosmographic coefficient\n"
           f"NAME | Checked.Sim.Duffing.IsDuffingSolution | Duffing oscillator initial value problem solution\n"
           f"# source: {cl}\n{c}n-th time derivative of the scale factor over the scale factor\n"
           f"{c}divided by the n-th power of the Hubble rate\n{c}orders 0 and 1 coefficients are one\n"
           f"# source: {sh}\nSHAPE | Checked.Cosmography.Aviles.cosmoCoeff | quantity\n"
           f"SHAPE | Checked.Sim.Duffing.IsDuffingSolution | property | x | is | a\n")
    good = ("Aviles.cosmoCoeff | the cosmographic coefficient with the derivative order of the coefficient {n}, the scale "
            "factor {a} and the time of evaluation {t} ({n}-th time derivative of the scale factor over the scale factor "
            "divided by the {n}-th power of the Hubble rate; orders 0 and 1 coefficients are one)\n"
            "Duffing.IsDuffingSolution | the position as function of time {x} is a Duffing oscillator initial value "
            "problem solution\n")
    if generated(good, reg):
        print("::error::check_claims P10/P11 controls failed (generated phrase rejected)", generated(good, reg))
        return 1
    swapped = reg.replace(f"{c}divided by the n-th power of the Hubble rate\n{c}orders 0 and 1 coefficients are one\n",
                          f"{c}orders 0 and 1 coefficients are one\n{c}divided by the n-th power of the Hubble rate\n")
    muts = [(good.replace("is a Duffing", "is the Duffing"), reg),                       # AC d05: article
            (good.replace("coefficient with the derivative", "coefficient for the derivative"), reg),  # a connective
            (good.replace("are one)", "are one)\x0b (orders 0 and 1 are two)"), reg),    # AC d01: hidden line end
            (good, reg.replace("| x | is | a", "| x | is | the")),                       # P10: shape line changed
            (good, reg.replace("SHAPE | Checked.Sim.Duffing.IsDuffingSolution | property | x | is | a\n", "")),  # P10
            (good, swapped)]                                                             # AC d03: order
    for ph, rg in muts:
        if not generated(ph, rg):
            print("::error::check_claims P10/P11 controls failed (mutant accepted):", ph[-80:], rg[-80:])
            return 1
    line = "CLAUSE | Checked.Chemistry.Coexistence.IsMaxwellCoexistence | equivalent to equal chemical potential in both phases"
    if baseline_reentry("B", line + "\n", "", "") or len(baseline_reentry("B", line + "\n", "", line + "\n")) != 1:
        print("::error::check_claims P12 controls failed")
        return 1
    return 0


def lint():
    if _controls():
        return 1
    data = ROOT / ".lake/phrases.jsonl"
    if not data.exists():
        print(".lake/phrases.jsonl missing: run `lake env lean scripts/trust/Claims.lean` first")
        return 1
    rules = glossary()
    bad = []
    n = 0
    entries = []
    for line in data.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        e = json.loads(line)
        entries.append(e)
        n += 1
        allowed = {e["short"], *e["rests_on"]}
        for rx, names in rules:
            m = rx.search(e["phrase"])
            if m and not (names & allowed):
                bad.append(f"{e['name']}: phrase uses '{m.group(0)}' (glossary: {sorted(names)}), "
                           f"but the definition is {e['short']} and rests on {sorted(e['rests_on'])}")
    phr = parse_phrases((ROOT / PHR).read_text(encoding="utf-8"))
    bad += duplicate_phrases(phr)
    bad += formula_in_phrase(phr)
    bad += head_noun(entries, rules)
    roles, signs, clauses, rbad = load_registry()
    bad += rbad
    bad += role_binding(phr, roles, signs)
    bad += coverage(phr, roles, signs, clauses, registry_names())
    bad += registry_complete(phr)
    bad += generated()
    bad += spec_vocabulary(entries, p2_baseline() | p5_baseline(), roles, signs, clauses)
    for b in bad:
        print("PHRASE:", b)
    print(f"phrases: {n} checked, {len(bad)} problems")
    return 1 if bad else 0


def _first(base, path):
    out = git("log", "--format=%H", "--reverse", "--diff-filter=A", f"{base}..HEAD", "--", path).stdout.split()
    return out[0] if out else None


def _before(a, b):
    """commit a is a strict ancestor of commit b"""
    return a != b and git("merge-base", "--is-ancestor", a, b).returncode == 0


def roles_route(base):
    """P3 route (run 2026-11-08T2228Z): role registry lines added since `base` come from a reader file under
    runs/<run>/roles/ whose BRIEF.md was committed alone strictly before the reader file, which was committed
    (touching only runs/<run>/) strictly before the first commit since `base` that changes the registry:
    brief, reading, copy (as check_blind_route.py B1/B4 for literal readings)."""
    old = git("show", f"{base}:{ROLES}")
    old_lines = set(old.stdout.splitlines()) if old.returncode == 0 else set()
    new_text = (ROOT / ROLES).read_text(encoding="utf-8") if (ROOT / ROLES).exists() else ""
    added = [l for l in new_text.splitlines() if l.strip() and not l.startswith("#") and l not in old_lines]
    if not added:
        return []
    srcs = sorted(set(re.findall(r"#\s*source:\s*(\S+)", new_text)))
    copy = git("log", "--format=%H", "--reverse", f"{base}..HEAD", "--", ROLES).stdout.split()
    bad = []
    for src in srcs:
        brief = str(Path(src).parent / "BRIEF.md")
        rc, bc = _first(base, src), _first(base, brief)
        if rc is None:
            continue  # reader file older than base: checked when it was added
        if bc is None or not _before(bc, rc):
            bad.append(f"{src}: its BRIEF.md is not committed strictly before the reading (P3 route)")
        files = git("show", "--name-only", "--format=", rc).stdout.split()
        run_dir = "/".join(src.split("/")[:2]) + "/"
        if any(not f.startswith(run_dir) for f in files):
            bad.append(f"{src}: the commit adding the reading changes files outside {run_dir} (P3 route)")
        if bc and any(f.startswith(("scripts/", "Checked/", "Work/")) for f in git("show", "--name-only", "--format=", bc).stdout.split()):
            bad.append(f"{brief}: the commit adding the brief changes scripts/, Checked/ or Work/ (P3 route)")
        if copy and not _before(rc, copy[0]):
            bad.append(f"{src}: the registry {ROLES} was changed before or with the reading (P3 route: brief, reading, copy)")
    return bad


def registry_removals(base, old_text=None, new_text=None, new_phr=None):
    """P8 (--base part): no `# source:` line and no registry line is removed since `base`, unless the definition the
    line is about no longer has a phrase (the definition left the pinned set; its phrase removal needs a LEDGER line)."""
    if old_text is None:
        o = git("show", f"{base}:{ROLES}")
        if o.returncode:
            return []
        old_text = o.stdout
    if new_text is None:
        new_text = (ROOT / ROLES).read_text(encoding="utf-8") if (ROOT / ROLES).exists() else ""
    if new_phr is None:
        new_phr = parse_phrases((ROOT / PHR).read_text(encoding="utf-8"))
    have = {l.strip() for l in new_text.splitlines()}
    bad = []
    for l in old_text.splitlines():
        l = l.strip()
        if not l or l in have:
            continue
        if re.match(r"#\s*source:", l):
            bad.append(f"{ROLES}: source line removed since {base}: {l} (P8)")
            continue
        if l.startswith("#"):
            continue
        parts = [x.strip() for x in l.split(" | ")]
        if len(parts) >= 3 and any(parts[1] == k or parts[1].endswith("." + k) for k in new_phr):
            bad.append(f"{ROLES}: blind line removed since {base} while {parts[1]} still has a phrase: {l} (P8)")
    return bad


def base_check(base):
    if not base or set(base) == {"0"} or git("cat-file", "-e", base + "^{commit}").returncode:
        base = "HEAD~1"
    rb = roles_route(base) + baseline_reentry(base)
    for b in rb:
        print("PHRASE ROLES:", b)
    if rb:
        return 1
    ocb = git("show", f"{base}:{CLAUSE_BASE}")
    if ocb.returncode == 0:
        grown = sorted(clause_baseline() - clause_baseline(ocb.stdout))
        for l in grown:
            print(f"P9 clause baseline line added since {base}: {l} (shrink-only)")
        if grown:
            return 1
    rr = registry_removals(base)
    for b in rr:
        print("PHRASE ROLES:", b)
    if rr:
        return 1
    old = git("show", f"{base}:{PHR}")
    if old.returncode:
        print(f"no {PHR} at {base}: nothing to compare")
        return 0
    ob = git("show", f"{base}:{P2_BASE}")
    if ob.returncode == 0:
        added = sorted(p2_baseline() - p2_baseline(ob.stdout))
        if added:
            for d, w in added:
                print(f"P2 baseline line added since {base}: {d} {w} (shrink-only)")
            return 1
    o5 = git("show", f"{base}:{P5_BASE}")
    if o5.returncode == 0:
        added = sorted(p5_baseline() - p5_baseline(o5.stdout))
        if added:
            for d, w in added:
                print(f"P5 baseline line added since {base}: {d} {w} (shrink-only)")
            return 1
    old = parse_phrases(old.stdout)
    new = parse_phrases((ROOT / PHR).read_text(encoding="utf-8"))
    changed = sorted(d for d, p in old.items() if new.get(d) != p)
    if not changed:
        print(f"phrases: {len(old)} at {base}, none changed or removed")
        return 0
    diff = git("diff", base, "HEAD", "--", "LEDGER.md").stdout
    added = "\n".join(l[1:] for l in diff.splitlines() if l.startswith("+") and not l.startswith("+++"))
    missing = []
    for d in changed:
        last = re.escape(d.split(".")[-1])
        if not (d in added or re.search(r"(?<![\w'])" + last + r"(?![\w'])", added)):
            missing.append(d)
        print(("removed" if d not in new else "changed") + f" phrase: {d}" +
              ("  -- NOT named in a LEDGER.md addition" if d in missing else ""))
    return 1 if missing else 0


if __name__ == "__main__":
    if "--generate" in sys.argv:
        sys.exit(write_generated())
    if "--base" in sys.argv:
        i = sys.argv.index("--base")
        sys.exit(base_check(sys.argv[i + 1] if i + 1 < len(sys.argv) else ""))
    sys.exit(lint())
