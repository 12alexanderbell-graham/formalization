#!/usr/bin/env python3
"""A hand-written 'open' necessity line left standing after the hypothesis was classified (run 2026-11-20T2028Z,
part 3; LEDGER experiment of run 2026-11-20T1428Z).

Why: reader test WP of run 2026-11-20T1428Z (`runs/2026-11-20T1428Z/t5/GRADE_WP.md`): 5 of 6 blind readers given
STATE.md beside CLAIMS_READER.md met a hand-written line calling a numbered hypothesis of a listed headline open
(STATE.md: hypothesis 2 of `redshiftCore_pins`; hypothesis 8 of the beta = -0.13 row) that `TRUST_MAP.md` (generated)
had classified since. They rejected it by the banner, but each such line teaches a reader that STATE.md's words are
stale, and nobody's job was to come back to them (the same pattern as the pending status headings that
`check_stale_status.py` closed in run 2026-11-18T2028Z).

Rule S-N1: in STATE.md, README.md and BLUEPRINT.md (the files of `check_headline_mentions.py`; run records are dated
and not read), inside an OPEN SCOPE, a numbered hypothesis of a headline that `TRUST_MAP.md` classifies
(NEEDED or REDUNDANT, section 'Hypothesis necessity, per headline') is STALE. A hypothesis is read as
  (a) a backticked headline name followed by a number list (`fs_neg_tenth_monotone_lt` 7; `x` 13/16; `x` 4, 5 and 8;
      optionally with 'hypothesis'/'hypotheses' between), or
  (b) 'hypothesis/hypotheses <number list> of' followed, in the same clause, by backticked headline names (each one
      is meant), e.g. 'hypothesis 1 of the six two-sided companions (`CCS.printedD4_fails`, ...)'.
Rule S-N2: 'the <N> open hypotheses of `x`' is STALE when TRUST_MAP lists fewer than N open hypotheses of `x`.
An OPEN SCOPE is the clause (text between ';' or '. ' boundaries) that contains an open word (open, unclassified,
not yet classified, still open), or, after a scope label ending in ':' ('Not yet:', 'Open in this family:', 'Open:'),
the rest of the line. A headline name is a backticked full name, a unique suffix of one ('B1.cubic_misses_z3'), or
its last component when that is unique among the headlines with a necessity entry.
Lines of the reading guide (the banner) and lines that cite their own classification are not exempt: rewrite a stale
line, e.g. drop the item or write 'classified since (TRUST_MAP.md)' without the number.

Rules S-N4, S-N5 (run 2026-11-21T0228Z; see their block below): the default inverted. Every hypothesis number a line
attaches to a headline is flagged when TRUST_MAP classifies it, unless the line states that same classification;
ordinal descriptions ('the last hypothesis of `x`') are read as numbers. Blind held-out recall of the word rules:
6/16 (test SN), 8/17 (SN2); of S-N4 as frozen before its test: 15/16 (SN3), false positives 0/10 in each test.

Limits: a hypothesis described by its content without its number ('the wall condition of `x`') is not
read; bundled hypotheses count as classified when TRUST_MAP lists them NEEDED or REDUNDANT as a bundle (the page a
reader checks shows them so).

Run by `check_necessity_prose.py` (CI trust step, after TRUST_MAP.md is regenerated; also by records_check.py).
Cost when it was introduced: 8 lines (7 of STATE.md, 1 of BLUEPRINT.md, 14 items), rewritten in run 2026-11-20T2028Z;
each rewrite of an old line is a new line for `check_headline_mentions.py`, so write the replacement in its vocabulary
(the template '- **Hypotheses:** each hypothesis of each headline of this section is listed in `TRUST_MAP.md` (per
headline).' passes).

Usage: check_stale_necessity.py [--measure FILE ...]   (default: the three files; exit 1 on a stale line)
       check_stale_necessity.py --selftest
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TRUST = ROOT / "TRUST_MAP.md"
FILES = ("STATE.md", "README.md", "BLUEPRINT.md")
NUM = r"\d+(?:\s*(?:/|,\s*and|,|and|&|–)\s*\d+)*"
# open words and scope labels widened after the held-out writer test SN (run 2026-11-20T2028Z: recall 6/16 before)
OPEN_WORD = re.compile(r"\b(?:open(?!\s+baseline)|unclassified|unresolved|undone|not yet|still to be shown|remaining|classify|settle|"
                       r"decide whether)\b", re.IGNORECASE)
LABEL = re.compile(r"(?:\bNot yet\b|\bNext\b|\bPart \d+[^:;.]{0,10}|\bRemaining\b[^:;.]{0,40}|\bStill to be shown\b|"
                   r"\bTo do\b|\bOpen\b[^:;.]{0,40}|\bopen\b[^:;.]{0,40}):", re.IGNORECASE)
# hypothesis lists of a clause that carry no headline name of their own (S-N1d)
END = r"(?!\s*(?:/|,|and|&|–)\s*\d)(?!\.\d)"  # the whole list
PE = [re.compile(r"\bhypothes(?:is|es)\s+(" + NUM + r")" + END, re.IGNORECASE),
      re.compile(r"\b(?:classify|settle|drop(?:ping)?|remov(?:e|ing)|test(?:ing)?)\s+(?:hypothes(?:is|es)\s+)?(" + NUM +
                 r")(?!\.\d)", re.IGNORECASE),
      re.compile(r"(?<![\d.\w−-])(" + NUM + r")\s*(?:[-–—]\s*)?(?:(?:is|are|remains?)\s+)?(?:all\s+|also\s+|still\s+)?"
                 r"(?:open|unresolved|undone|unclassified)\b", re.IGNORECASE),
      re.compile(r"\b(?:open|unresolved|undone)\s*:?\s+(" + NUM + r")(?!\s*(?:→|->|\d|\.\d))", re.IGNORECASE),
      re.compile(r"\bthat\s+(" + NUM + r")\s+(?:is|are)\s+(?:redundant|needed)\b", re.IGNORECASE)]
PA = re.compile(r"`([A-Za-z_][\w.']*)`\s*(?:[:–—-]\s*)?(?:hypothes(?:is|es)\s+)?(" + NUM + r")(?![\w.]*\d*\s*%)(?!\.\d)")
PB = re.compile(r"\bhypothes(?:is|es)\s+(" + NUM + r")\s+of\b([^;]*)", re.IGNORECASE)
PC = re.compile(r"\bthe\s+(\d+)\s+open\s+hypotheses\s+of\s+`([A-Za-z_][\w.']*)`", re.IGNORECASE)
PD = re.compile(r"\bopen\s+(" + NUM + r")(?!\s*(?:→|->|\d|\.\d))|(?<![\d.])(" + NUM + r")\s+(?:(?:is|are|remains?|still)\s+)?open\b")
CLASSIFIED_AFTER = re.compile(r"\s*(?:\([^)]*\)\s*)?(?:(?:is|are|both|each|now|shown|also)\s+)*(?:NEEDED|REDUNDANT|needed|"
                              r"redundant)\b")  # 'x 1 NEEDED' states a classification, not an open item
CLASSIFIED_BEFORE = re.compile(r"(?:witness(?:es)?\s+(?:for|of)|(?<!to be )shown|proved|classified|removed|closed)\b[^;.()]{0,30}$",
                               re.IGNORECASE)  # 'witnesses for hypotheses 2, 3' lists classified ones


def classified_context(line, m):
    return bool(CLASSIFIED_AFTER.match(line, m.end()) or CLASSIFIED_BEFORE.search(line[max(0, m.start() - 60):m.start()]))


CODE = re.compile(r"`([A-Za-z_][\w.']*)`")


def parse_trust(text):
    """name -> {'n': count, 'needed': set, 'redundant': set, 'open': set}"""
    out = {}
    sec = text.split("## Hypothesis necessity, per headline", 1)
    if len(sec) < 2:
        raise SystemExit("check_stale_necessity: TRUST_MAP.md has no 'Hypothesis necessity, per headline' section; FAIL")
    for line in sec[1].splitlines():
        m = re.match(r"- `([^`]+)` \((\d+)\):(.*)$", line)
        if not m:
            continue
        body = re.sub(r"\(`[^`]*`\)", "", m.group(3))
        d = {"n": int(m.group(2)), "needed": set(), "redundant": set(), "open": set()}
        for part in body.split(";"):
            p = part.strip()
            if p.startswith("parts of") or p.startswith("shape"):
                continue
            for key in ("needed", "redundant", "open"):
                if p.startswith(key):
                    d[key] |= {int(x) for x in re.findall(r"\d+", p[len(key):])}
        out[m.group(1)] = d
    if not out:
        raise SystemExit("check_stale_necessity: no necessity entries parsed from TRUST_MAP.md; FAIL")
    return out


def resolver(trust):
    last = {}
    for k in trust:
        last.setdefault(k.split(".")[-1], []).append(k)

    def resolve(name):
        if name in trust:
            return name
        hits = [k for k in trust if k.endswith("." + name)]
        if len(hits) == 1:
            return hits[0]
        cands = last.get(name.split(".")[-1], [])
        return cands[0] if len(cands) == 1 and "." not in name else None
    return resolve


def nums(s):
    """the numbers of a list; 'a–b' (en dash) is the range a, …, b"""
    out = []
    for a, b in re.findall(r"(\d+)(?:\s*–\s*(\d+))?", s):
        out += list(range(int(a), int(b) + 1)) if b and int(b) >= int(a) and int(b) - int(a) < 50 else [int(a)]
    return out


def clauses(line):
    """(start, end) spans of the clauses of a line: split at ';' and at '. ' / ': ' only when they end a clause."""
    spans, start = [], 0
    for m in re.finditer(r";|\.\s+(?=[A-Z(`*])", line):
        spans.append((start, m.start()))
        start = m.end()
    spans.append((start, len(line)))
    return spans


def open_scopes(line):
    """character spans of the line that are inside an open scope"""
    out = []
    lab = LABEL.search(line)
    if lab:
        out.append((lab.end(), len(line)))
    for a, b in clauses(line):
        if OPEN_WORD.search(line[a:b]):
            out.append((a, b))
    return out


def scan_line(line, trust, resolve, section_heads=()):
    """[(name, hypothesis or None, claimed, why)] stale items of one line"""
    scopes = open_scopes(line)
    if not scopes:
        return []

    def inside(pos):
        return any(a <= pos < b for a, b in scopes)
    stale = []
    seen = set()

    def judge(name, hs, pos, how):
        h = resolve(name)
        if h is None or not inside(pos):
            return
        d = trust[h]
        for i in hs:
            if i < 1 or i > d["n"]:
                continue
            if (i in d["needed"] or i in d["redundant"]) and (h, i) not in seen:
                seen.add((h, i))
                cls = "NEEDED" if i in d["needed"] else "REDUNDANT"
                stale.append((h, i, how, f"TRUST_MAP.md: hypothesis {i} of `{h}` is {cls}"))
    for m in PA.finditer(line):
        if classified_context(line, m):
            continue
        judge(m.group(1), nums(m.group(2)), m.start(), "S-N1a")
    for m in PB.finditer(line):
        tail = m.group(2)
        cut = re.search(r"\.\s+[A-Z]", tail)
        tail = tail[:cut.start()] if cut else tail
        for c in CODE.finditer(tail):
            judge(c.group(1), nums(m.group(1)), m.start(), "S-N1b")
    paths = {p.replace("/", ".") for p in re.findall(r"Checked/((?!Trust/)[\w/]+)\.lean", line)}
    if paths:
        own = [h for h in trust if h.rsplit(".", 1)[0] in paths or
               any(h.rsplit(".", 1)[0].endswith("." + q) or q.endswith("." + h.rsplit(".", 1)[0]) for q in paths)]
        if own:
            section_heads = own
    line_names = {h for c in CODE.finditer(line) if (h := resolve(c.group(1)))}
    for pat in PE:
        for m in pat.finditer(line):
            if not inside(m.start()) or classified_context(line, m):
                continue
            a, b = next((a, b) for a, b in clauses(line) if a <= m.start() <= b)
            spans = [c.group(1) for c in CODE.finditer(line[a:b])]
            cl = {h for c in spans if (h := resolve(c))}
            if len(cl) > 1:
                continue  # several headlines in the clause: read only by (a) and (b)
            if not cl and any(not c.endswith((".lean", ".md", ".py", ".txt")) and "/" not in c for c in spans):
                continue  # the clause names something that is not a headline (`_fails` companions): referent unknown
            own = cl or (line_names if len(line_names) == 1 else set())
            for i in nums(m.group(1)):
                hs = [h for h in sorted(own) if trust[h]["n"] >= i]
                if not hs and not cl:  # the line's headline has no hypothesis i: the section's are meant
                    hs = [h for h in section_heads if trust[h]["n"] >= i]
                if hs and all(i in trust[h]["needed"] or i in trust[h]["redundant"] for h in hs) \
                        and all((h, i) not in seen for h in hs):
                    seen.update((h, i) for h in hs)
                    names = ", ".join(f"`{h.split('.')[-1]}`" for h in hs)
                    where = "named on the line" if set(hs) <= own else "named in this section"
                    stale.append((hs[0], i, "S-N1c", f"TRUST_MAP.md: hypothesis {i} of {names} ({where}) is "
                                                      f"classified"))
    for m in PC.finditer(line):
        h = resolve(m.group(2))
        if h is None:
            continue
        k = int(m.group(1))
        if len(trust[h]["open"]) < k:
            stale.append((h, None, "S-N2", f"TRUST_MAP.md: {len(trust[h]['open'])} open hypotheses of `{h}`, not {k}"))
    return stale


# ---------------------------------------------------------------------------------------------------------------
# Rules S-N4 and S-N5 (run 2026-11-21T0228Z): the default inverted. Two held-out writers (tests SN and SN2) put
# stale lines past the word rules above blind, 6/16 and 8/17: each round of open words and shapes added after
# reading one writer missed half of the next writer's lines. S-N4 does not look for open words. It finds every
# hypothesis number a line attaches to a headline with a necessity entry and flags each classified one unless the
# line states that same classification: the list is followed by its own word (`x` 2, 3 NEEDED), or its clause or
# sentence states it (needed / refutes / cannot be dropped / witnesses for; redundant) with no plan or open word and
# not the other classification. Blind figure (test SN3, frozen prototype `runs/2026-11-21T0228Z/t5/sn4_proto.py`,
# brief registered first): recall 15/16, false positives 0/10 (word rules: 10/16, 0/10).
# S-N5 (written after SN3, NOT blind): an ordinal description ('the first hypothesis', 'the last two hypotheses',
# 'the second-to-last hypothesis of `x`') is read as the numbers it names (11 of 11 description lines of the three
# writers were ordinal). Still not read: a description by content ('the density bound of `x`').
NUMR = r"\d{1,2}(?:\s*(?:/|,\s*and|,|and|&|or|–|-(?=\d{1,2}\b))\s*\d{1,2})*"
CUE = re.compile(r"hypothes|necessity|necessar|needed|redundan|\bopen\b|classif|unresolved|undone|unchecked|dropp?|"
                 r"remov|\bprove\b", re.IGNORECASE)
AGREE = re.compile(r"\s*(?:\([^)]*\)\s*)?(?:(?:is|are|both|each|all|now|shown|also|already|were|was)\s+)*"
                   r"(NEEDED|REDUNDANT|needed|redundant)\b")
PLAN = re.compile(r"\b(?:show|shows|showing|whether|need to|needs to|decide|determine|check|test|tested|testing|"
                  r"classify|settle|resolve|work out|try|to be|if|still|not yet|open|unclassified|unresolved|"
                  r"unchecked|undone|next|todo|to do|pending|remain|prove)\b", re.IGNORECASE)
MATH_BEFORE = re.compile(r"(?:[−+\-/^{=≥≤<>·×*(\[≈~]|\b(?:was|were|previously|formerly|about|other|another)|\bof\s+[a-zα-ω]|"
                         r"\b(?:β|η|Ω|λ|v|x|t|K|k|q|p|f)\s*(?:=|≥|≤|<|>))\s*$")
MATH_AFTER = re.compile(r"\s*(?:[/^{}·×*−+=]|\s[a-zα-ω]\b(?!\w))|\s+(?:min|minutes?|s|h|hours?|seconds?|digits|days?|GB|MB|"
                        r"times|cells|steps|modules|headlines|lines|runs|jobs|commands|files|items|words|readers|of\s+\d)\b")
NOUN_BEFORE = re.compile(r"\b(?:Tables?|Eqs?|Figs?|Figure|rows?|runs?|[Pp]arts?|items?|steps?|rounds?|pages?|order|"
                         r"index|[Ss]ections?|lines?|shards?|levels?|digits|degree|[Cc]hapter|[Aa]ppendix|[nNK]|β|"
                         r"of order)\.?\s*$")
ORD = {"first": 1, "second": 2, "third": 3, "fourth": 4, "fifth": 5, "sixth": 6, "seventh": 7, "eighth": 8,
       "ninth": 9, "tenth": 10}
CNT = {"two": 2, "three": 3, "four": 4}
PORD = re.compile(r"\bthe\s+(?:very\s+)?(first|second|third|fourth|fifth|sixth|seventh|eighth|ninth|tenth|last|final|"
                  r"second[- ]to[- ]last|next[- ]to[- ]last|penultimate)(?:\s+(two|three|four))?\s+(hypothes(?:is|es))\b",
                  re.IGNORECASE)


def _in_code(line, pos):
    return line[:pos].count("`") % 2 == 1


def _nums(s):
    out = []
    for a, b in re.findall(r"(\d+)(?:\s*[–-]\s*(\d+))?", s):
        out += list(range(int(a), int(b) + 1)) if b and 0 <= int(b) - int(a) < 50 else [int(a)]
    return out


def ordinals(line, trust, resolve, section_heads):
    """S-N5: the line with each ordinal description of hypotheses replaced by their numbers"""
    def sub(m):
        word, cnt = m.group(1).lower().replace(" ", "-"), m.group(2)
        k = CNT[cnt.lower()] if cnt else 1
        if word in ORD:
            idx = list(range(ORD[word], ORD[word] + k)) if word == "first" else [ORD[word]]
        else:
            a, b = next((a, b) for a, b in clauses(line) if a <= m.start() <= b)
            after = CODE.search(line, m.end(), b)
            if after and re.match(r"\s*(?:of|in|for)\s+$", line[m.end():after.start()]):
                h = resolve(after.group(1))
            else:
                cl = {h for c in CODE.finditer(line[a:b]) if (h := resolve(c.group(1)))}
                ln = {h for c in CODE.finditer(line) if (h := resolve(c.group(1)))}
                one = cl if len(cl) == 1 else ln if len(ln) == 1 else set(section_heads) if len(section_heads) == 1 else set()
                h = next(iter(one)) if one else None
            if h is None:
                return m.group(0)
            n = trust[h]["n"]
            last = n if word in ("last", "final") else n - 1
            idx = list(range(last - k + 1, last + 1))
        idx = [i for i in idx if i >= 1]
        if not idx:
            return m.group(0)
        return ("hypotheses " if len(idx) > 1 else "hypothesis ") + ", ".join(map(str, idx))
    return PORD.sub(sub, line)


def refs4(line, trust, resolve, section_heads):
    """(headline, number, start, end) of every hypothesis number the line attaches to a headline with an entry"""
    out = []
    names = [(m.start(), m.end(), resolve(m.group(1))) for m in CODE.finditer(line)]
    for a, b in clauses(line):
        cl = line[a:b]
        hs = [(s, e, h) for s, e, h in names if a <= s < b and h]
        others = [1 for s, e, h in names if a <= s < b and not h]
        cue = CUE.search(cl)
        for m in re.finditer(r"(?<![\w.\-/−])(" + NUMR + r")(?![\w%]|\.\d|\s*(?:→|->|≤|<|>|=|×|\*|\^))", cl):
            s = a + m.start()
            e = s + len(m.group(1))
            if NOUN_BEFORE.search(line[:s]) or MATH_BEFORE.search(line[:s]) or MATH_AFTER.match(line, e) \
                    or _in_code(line, s):
                continue  # a number of a formula, a table, a run or of code: not a hypothesis
            before = [(st, en, h) for st, en, h in hs if en <= s]
            after = [(st, en, h) for st, en, h in hs if st >= e]
            if before and re.match(r"^\s*`?[:–—-]?\s*(?:hypothes(?:is|es)\s+)?$", line[before[-1][1]:s]):
                own = [before[-1][2]]  # `x` 4, 5 / `x`: hypotheses 4, 5
            elif after and re.match(r"^\s*(?:(?:is|are)\s+)?(?:(?:needed|redundant|open)\s+)?(?:of|in|for|from)\s+"
                                    r"(?:the\s+\w+\s+)?$", line[e:after[0][0]]):
                own = [after[0][2]]  # 4, 5 of `x` / 16 is redundant in `x`
            elif re.search(r"hypothes(?:is|es)\s+$", line[a:s]) or cue:
                if hs:
                    own = [hs[0][2]] if len({h for _, _, h in hs}) == 1 else []
                elif others:
                    own = []  # the clause names something that is not a headline: referent unknown
                else:
                    own = list(section_heads) if len(section_heads) == 1 else []
            else:
                own = []
            for h in own:
                for i in _nums(m.group(1)):
                    if 1 <= i <= trust[h]["n"]:
                        out.append((h, i, s, e))
    return out


def scan_line4(line, trust, resolve, section_heads=()):
    """S-N4 (and S-N5 through `ordinals`): [(name, hypothesis, rule, why)]"""
    line = ordinals(line, trust, resolve, section_heads)
    out, seen = [], set()
    rs = refs4(line, trust, resolve, section_heads)
    for h, i, s, e in rs:  # a hypothesis stated with its own word anywhere on the line counts as stated
        d = trust[h]
        ag = AGREE.match(line, e)
        a = next(a for a, b in clauses(line) if a <= s <= b)
        if ag and ag.group(1).lower() == ("needed" if i in d["needed"] else "redundant" if i in d["redundant"] else "")\
                and not PLAN.search(line[a:s]):
            seen.add((h, i))
    for h, i, s, e in rs:
        d = trust[h]
        cls = "needed" if i in d["needed"] else "redundant" if i in d["redundant"] else None
        if cls is None or (h, i) in seen:
            continue
        a, b = next((a, b) for a, b in clauses(line) if a <= s <= b)
        ag = AGREE.match(line, e)
        if ag and ag.group(1).lower() == cls and not PLAN.search(line[a:s]):
            continue  # `x` 2, 3 NEEDED
        if re.search(r"(?:witness(?:es)?\s+(?:for|of)|(?<!to be )(?<!to )\bshown|\bproved|\bclassified|\bremoved|"
                     r"\bclosed)\b[^;]{0,40}$", line[a:s], re.IGNORECASE) and not PLAN.search(line[a:s]):
            continue  # witnesses for hypotheses 2, 3
        ev = {"needed": r"\bneeded\b|\bnecessary\b|refut|cannot be dropped|\bwitness", "redundant": r"\bredundant\b"}[cls]
        other = {"needed": r"\bredundant\b", "redundant": r"\bneeded\b|\bnecessary\b|refut|cannot be dropped"}[cls]
        sa = max([0] + [m.end() for m in re.finditer(r"\.\s+(?=[A-Z(`*])", line[:s])])
        nx = re.search(r"\.\s+(?=[A-Z(`*])|\.$", line[s:])
        sentence = line[sa:s + nx.start()] if nx else line[sa:]
        if any(re.search(ev, sp, re.IGNORECASE) and not PLAN.search(sp) and not re.search(other, sp, re.IGNORECASE)
               for sp in (line[a:b], sentence)):
            continue  # the clause or its sentence states this classification, and no other, and no plan
        seen.add((h, i))
        out.append((h, i, "S-N4", f"TRUST_MAP.md: hypothesis {i} of `{h}` is {cls.upper()}; the line does not "
                                  f"state it so"))
    return out


# Rule S-N3 (run 2026-11-21T0228Z, NOT blind; planned in brief SN2): a clause that names exactly one headline whose
# TRUST_MAP entry has NO open hypothesis, and calls something about its hypotheses open or to be decided, is stale
# whatever words describe the hypothesis ('two hypotheses of `x` are open: C² on the open ball and radial
# symmetry', run 2026-11-20T1828Z, true then, stale since). Cost when introduced: 0 lines of the three files; 6 lines
# of dated run records (not read), 4 of them stale plans.
HYPW = re.compile(r"hypothes|assumption|\bcondition|necessity|redundan|\bneeded\b|droppable|can be dropped", re.IGNORECASE)
OPENW3 = re.compile(r"\b(?:open|unclassified|unresolved|undone|not yet|still to be shown|remaining|classify|settle|"
                    r"decide whether|whether|to be shown|unknown|unchecked)\b", re.IGNORECASE)


def scan_line3(line, trust, resolve):
    out = []
    for a, b in clauses(line):
        cl = line[a:b]
        hs = {h for m in CODE.finditer(cl) if (h := resolve(m.group(1)))}
        if len(hs) == 1:
            h = next(iter(hs))
            if not trust[h]["open"] and HYPW.search(cl) and OPENW3.search(cl):
                out.append((h, None, "S-N3", f"TRUST_MAP.md: `{h}` has no open hypothesis (all {trust[h]['n']} "
                                             f"classified)"))
    return out


def scan(text, trust):
    resolve = resolver(trust)
    out = []
    lines = text.splitlines()
    heads, start = [], 0
    for n, line in enumerate(lines, 1):
        if line.startswith("## ") or n == 1:
            end = next((k for k in range(n, len(lines)) if lines[k].startswith("## ")), len(lines))
            sec = "\n".join(lines[n - 1:end])
            heads = sorted({h for c in CODE.findall(sec) if (h := resolve(c))})
        items = scan_line(line, trust, resolve, heads)
        got = {(h, i) for h, i, _, _ in items}
        items += [x for x in scan_line4(line, trust, resolve, heads) if (x[0], x[1]) not in got]
        items += [x for x in scan_line3(line, trust, resolve) if x[0] not in {y[0] for y in items}]
        for item in items:
            out.append((n, *item))
    return out


def selftest():
    trust = parse_trust("\n".join([
        "## Hypothesis necessity, per headline", "",
        "- `Fid.core_pins` (2): needed 1 (`core_pins_h1`), 2 (`core_pins_h2`); shape: bundled 2",
        "- `FS.mono_lt` (7): needed 1 (`mono_lt_h1`); redundant 6 (`mono_lt_r6`); open 4, 7",
        "- `FS.sep_equal` (18): needed 1 (`a`); open 2, 3, 4",
        "- `A.dup_name` (1): needed 1 (`x`)",
        "- `B.dup_name` (1): open 1",
        "- `FS.Sep.below` (9): needed 1 (`b1`); redundant 7 (`b7`); open 4, 5",
    ]))
    cases = [
        ("Not yet: part 2 of `core_pins`; `mono_lt` 7.", []),                        # 'part 2 of' is not read
        ("Not yet: `core_pins` 2; `mono_lt` 7.", [("Fid.core_pins", 2)]),           # label scope, bundled needed
        ("- the open hypotheses `mono_lt` 4/6/7 next", [("FS.mono_lt", 6)]),         # REDUNDANT 6 stale
        ("Measure: `mono_lt` 6 is REDUNDANT; open 120 -> 110.", []),                  # different clause, no number item
        ("`mono_lt` 6 shown REDUNDANT (run X).", []),                                # no open scope
        ("Open in this family: hypothesis 1 of the pair (`core_pins`, `mono_lt`).", [("Fid.core_pins", 1),
                                                                                      ("FS.mono_lt", 1)]),
        ("the 16 open hypotheses of `sep_equal` remain", [("FS.sep_equal", None)]),  # S-N2
        ("the 3 open hypotheses of `sep_equal` remain", []),
        ("Not yet: `dup_name` 1.", []),                                               # ambiguous last component
        ("Not yet: `A.dup_name` 1.", [("A.dup_name", 1)]),
        ("open: `mono_lt` 0.95 of the window", []),                                   # a decimal is not a list
        ("Not yet: `mono_lt` 1–3 by profiles", [("FS.mono_lt", 1)]),                 # en-dash range, 1 NEEDED
    ]
    sect = ["FS.mono_lt"]
    cases_d = [
        ("- **Necessity**: 1 NEEDED, 6 REDUNDANT; 4 open (LEDGER)", []),
        ("- **Necessity**: 1 NEEDED; 6 open (LEDGER)", [("FS.mono_lt", 6)]),         # section headline, REDUNDANT 6
        ("- **Necessity**: 1 NEEDED; open 6, 7", [("FS.mono_lt", 6)]),
        ("- Measure: needed 12 → 13, open 6 → 5", []),                               # a count, not a hypothesis
        ("- **Necessity**: `core_pins` 1 NEEDED; 6 open", [("FS.mono_lt", 6)]),       # clause without a name
        ("- **Necessity**: 6 open for `core_pins`", []),                              # named clause: read by (a)
        ("- **Run Y** (`Checked/FS/Sep.lean`): 1 NEEDED, 4–7 open", [("FS.Sep.below", 7)]),  # path: its own module
        ("- Next: hypotheses 6, 7 of the rows (`Checked/FS/Sep.lean`)", [("FS.Sep.below", 7)]),  # list end, no name
        ("- Part 1: the `_x` companions' hypothesis 6; `core_pins` 1 NEEDED", []),   # unknown referent: not read
        ("- Next: classify 1, 4 and 6", [("FS.mono_lt", 1), ("FS.mono_lt", 6)]),     # plan verb, section
        ("- **Necessity:** hypotheses 1 and 6 NEEDED", []),                          # no open scope
        ("- Still to be shown: that 6 is redundant", [("FS.mono_lt", 6)]),
        ("- witnesses for hypotheses 1, 6 (`N.lean`), 4, 7 disclosed open", []),     # classified by context
        ("- open baseline updated (`mono_lt` 1, 6 removed)", []),                    # not an open claim
    ]
    cases4 = [  # S-N4 / S-N5 (run 2026-11-21T0228Z): no open word needed; a stated classification passes
        ("- Need to show `mono_lt` 6 redundant.", [("FS.mono_lt", 6)]),             # plan verb before an agreeing word
        ("Part 2: check whether 6 is redundant in `mono_lt`.", [("FS.mono_lt", 6)]),  # number before 'in `x`'
        ("Next: `mono_lt` - prove 1 necessary; also `sep_equal` hypothesis 1.", [("FS.mono_lt", 1), ("FS.sep_equal", 1)]),
        ("- **Redundancy:** `mono_lt` hyps 6 not yet tested.", [("FS.mono_lt", 6)]),
        ("Not yet: `mono_lt` 1-3 by profiles.", [("FS.mono_lt", 1)]),                # hyphen range; 2, 3 have no entry
        ("Not yet: the sixth hypothesis of `mono_lt`.", [("FS.mono_lt", 6)]),         # S-N5 ordinal
        ("- `mono_lt`: the very first hypothesis is still unclassified.", [("FS.mono_lt", 1)]),
        ("Open: whether the second-to-last hypothesis of `mono_lt` can go.", [("FS.mono_lt", 6)]),
        ("- `mono_lt`: 1 NEEDED, 6 REDUNDANT; 4, 7 open.", []),                       # agreeing statement
        ("- `mono_lt` 1 and 6: both shown, 1 needed and 6 redundant (witnesses in `N.lean`).", []),
        ("- the last hypothesis of `mono_lt` is still open.", []),                     # 7 is open
        ("- velocity 1 − e^{−η} for `mono_lt` (Table 6, row 1, run 6).", []),         # formula, table, row, run
        ("- Next: `mono_lt` 4 and 7 (both open).", []),
        ("- with zero wall value it refutes `mono_lt` (hypothesis 1).", []),           # refutation states NEEDED
        ("- push (`mono_lt`: six new modules, data ≈ 2 min); the other 6 disclosed open.", []),  # durations, counts
        ("- Next: hypothesis 1 of `mono_lt` takes 6 min; then 6 of `mono_lt`.", [("FS.mono_lt", 1), ("FS.mono_lt", 6)]),
    ]
    cases3 = [  # S-N3: `core_pins` has no open hypothesis
        ("- the bundled condition of `core_pins` is still open.", [("Fid.core_pins", None)]),
        ("- `core_pins`: whether the second condition can be dropped.", [("Fid.core_pins", None)]),
        ("- `core_pins` fully classified; `mono_lt` 4 and 7 open.", []),
        ("- the wall condition of `mono_lt` is open.", []),                           # `mono_lt` has open ones
        ("- Next: promote `core_pins` to the reader page.", []),                     # no hypothesis word
    ]
    fails = 0
    resolve = resolver(trust)
    for text, want in cases3:
        got = [(h, i) for h, i, _, _ in scan_line3(text, trust, resolve)]
        if got != want:
            print(f"selftest FAIL (S-N3): {text!r}: expected {want}, got {got}")
            fails += 1
    for text, want in cases4:
        got = [(h, i) for h, i, _, _ in scan_line4(text, trust, resolve)]
        if got != want:
            print(f"selftest FAIL (S-N4): {text!r}: expected {want}, got {got}")
            fails += 1
    for text, want in cases:
        got = [(h, i) for h, i, _, _ in scan_line(text, trust, resolve)]
        if got != want:
            print(f"selftest FAIL: {text!r}: expected {want}, got {got}")
            fails += 1
    for text, want in cases_d:
        got = [(h, i) for h, i, _, _ in scan_line(text, trust, resolve, sect)]
        if got != want:
            print(f"selftest FAIL (section): {text!r}: expected {want}, got {got}")
            fails += 1
    print(f"check_stale_necessity selftest: {len(cases) + len(cases_d) + len(cases4) + len(cases3)} controls; {'FAIL' if fails else 'ok'}")
    return 1 if fails else 0


def main(argv):
    if "--selftest" in argv:
        return selftest()
    if selftest():
        return 1
    trust = parse_trust(TRUST.read_text(encoding="utf-8"))
    files = argv[argv.index("--measure") + 1:] if "--measure" in argv else list(FILES)
    total = 0
    for f in files:
        p = ROOT / f
        got = scan(p.read_text(encoding="utf-8"), trust)
        total += len(got)
        for n, h, i, how, why in got:
            what = f"hypothesis {i} of `{h}`" if i else (f"the hypotheses of `{h}`" if how == "S-N3" else f"the open count of `{h}`")
            print(f"{f}:{n}: {how} STALE: called open, {why}. Rewrite the line (drop the item, or say it was "
                  f"classified since, without its number).  [{what}]")
    print(f"check_stale_necessity ({', '.join(files)}): {total} finding(s); {'FAIL' if total else 'ok'}")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
