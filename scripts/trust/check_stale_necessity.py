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

Limits: a word list for the scope; a hypothesis described without its number ('the wall condition of `x`') is not
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
        for item in scan_line(line, trust, resolve, heads):
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
    fails = 0
    resolve = resolver(trust)
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
    print(f"check_stale_necessity selftest: {len(cases) + len(cases_d)} controls; {'FAIL' if fails else 'ok'}")
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
            what = f"hypothesis {i} of `{h}`" if i else f"the open count of `{h}`"
            print(f"{f}:{n}: {how} STALE: called open, {why}. Rewrite the line (drop the item, or say it was "
                  f"classified since, without its number).  [{what}]")
    print(f"check_stale_necessity ({', '.join(files)}): {total} finding(s); {'FAIL' if total else 'ok'}")
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
