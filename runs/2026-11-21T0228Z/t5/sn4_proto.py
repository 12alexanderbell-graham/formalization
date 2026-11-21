#!/usr/bin/env python3
"""Prototype of rule S-N4 (default-deny) for check_stale_necessity.py, measured on writers SN, SN2 and the records."""
import json, re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_stale_necessity as c

NUMR = r"\d{1,2}(?:\s*(?:/|,\s*and|,|and|&|or|–|-(?=\d{1,2}\b))\s*\d{1,2})*"
CUE = re.compile(r"hypothes|necessity|needed|redundan|\bopen\b|classif|unresolved|undone|unchecked|dropp?|remov", re.I)
AGREE = re.compile(r"\s*(?:\([^)]*\)\s*)?(?:(?:is|are|both|each|all|now|shown|also|already|were|was)\s+)*(NEEDED|REDUNDANT|needed|redundant)\b")
PLAN = re.compile(r"\b(?:show|shows|showing|whether|need to|needs to|decide|determine|check|test|tested|testing|classify|"
                  r"settle|resolve|work out|try|to be|if|still|not yet|open|unclassified|unresolved|unchecked|undone|"
                  r"next|todo|to do|pending|remain)\b", re.I)
ALLOW_BEFORE = re.compile(r"(?:witness(?:es)?\s+(?:for|of)|(?<!to be )(?<!to )shown|proved|classified|removed|closed|"
                          r"hypotheses|hypothesis)\s*$", re.I)


MATH_BEFORE = re.compile(r"(?:[−+\-/^{=≥≤<>·×*(\[]|\b(?:was|were|previously|formerly)|\bof\s+[a-zα-ω]|\b(?:β|η|Ω|λ|v|x|t|K|k|q|p|f)\s*(?:=|≥|≤|<|>))\s*$")
MATH_AFTER = re.compile(r"\s*(?:[/^{}·×*−+=]|\s[a-zα-ω]\b(?!\w))")


NOUN_BEFORE = re.compile(r"\b(?:Tables?|Eqs?|Figs?|Figure|rows?|runs?|[Pp]arts?|items?|steps?|rounds?|pages?|order|index|"
                         r"[Ss]ections?|lines?|shards?|levels?|digits|degree|[Cc]hapter|[Aa]ppendix|[nNK]|β|of order)\.?\s*$")


def in_code(line, pos):
    """inside a backtick span"""
    return line[:pos].count("`") % 2 == 1


def nums(s):
    out = []
    for a, b in re.findall(r"(\d+)(?:\s*[–-]\s*(\d+))?", s):
        out += list(range(int(a), int(b) + 1)) if b and 0 <= int(b) - int(a) < 50 else [int(a)]
    return out


def refs(line, trust, resolve, section_heads):
    """(headline, number, start, end) of every hypothesis number the line attaches to a headline with a necessity entry"""
    out = []
    names = [(m.start(), m.end(), resolve(m.group(1))) for m in c.CODE.finditer(line)]
    for a, b in c.clauses(line):
        cl = line[a:b]
        hs = [(s, e, h) for s, e, h in names if a <= s < b and h]
        others = [1 for s, e, h in names if a <= s < b and not h]
        cue = CUE.search(cl)
        for m in re.finditer(r"(?<![\w.\-/−])(" + NUMR + r")(?![\w.%]|\s*(?:→|->|≤|<|>|=|×|\*|\^))", cl):
            s = a + m.start()
            if NOUN_BEFORE.search(line[:s]) or MATH_BEFORE.search(line[:s]) or MATH_AFTER.match(line, s + len(m.group(1))) or in_code(line, s):
                continue  # a number of a formula or of code, not a hypothesis
            # the headline this list belongs to: the nearest named headline before it in the clause, else after it
            # ('of/in `x`'), else the line's single headline, else the section's
            before = [h for st, e, h in hs if e <= s]
            after = [h for st, e, h in hs if st >= s + len(m.group(1))]
            if before and re.match(r"^\s*`?[:–—-]?\s*(?:hypothes(?:is|es)\s+)?$", line[[e for st, e, h in hs if e <= s][-1]:s]):
                own = [before[-1]]
            elif after and re.match(r"^\s*(?:(?:is|are)\s+)?(?:(?:needed|redundant|open)\s+)?(?:of|in|for|from)\s+(?:the\s+\w+\s+)?$", line[s + len(m.group(1)):[st for st, e, h in hs if st >= s + len(m.group(1))][0]]):
                own = [after[0]]
            elif re.search(r"hypothes(?:is|es)\s+$", line[a:s]) or cue:
                if hs:
                    own = [hs[0][2]] if len({h for _, _, h in hs}) == 1 else []
                elif others:
                    own = []
                else:
                    own = list(section_heads) if len(section_heads) == 1 else []
            else:
                own = []
            for h in own:
                for i in nums(m.group(1)):
                    if 1 <= i <= trust[h]["n"]:
                        out.append((h, i, s, s + len(m.group(1))))
    return out


def scan_line(line, trust, resolve, section_heads=()):
    st = []
    for h, i, s, e in refs(line, trust, resolve, section_heads):
        d = trust[h]
        if i in d["open"]:
            continue
        cls = "needed" if i in d["needed"] else "redundant" if i in d["redundant"] else None
        if cls is None:
            continue
        a, b = next((a, b) for a, b in c.clauses(line) if a <= s <= b)
        ag = AGREE.match(line, e)
        # an agreeing statement: the list is followed by its own classification, with no plan word before it
        if ag and ag.group(1).lower() == cls and not PLAN.search(line[a:s]):
            continue
        if ALLOW_BEFORE.search(line[max(a, s - 40):s]) and ag and ag.group(1).lower() == cls and not PLAN.search(line[a:s]):
            continue
        if re.search(r"(?:witness(?:es)?\s+(?:for|of)|(?<!to be )(?<!to )\bshown|\bproved|\bclassified|\bremoved|\bclosed)\b[^;]{0,40}$",
                     line[a:s], re.I) and not PLAN.search(line[a:s]):
            continue
        clause = line[a:b]
        ev = {"needed": r"\bneeded\b|refut|cannot be dropped|\bwitness", "redundant": r"\bredundant\b"}[cls]
        other = {"needed": r"\bredundant\b", "redundant": r"\bneeded\b|refut|cannot be dropped"}[cls]
        sa = max([0] + [m.end() for m in re.finditer(r"\.\s+(?=[A-Z(`*])", line[:s])])
        se = next((sa2.start() for sa2 in re.finditer(r"\.\s+(?=[A-Z(`*])|\.$", line[s:])), len(line) - s) + s
        sentence = line[sa:se]
        for span in (clause, sentence):
            if re.search(ev, span, re.I) and not PLAN.search(span) and not re.search(other, span, re.I):
                break  # the clause, or its sentence, states this classification (and no other, and no plan)
        else:
            span = None
        if span is not None:
            continue
        st.append((h, i, "S-N4", f"hypothesis {i} of `{h}` is {cls.upper()} in TRUST_MAP.md; the line does not state it so"))
    # dedupe
    seen, out = set(), []
    for x in st:
        if x[:2] not in seen:
            seen.add(x[:2]); out.append(x)
    return out


def scan(text, trust):
    resolve = c.resolver(trust)
    out = []
    lines = text.splitlines()
    heads = []
    for n, line in enumerate(lines, 1):
        if line.startswith("## ") or n == 1:
            end = next((k for k in range(n, len(lines)) if lines[k].startswith("## ")), len(lines))
            sec = "\n".join(lines[n - 1:end])
            heads = sorted({h for cc in c.CODE.findall(sec) if (h := resolve(cc))})
        for item in scan_line(line, trust, resolve, heads):
            out.append((n, *item))
    return out


if __name__ == "__main__":
    trust = c.parse_trust((ROOT / "TRUST_MAP.md").read_text(encoding="utf-8"))
    for tag, f in (("SN", "runs/2026-11-20T2028Z/t5/writer_SN.json"), ("SN2", "runs/2026-11-21T0228Z/t5/writer_SN2.json")):
        d = json.load(open(ROOT / f))
        rows = []
        for e in d:
            text = "# x\n\n" + (f"## Section on `{e['section_headline']}`\n" if e.get("section_headline") else "") + e["line"] + "\n"
            old = bool(c.scan(text, trust)); new = bool(scan(text, trust))
            rows.append((e["id"], e["kind"], e.get("by_number"), old, new, e["line"]))
        for lab, idx in (("current", 3), ("S-N4", 4), ("either", None)):
            g = (lambda r: r[3] or r[4]) if idx is None else (lambda r, i=idx: r[i])
            sn = [r for r in rows if r[1] == "STALE" and r[2]]; sd = [r for r in rows if r[1] == "STALE" and not r[2]]
            tr = [r for r in rows if r[1] == "TRUE"]
            print(f"{tag} {lab}: recall {sum(map(g, sn))}/{len(sn)}, desc {sum(map(g, sd))}/{len(sd)}, FP {sum(map(g, tr))}/{len(tr)}")
        for r in rows:
            if (r[1] == "STALE" and r[2] and not r[4]) or (r[1] == "TRUE" and r[4]):
                print("   ", "MISS" if r[1] == "STALE" else "FP", r[0], r[5][:130])
    if "--records" in sys.argv:
        for f in ("STATE.md", "README.md", "BLUEPRINT.md"):
            for n, h, i, how, why in scan((ROOT / f).read_text(encoding="utf-8"), trust):
                print(f"{f}:{n}: {why}")
