#!/usr/bin/env python3
"""Run 2026-11-18T2028Z: how many new lines about a headline also name a source (a year 1900-2099 outside code spans,
or paper/source/table/literature/printed/published/article), per run over the nine replayed runs — the cost of a
'template-only or registered objection' rule for such lines (next part-3 step)."""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_headline_mentions as C
from measure import PAIRS
SRC = re.compile(r"(?<![\w.])(19\d\d|20\d\d)(?![\w.])|\b(papers?|sources?|tables?|literature|printed|published|articles?)\b")
keys, fulls, modules = C.headlines()
tot = 0
for b, h in PAIRS:
    old = {C.ident(l) for t in C.files_at(b).values() for l in t.splitlines()}
    n = 0
    for path, txt in C.files_at(h).items():
        lines = txt.splitlines(); bidx, chains = C.blocks_of(lines)
        for i, l in enumerate(lines):
            if not l.strip() or C.ident(l) in old:
                continue
            if C.RUN_README.match(path) and any(x.startswith("## ") for x in lines[:i]):
                continue
            t = re.sub(r"`[^`]*`", " ", C.norm(l))
            if SRC.search(t) and C.about(lines, i, bidx, chains, keys):
                n += 1
    tot += n
    print(f"{b}..{h}: {n} new about-lines naming a source")
print(f"total {tot} over {len(PAIRS)} runs")
