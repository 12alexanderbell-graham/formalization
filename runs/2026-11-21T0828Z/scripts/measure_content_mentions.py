#!/usr/bin/env python3
"""Part 3 measurement (run 2026-11-21T0828Z; section Next of runs/2026-11-21T0228Z/README.md): how often do the
hand-written records describe a hypothesis of a headline that still has open hypotheses by its CONTENT (no number),
the limit stated in check_stale_necessity.py?  Lists every line of STATE.md, README.md, BLUEPRINT.md and the last
N run READMEs that names such a headline (full name, unique suffix or last component) together with a hypothesis
content word, and no hypothesis number attached to the name.  Output: the lines, for hand classification."""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
tm = (ROOT / "TRUST_MAP.md").read_text()
sec = tm[tm.index("## Hypothesis necessity, per headline"):]
heads = {}
for m in re.finditer(r"^- `([^`]+)` \((\d+)\):(.*)$", sec, re.M):
    o = re.search(r"open ([\d, ]+)", m.group(3))
    if o:
        heads[m.group(1)] = [int(x) for x in re.findall(r"\d+", o.group(1))]
names = {}
for h in heads:
    parts = h.split(".")
    for k in range(len(parts)):
        names.setdefault(".".join(parts[k:]), set()).add(h)
names = {n: hs for n, hs in names.items() if len(hs) == 1}
CONTENT = re.compile(r"\b(bound|condition|range|hypothes[ie]s|assumption|regularity|symmetry|wall|initial|"
                     r"limit|decay|positivity|sign|window|density|curvature|law|source|redshift|data|box|"
                     r"offset|scale|residual|selection|continuity|differentiab\w*)\b", re.I)
files = [ROOT / f for f in ("STATE.md", "README.md", "BLUEPRINT.md")]
nrun = int(sys.argv[1]) if len(sys.argv) > 1 else 10
files += sorted((ROOT / "runs").glob("2026-*/README.md"))[-nrun:]
hits = 0
for f in files:
    for i, line in enumerate(f.read_text().splitlines(), 1):
        for n, hs in names.items():
            for m in re.finditer(r"`(?:[\w.]*\.)?" + re.escape(n) + r"`", line):
                after = line[m.end():m.end() + 25]
                if re.match(r"\s*(?:hypothes\w+\s*)?\(?\d", after):
                    continue
                win = line[max(0, m.start() - 120):m.end() + 120]
                cm = CONTENT.findall(win)
                if cm:
                    hits += 1
                    print(f"{f.relative_to(ROOT)}:{i}: [{next(iter(hs))} open {heads[next(iter(hs))]}] "
                          f"words={sorted(set(w.lower() for w in cm))} :: {win.strip()[:260]}")
print("candidate mentions:", hits, file=sys.stderr)
