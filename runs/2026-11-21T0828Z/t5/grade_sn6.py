#!/usr/bin/env python3
"""Grade held-out writer SN6 with the frozen rule (sn6_frozen.py, commit 699ff0a) and with main before it (rules
S-N1..S-N5). A line counts as flagged when any finding names a headline of the key line."""
import importlib.util, re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
D = Path(__file__).resolve().parent
def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
new = load(D / (sys.argv[1] if len(sys.argv) > 1 else "sn6_frozen.py"), "sn6")
old_src = subprocess.run(["git", "-C", str(ROOT), "show", "db96093:scripts/trust/check_stale_necessity.py"], capture_output=True, text=True).stdout
(D / "_old.py").write_text(old_src); old = load(D / "_old.py", "old"); (D / "_old.py").unlink()
trust = new.parse_trust((ROOT / "TRUST_MAP.md").read_text())
lines = [l for l in (D / "LINES_SN6.md").read_text().splitlines() if l.startswith("- ")]
key = {}
for l in (D / "KEY_SN6.md").read_text().splitlines():
    m = re.match(r"(\d+)\.\s+(STALE|HONEST)", l)
    if m: key[int(m.group(1))] = m.group(2)
res = {}
for name, mod in (("main before (S-N1..5)", old), ("frozen S-N6", new)):
    tp = fn = fp = 0; rows = []
    for i, l in enumerate(lines, 1):
        f = mod.scan(l, trust)
        flagged = bool(f)
        k = key[i]
        rows.append(f"{i:2d} {k:6s} {'FLAG' if flagged else '----'} {[x[3] for x in f]}")
        if k == "STALE": tp += flagged; fn += not flagged
        else: fp += flagged
    print(f"== {name}: recall {tp}/{tp+fn}; honest lines flagged {fp}/{len(lines)-tp-fn}")
    print("\n".join(rows))
