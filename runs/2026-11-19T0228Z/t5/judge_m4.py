#!/usr/bin/env python3
"""Run 2026-11-19T0228Z: re-run red team M4's reported lines (m4_lines.txt, `FILE|LINE`) against the working tree's
check with try_line.py's placement (STATE.md: under the Gelfand multiplicity heading). Prints PASS or the first finding."""
import subprocess, sys
from pathlib import Path
H = Path(__file__).parent
n = 0
for row in (H / "m4_lines.txt").read_text(encoding="utf-8").splitlines():
    f, line = row.split("|", 1)
    out = subprocess.run([sys.executable, str(H / "try_line.py"), f, line], capture_output=True, text=True).stdout
    ok = out.startswith("PASS")
    n += ok
    print(f"{'PASS   ' if ok else 'flagged'} {f}: {line[:90]}")
print(f"{n} of {len(open(H / 'm4_lines.txt').read().splitlines())} lines pass")
