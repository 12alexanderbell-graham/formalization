#!/usr/bin/env python3
"""Run 2026-11-19T1428Z: re-run every red-team line (file ||| under ||| line ||| ...) with try_line.py in the working
tree of the current directory and print PASS/FLAGGED per line. Usage: judge_lines.py LINES_FILE"""
import subprocess, sys
from pathlib import Path
T = "runs/2026-11-19T0228Z/t5/try_line.py"
n = p = 0
for raw in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
    parts = [x.strip() for x in raw.split("|||")]
    if len(parts) < 3 or parts[0] not in ("STATE.md", "README.md", "BLUEPRINT.md"):
        continue
    f, under, line = parts[0], parts[1], parts[2]
    cmd = ["python3", T, f, line] + ([] if under in ("-", "") else ["--under", under])
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    ok = out.startswith("PASS")
    n += 1; p += ok
    print(("PASS    " if ok else "FLAGGED ") + line)
print(f"{n} lines, {p} pass, {n - p} flagged")
