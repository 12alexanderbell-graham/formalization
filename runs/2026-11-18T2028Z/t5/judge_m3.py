#!/usr/bin/env python3
"""Run 2026-11-18T2028Z: re-run red team M3's reported lines, each appended to README.md (as the red team placed most),
against the working tree's check. Prints PASS (defect accepted) or the findings."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_headline_mentions as C
head = C.files_at(None)
for f in ["README.md", "STATE.md"]:
    for d in (Path(__file__).parent / "m3_lines.txt").read_text(encoding="utf-8").splitlines():
        new = dict(head)
        new[f] = head[f].rstrip("\n") + "\n\n" + d + "\n"
        e = C.run(head, new)
        print(f"{f}: {'PASS (accepted)' if not e else 'flagged: ' + e[0].split(': ', 1)[1][:110]} | {d[:70]}")
