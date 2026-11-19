#!/usr/bin/env python3
"""Run 2026-11-19T1428Z: cost of M8 on the records. For each run-final commit since SINCE (default 2026-11-18), the
new about-lines (against the previous run-final commit) that the current rules flag with M8 and pass without it."""
import subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_headline_mentions as C
since = sys.argv[1] if len(sys.argv) > 1 else "2026-11-18T00:00"
log = subprocess.run(["git", "log", "--first-parent", "--reverse", f"--since={since}", "--format=%H %s", "main"],
                     cwd=ROOT, capture_output=True, text=True).stdout.splitlines()
finals = [l.split(" ", 1) for l in log if " final" in l.split(":")[0]]
total = 0
for (b, _), (h, msg) in zip(finals, finals[1:]):
    bf, hf = C.files_at(b), C.files_at(h)
    allid = {C.ident(l) for t in hf.values() for l in t.splitlines()}
    on = set(C.run(bf, hf)); off = set(C.run(bf, hf, m8_pre=allid))
    extra = sorted(on - off)
    total += len(extra)
    print(f"{h[:8]} {msg[:40]!r}: {len(extra)}")
    for e in extra:
        print("   ", e[:300])
print(f"{len(finals) - 1} runs, {total} lines flagged by M8 only")
