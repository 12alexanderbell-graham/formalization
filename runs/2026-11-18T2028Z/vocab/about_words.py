#!/usr/bin/env python3
"""Run 2026-11-18T2028Z (part 3): words used by the lines of the current records that check_headline_mentions reads as
about a listed headline (STATE.md, README.md, BLUEPRINT.md, run-record front pages at HEAD), minus STATUS, with counts.
Usage: about_words.py [exclude-file]  — words in the exclude file are left out."""
import sys, collections
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_headline_mentions as C
import re
excl = set()
if len(sys.argv) > 1:
    excl = {l.strip() for l in Path(sys.argv[1]).read_text().splitlines() if l.strip()}
keys, fulls, modules = C.headlines()
cnt = collections.Counter()
for path, txt in C.files_at(None).items():
    lines = txt.splitlines()
    bidx, chains = C.blocks_of(lines)
    front = len(lines)
    if C.RUN_README.match(path):
        std = [i for i, l in enumerate(lines) if re.match(r"^## (Start|Bottleneck|What we did)\b", l)]
        front = std[0] if std else next((i for i, l in enumerate(lines) if l.startswith("## ")), len(lines))
    for i, l in enumerate(lines[:front]):
        if not l.strip() or not C.about(lines, i, bidx, chains, keys):
            continue
        for w in C.tokens(C.words(C.norm(l), fulls, modules)):
            if len(w) > 1 and not C.STATUS.match(w) and w not in excl:
                cnt[w] += 1
for w, n in sorted(cnt.items(), key=lambda x: (-x[1], x[0])):
    print(f"{w}\t{n}")
