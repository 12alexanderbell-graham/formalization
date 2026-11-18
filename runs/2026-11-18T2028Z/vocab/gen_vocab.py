#!/usr/bin/env python3
"""Run 2026-11-18T2028Z (part 3): the words of the generated pages (CLAIMS_READER.md, TRUST_MAP.md) minus STATUS,
tokenized exactly as check_headline_mentions reads a line. Prints one word per line, sorted."""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_headline_mentions as C
keys, fulls, modules = C.headlines()
out = set()
for f in ["CLAIMS_READER.md", "TRUST_MAP.md"]:
    for l in (ROOT / f).read_text(encoding="utf-8").splitlines():
        out |= {w for w in C.tokens(C.words(C.norm(l), fulls, modules)) if len(w) > 1 and not C.STATUS.match(w)}
print("\n".join(sorted(out)))
