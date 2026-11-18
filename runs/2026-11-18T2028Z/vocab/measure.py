#!/usr/bin/env python3
"""Run 2026-11-18T2028Z (part 3): replay check_headline_mentions on the records of past runs with a given vocabulary.
Usage: measure.py [vocab file]   (default: scripts/trust/mention_vocab.txt). Prints findings per run (M1 / M2 / other)."""
import sys, re, collections
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_headline_mentions as C

PAIRS = [("5c6a05b", "fa47717"), ("fa47717", "c32a441"), ("c32a441", "25fd5dd"), ("25fd5dd", "adcb9a6"),
         ("adcb9a6", "7d5b41c"), ("7d5b41c", "a736a0b"), ("a736a0b", "d25cb3f"),
         ("7717f08", "1473ec0"), ("1473ec0", "2788d1e")]

def main():
    vf = sys.argv[1] if len(sys.argv) > 1 else str(ROOT / C.VOCAB)
    vocab = C.load_vocab(Path(vf).read_text(encoding="utf-8"))
    obj = C.load_obj()
    tot = 0
    words = collections.Counter()
    for b, h in PAIRS:
        errs = C.run(C.files_at(b), C.files_at(h), vocab=vocab, obj=obj)
        lines = {e.split(": about")[0].split(": M")[0] for e in errs}
        m1 = [e for e in errs if " M1 " in e]
        for e in m1:
            for w in e.split(C.VOCAB + ": ")[1].split(", "):
                words[w] += 1
        print(f"{b}..{h}: {len(errs)} findings on {len(lines)} lines (M1 {len(m1)}, M2 {sum(' M2 ' in e for e in errs)})")
        if b < "7717f08" or True:
            tot += len(lines) if (b, h) in PAIRS[:7] else 0
    print(f"seven runs 5c6a05b..d25cb3f: {tot} flagged lines, {len(vocab)} vocabulary words")
    print("most frequent unknown words:", ", ".join(f"{w} {n}" for w, n in words.most_common(60)))

if __name__ == "__main__":
    main()
