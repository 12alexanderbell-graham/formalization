"""Pre-flight for StatementDeps' citation rule (run 2026-11-18T0628Z, annex LIV).

StatementDeps reads every backticked token of STATE.md and FINDINGS.md (and `a[_b]` variants) and, when it
names exactly one Checked theorem by suffix, requires that theorem to be a registered headline. A helper
lemma with a short name (`src`, `band`, `S1`) collides with a backticked word (`[src]` tags of FINDINGS.md)
and fails the relock only after ≈ 10 minutes. Run this on a new or changed Lean file first:

    python3 scripts/trust/precheck_names.py Checked/Trust/NecessityXY.lean

It prints every theorem/lemma of the file whose short name is a backticked token (or a suffix match of one)
in STATE.md or FINDINGS.md, and exits 1 if there is any. Not a CI check (StatementDeps is); a time saver.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def tokens():
    text = (ROOT / "STATE.md").read_text(encoding="utf-8") + "\n" + (ROOT / "FINDINGS.md").read_text(encoding="utf-8")
    parts = text.split("`")
    toks = set()
    for i, t in enumerate(parts):
        if i % 2 == 1 and t and " " not in t:
            m = re.fullmatch(r"([^\[\]]*)\[([^\[\]]*)\]([^\[\]]*)", t)
            toks |= {m.group(1) + m.group(3), m.group(1) + m.group(2) + m.group(3)} if m else {t}
    return toks


def main(paths):
    toks = tokens()
    bad = []
    for p in paths:
        src = Path(p).read_text(encoding="utf-8")
        for name in re.findall(r"^(?:theorem|lemma)\s+([^\s(:]+)", src, flags=re.M):
            short = name.split(".")[-1]
            hits = sorted(t for t in toks if t == short or t.endswith("." + short) or t == name)
            if hits:
                bad.append((p, name, hits))
    for p, name, hits in bad:
        print(f"{p}: `{name}` matches backticked {hits} in STATE.md/FINDINGS.md — rename it (StatementDeps would require a headline)")
    if not bad:
        print("precheck_names: ok")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
