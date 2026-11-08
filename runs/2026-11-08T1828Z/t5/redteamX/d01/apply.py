#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(rel, old, new, count=1):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == count, (rel, old, t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")
def sub_any(rel, old, new):
    # best effort for the generated file: the author regenerates it with Claims.lean anyway
    p = root / rel
    t = p.read_text(encoding="utf-8")
    p.write_text(t.replace(old, new), encoding="utf-8")
def ledger(line):
    p = root / "LEDGER.md"
    t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"):
        t += "\n"
    p.write_text(t + line + "\n", encoding="utf-8")
OLD = "the redshift a({t₀})/a({t}) − 1, observed at time {t₀}, of light emitted at time {t} (scale factor {a})"
NEW = "the redshift a({t₀})/a({t}) − 1, observed at time {t}, of light emitted at time {t₀} (scale factor {a})"
sub("scripts/trust/phrases.txt", OLD, NEW)
sub_any("CLAIMS.md", "observed at time `t₀`, of light emitted at time `t` (scale factor `a`)",
        "observed at time `t`, of light emitted at time `t₀` (scale factor `a`)")
ledger("- 2026-11-08, run 2026-11-08T1828Z — phrase of `redshift` in `scripts/trust/phrases.txt` reworded (wording of the observation and emission times made explicit; formula unchanged); CLAIMS.md regenerated.")
