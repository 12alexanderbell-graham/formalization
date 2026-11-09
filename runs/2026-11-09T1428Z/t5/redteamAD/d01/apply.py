#!/usr/bin/env python3
"""d01: a reader file cited twice.  P11b orders the lines of each reader FILE (idx never decreases) but not the BLOCKS;
the generator drops a repeated line (dedupe) and then glues a 'divided by ...' line to whatever text was shown last.
Pure re-arrangement of the registry: no reader line added or removed, no new reader file."""
import sys, importlib.util
from pathlib import Path
def regen(root):
    p = Path(root)/"scripts/trust/check_claims.py"
    sys.path.insert(0, str(p.parent))
    spec = importlib.util.spec_from_file_location("cc_regen", p)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    sys.path.pop(0)
    assert m.write_generated() == 0      # = python3 scripts/trust/check_claims.py --generate (P11 rewrite)
def sub1(path, old, new):
    t = Path(path).read_text(encoding="utf-8")
    assert t.count(old) == 1, (str(path), old[:70], t.count(old))
    Path(path).write_text(t.replace(old, new), encoding="utf-8")
def ledger(root, line):
    p = Path(root)/"LEDGER.md"
    t = p.read_text(encoding="utf-8")
    p.write_text(t + ("" if t.endswith("\n") else "\n") + line + "\n", encoding="utf-8")


root = Path(sys.argv[1])
reg = root/"scripts/trust/phrase_roles.txt"
CL = "runs/2026-11-09T0228Z/clauses/CLAUSES.txt"
SY = "runs/2026-11-09T0228Z/symbols/SYMBOLS.txt"
c = "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | "
A = c + "n-th time derivative of the scale factor over the scale factor\n"
B = c + "divided by the n-th power of the Hubble rate\n"
o2 = c + "The order 2 coefficient is minus the deceleration parameter usually written q\n"
o3 = c + "The order 3 coefficient is the jerk parameter usually written j\n"
# CLAUSES block closes after A; SYMBOLS gives its order-2 line; CLAUSES is cited again, starting with A (repeated), B, ...
sub1(reg, A + B, A + f"# source: {SY}\n" + o2 + f"# source: {CL}\n" + A + B)
# the original SYMBOLS block now starts at order 3
sub1(reg, f"# source: {SY}\n" + o2 + o3, f"# source: {SY}\n" + o3)
regen(root)
ledger(root, "- 2026-11-09, run 2026-11-09T1428Z — **Aviles.cosmoCoeff phrase regenerated** after the registry cited the clause and symbol readings in an interleaved order (no reader line added or removed); phrase rewritten by `check_claims.py --generate`.")
