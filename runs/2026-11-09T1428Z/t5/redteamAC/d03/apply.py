import sys, os
root = sys.argv[1]
def sub(path, old, new):
    p = os.path.join(root, path)
    s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (path, old, s.count(old))
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
R = "scripts/trust/phrase_roles.txt"
P = "scripts/trust/phrases.txt"
c = "CLAUSE | Checked.Cosmography.Aviles.cosmoCoeff | "
div, one = c + "divided by the n-th power of the Hubble rate\n", c + "orders 0 and 1 coefficients are one\n"
# registry move: no line is added or removed, only the ORDER of two lines of the CLAUSES block changes
# (the generator glues a clause that starts "divided by" to the clause shown before it)
sub(R, div + one, one + div)
# the phrase exactly as runs/2026-11-09T0228Z/scripts/gen_phrases.py prints it from the reordered registry
sub(P,
    "({n}-th time derivative of the scale factor over the scale factor divided by the {n}-th power of the Hubble rate; orders 0 and 1 coefficients are one;",
    "({n}-th time derivative of the scale factor over the scale factor; orders 0 and 1 coefficients are one divided by the {n}-th power of the Hubble rate;")
with open(os.path.join(root, "LEDGER.md"), "a", encoding="utf-8") as f:
    f.write("\n- 2026-11-09, run 2026-11-09T1428Z: phrase of `cosmoCoeff` regenerated from the blind registry (clause order of the CLAUSES block of `phrase_roles.txt`; no reader line added, removed or changed).\n")
