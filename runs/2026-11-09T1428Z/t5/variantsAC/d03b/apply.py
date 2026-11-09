# Judge's variant of AC d03 (not blind): the registry keeps the reader's order; the phrase moves the "divided by" text
# to the other clause by hand (P11 alone must catch it).
import os, sys
root = sys.argv[1]
def sub(path, old, new):
    p = os.path.join(root, path); s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (path, old); open(p, "w", encoding="utf-8").write(s.replace(old, new))
sub("scripts/trust/phrases.txt",
    "({n}-th time derivative of the scale factor over the scale factor divided by the {n}-th power of the Hubble rate; orders 0 and 1 coefficients are one;",
    "({n}-th time derivative of the scale factor over the scale factor; orders 0 and 1 coefficients are one divided by the {n}-th power of the Hubble rate;")
open(os.path.join(root, "LEDGER.md"), "a", encoding="utf-8").write("\n- cosmoCoeff: phrase reworded.\n")
