import sys, os
root = sys.argv[1]
def sub(path, old, new):
    p = os.path.join(root, path)
    s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (path, old, s.count(old))
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
# P7 compares NFKC-lowercased tokens (capital Omega == small omega) and P4/P6 compare WORD matches, which drop Greek letters and digits
sub("scripts/trust/phrases.txt",
    "BambaK.omega0 | the present total density parameter Ω0 with",
    "BambaK.omega0 | the present total density parameter ω0 with")
with open(os.path.join(root, "LEDGER.md"), "a", encoding="utf-8") as f:
    f.write("\n- 2026-11-09, run 2026-11-09T1428Z: phrase of `omega0` reworded (symbol of the name).\n")
