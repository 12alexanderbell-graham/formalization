import sys, os
root = sys.argv[1]
def sub(path, old, new):
    p = os.path.join(root, path)
    s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (path, old, s.count(old))
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
# P7/P9 require the NAME, SIGN and CLAUSE texts, never a ROLE: the roles (and so the arguments) of w0 and wa are simply not mentioned
sub("scripts/trust/phrases.txt",
    "with the present matter density parameter {Ω}, the present dark energy equation of state {w₀}, the equation of state evolution parameter {wₐ} and the observation time {t₀} (spatially flat universe with dust and separately conserved dark energy;",
    "with the present matter density parameter {Ω} and the observation time {t₀} (spatially flat universe with dust and separately conserved dark energy;")
with open(os.path.join(root, "LEDGER.md"), "a", encoding="utf-8") as f:
    f.write("\n- 2026-11-09, run 2026-11-09T1428Z: phrase of `IsFlatCPL` shortened (the argument list now names only the arguments the clause texts speak of; wording of the blind texts unchanged).\n")
