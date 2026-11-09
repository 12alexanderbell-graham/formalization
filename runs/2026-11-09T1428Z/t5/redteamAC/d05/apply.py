import sys, os
root = sys.argv[1]
def sub(path, old, new):
    p = os.path.join(root, path)
    s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (path, old, s.count(old))
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
# article and verb are the author's choice (PRED of gen_phrases.py): "a" -> "the" for the three initial value problems
sub("scripts/trust/phrases.txt",
    "the position as function of time {x} is a Duffing oscillator initial value problem solution",
    "the position as function of time {x} is the Duffing oscillator initial value problem solution")
sub("scripts/trust/phrases.txt",
    "are a Michaelis Menten mass action initial value problem solution",
    "are the Michaelis Menten mass action initial value problem solution")
sub("scripts/trust/phrases.txt",
    "are a Robertson chemical kinetics initial value problem solution",
    "are the Robertson chemical kinetics initial value problem solution")
with open(os.path.join(root, "LEDGER.md"), "a", encoding="utf-8") as f:
    f.write("\n- 2026-11-09, run 2026-11-09T1428Z: phrases of `IsDuffingSolution`, `IsMMSolution` and `IsRobSolution` reworded (article before the name; PRED in gen_phrases.py).\n")
