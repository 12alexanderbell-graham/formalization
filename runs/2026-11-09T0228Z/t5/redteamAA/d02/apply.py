import sys, pathlib
def root(): return pathlib.Path(sys.argv[1])
def sub(path, old, new):
    p = root() / path
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (path, old[:60], t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")
def ledger(line):
    p = root() / "LEDGER.md"
    t = p.read_text(encoding="utf-8")
    p.write_text(t.rstrip("\n") + "\n\n" + line + "\n", encoding="utf-8")
def dropline(path, line):
    p = root() / path
    t = p.read_text(encoding="utf-8").split("\n")
    assert t.count(line) == 1, line
    t.remove(line)
    p.write_text("\n".join(t), encoding="utf-8")
old = ("B and C turn into A and C with rate constant of the second reaction {k₂}, and two B turn into B and C with rate constant of the third reaction {k₃}")
new = ("two B turn into B and C with rate constant of the second reaction {k₂}, and B and C turn into A and C with rate constant of the third reaction {k₃}")
sub("scripts/trust/phrases.txt", old, new)
ledger("## 2026-11-09 · phrase wording · IsRobSolution\n- `IsRobSolution`: the reactions of the network are listed in the order of the reaction numbering (wording only; roles, names, species unchanged).")
