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
sub("scripts/trust/phrases.txt", "the metric F(R) gravity Friedmann equation with dust (the expansion-rate equation", "the metric F(R) gravity Friedmann equation (the expansion-rate equation")
dropline("scripts/trust/phrase_roles.txt", "NAME | Checked.Cosmography.FRCosmo.FriedmannEq | metric F(R) gravity Friedmann equation with dust")
ledger("## 2026-11-09 · phrase wording · FriedmannEq\n- `FriedmannEq`: the phrase names the equation without the matter content already carried by the density it contains; the NAME line of its name reading is dropped from `scripts/trust/phrase_roles.txt` (registry shrinks; no line added).")
