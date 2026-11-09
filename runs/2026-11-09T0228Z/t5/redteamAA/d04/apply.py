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
sub("scripts/trust/phrases.txt", "has sign of curvature constant, minus the curvature density parameter)", "has sign of curvature constant and is the curvature density parameter)")
dropline("scripts/trust/phrase_roles.txt", "SIGN | Checked.Cosmography.BambaZ.curvK | has sign of curvature constant, minus the curvature density parameter")
ledger("## 2026-11-09 · phrase wording · curvK\n- `curvK`: the phrase states the identification with the curvature density parameter in one clause; the matching SIGN line is dropped from `scripts/trust/phrase_roles.txt` (registry shrinks; no line added).")
