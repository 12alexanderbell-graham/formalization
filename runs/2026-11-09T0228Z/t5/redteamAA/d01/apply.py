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
sub("scripts/trust/phrases.txt", "Ω_k is one minus Ω₀)", "Ωₘ is one minus Ω₀)")
ledger("## 2026-11-09 · phrase wording · omega0\n- `omega0`: the closing relation of its phrase now names the matter density parameter Ωₘ (wording only; sign convention, name and roles unchanged).")
