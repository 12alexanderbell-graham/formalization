import sys
from pathlib import Path
def edit(root, reps, ledger, reg=None):
    root = Path(root)
    p = root/"scripts/trust/phrases.txt"
    s = p.read_text(encoding="utf-8")
    for a, b in reps:
        assert s.count(a) == 1, a
        s = s.replace(a, b)
    p.write_text(s, encoding="utf-8")
    l = root/"LEDGER.md"
    l.write_text((l.read_text(encoding="utf-8") if l.exists() else "") + "\n" + ledger + "\n", encoding="utf-8")
    if reg:
        r = root/"scripts/trust/phrase_roles.txt"
        t = r.read_text(encoding="utf-8")
        for after, line in reg:
            assert after in t
            t = t.replace(after, after + "\n" + line, 1)
        r.write_text(t, encoding="utf-8")
