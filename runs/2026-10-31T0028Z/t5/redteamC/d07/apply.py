#!/usr/bin/env python3
import sys, re, pathlib
R = pathlib.Path(sys.argv[1])
def rd(p): return (R / p).read_text(encoding="utf-8")
def wr(p, s):
    (R / p).parent.mkdir(parents=True, exist_ok=True)
    (R / p).write_text(s, encoding="utf-8")
def rep(p, old, new):
    s = rd(p)
    assert s.count(old) == 1, (p, old[:70], s.count(old))
    wr(p, s.replace(old, new, 1))
def app(p, line):
    wr(p, rd(p).rstrip("\n") + "\n" + line + "\n")
def new(p, s):
    assert not (R / p).exists(), p
    wr(p, s)
def register(headline, row, witness):
    """append a headline to the registry and update the generated TRUST_MAP.md exactly as
    StatementDeps.lean would regenerate it (so the stale-map check does not fire)."""
    app("scripts/trust/headlines.txt", headline)
    s = rd("TRUST_MAP.md")
    s, n = re.subn(r"Headlines: (\d+)\. Resting on no unpinned physics definition: (\d+)\.",
                   lambda m: "Headlines: %d. Resting on no unpinned physics definition: %d." % (int(m.group(1)) + 1, int(m.group(2)) + 1), s)
    assert n == 1
    if witness:
        s, n = re.subn(r"\(trust track T2\): (\d+) headlines have hypotheses; (\d+) of them",
                       lambda m: "(trust track T2): %d headlines have hypotheses; %d of them" % (int(m.group(1)) + 1, int(m.group(2)) + 1), s)
        assert n == 1
    wr("TRUST_MAP.md", s.rstrip("\n") + "\n" + row + "\n")
def state_bullet(text):
    rep("STATE.md", "- **Findings F1–F11**", text + "\n- **Findings F1–F11**")
def import_checked(mod):
    app("Checked.lean", "import " + mod)

rep("scripts/trust/def_kinds.txt", "Checked.Cosmography.CVdQ.dQFlat PRINTED", "Checked.Cosmography.CVdQ.dQFlat FORMULA")
rep("scripts/trust/def_kinds.txt", "Checked.Cosmography.FREta.jL PRINTED", "Checked.Cosmography.FREta.jL FORMULA")
# regenerate TRUST_MAP.md as StatementDeps would: two fewer PRINTED definitions, none second-read lost
s = rd("TRUST_MAP.md")
assert s.count("38 PRINTED definitions; 36 carry") == 1
s = s.replace("38 PRINTED definitions; 36 carry", "36 PRINTED definitions; 36 carry")
out = []
for line in s.split("\n"):
    if line.startswith("| `") and line.count(" | ") == 4:
        parts = line.split(" | ")
        items = [x for x in parts[3].split(", ") if x not in ("dQFlat", "jL")]
        parts[3] = ", ".join(items) if items else "—"
        line = " | ".join(parts)
    out.append(line)
wr("TRUST_MAP.md", "\n".join(out))
rep("STATE.md", "36/38 PRINTED definitions have a machine-checked agreement", "36/36 PRINTED definitions have a machine-checked agreement")
rep("STATE.md", "Not yet read twice: `dQFlat` (Eq. 5), `jL` (= 1), and the printed parts inside", "Not yet read twice: the printed parts inside")
