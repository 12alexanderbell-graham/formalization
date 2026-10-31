import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rep(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")
rep("STATE.md", "36/38 PRINTED definitions have a machine-checked", "38/38 PRINTED definitions have a machine-checked")
rep("STATE.md",
    "Not yet read twice: `dQFlat` (Eq. 5), `jL` (= 1), and the printed parts inside the F1/F2 CLAIM definitions.",
    "Third batch: `dQFlat` (Eq. 5), `jL` (= 1) and the printed parts inside the F1/F2 CLAIM definitions are read twice and agree; every printed coefficient behind a finding now has an independent machine-checked second reading.")
rep("STATE.md", "second reading 36/38", "second reading 38/38")
rep("TRUST_MAP.md", "38 PRINTED definitions; 36 carry", "38 PRINTED definitions; 38 carry")
