import sys, os
def edit(root, rel, old, new):
    p = os.path.join(root, rel)
    s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
def ledger(root, line):
    p = os.path.join(root, "LEDGER.md")
    s = open(p, encoding="utf-8").read()
    if not s.endswith("\n"): s += "\n"
    open(p, "w", encoding="utf-8").write(s + line + "\n")

root=sys.argv[1]
edit(root,'FINDINGS.md','the window of `fs_neg_wall_shear_window` also excludes the four other printed values. One printed value is its correct rounding: Guo, Zhuang, Meng & Rabczuk, arXiv:2010.05682v1, Table 8 (p. 33; typeset, crop `runs/2026-11-11T1028Z/typeset/guo2020_p33_table8.png`; the same table lists the older values without comment).','the window of `fs_neg_wall_shear_window` also excludes the four other printed values and the value of Guo, Zhuang, Meng & Rabczuk, arXiv:2010.05682v1, Table 8 (p. 33; typeset, crop `runs/2026-11-11T1028Z/typeset/guo2020_p33_table8.png`; the same table lists the older values without comment).')
ledger(root,'- 2026-11-13 run 1028Z: `FINDINGS.md` `F13` Correct line reworded for clarity.')
