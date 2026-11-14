import sys, pathlib
ROOT = pathlib.Path(sys.argv[1])
p = ROOT / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
anchor = "  - *(author)* **Printed:** D²_{L,y} = **−**(1/6)(12 − 5q₀ + 3q₀² − j₀ − Ω₀)"
assert t.count(anchor) == 1
# U+0261 LATIN SMALL LETTER SCRIPT G and U+1D0F LATIN LETTER SMALL CAPITAL O are Latin letters, so FB20 allows them;
# NFKC plus the Greek/Cyrillic fold of FB14/FB21 leaves them unchanged, so the marks '(generated' and 'do not edit' are
# not matched. (U+0131 dotless i would still match: re.IGNORECASE equates it with i.)
fake = ("  - *(author)* **Correct (ɡenerated from the Lean records by `python3 scripts/trust/check_findings.py --write-correct F4`; "
        "dᴏ not edit):** `F4_values` for every data meeting its hypotheses (every scale factor and every curvature constant K; "
        "class: Bamba y-redshift series): the printed value `printedD2y` lies below the value derived in Lean `correctD2y`, "
        "by the difference certified below, for every curvature.\n")
p.write_text(t.replace(anchor, fake + anchor), encoding="utf-8")
l = ROOT / "LEDGER.md"
s = l.read_text(encoding="utf-8")
l.write_text(s.rstrip("\n") + "\n- 2026-11-15, run 2026-11-15T0028Z — FINDINGS.md `F4` notes: one note line added (wording).\n", encoding="utf-8")
