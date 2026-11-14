import sys, pathlib
ROOT = pathlib.Path(sys.argv[1])
p = ROOT / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
old = "| C2 | Aviles et al. 2012 | — | → **F1** |"
new = ("| C2 | Aviles et al. 2012 (arXiv:1204.2007), Eq. (15) and the numbers of its Table V | The paper's own l₀ and m₀ "
       "values were evaluated with the printed formulas and are wrong: at Ω_m = 0.3 the printed l₀ gives 0.685[✓F1_printedL0(printedAvilesL0, Ω=0.3, printed)] "
       "where every flat ΛCDM model has 3.115[✓F1_l0(cosmoCoeff, derived)] (certified, F1) | → **F1** |")
assert t.count(old) == 1
p.write_text(t.replace(old, new), encoding="utf-8")
