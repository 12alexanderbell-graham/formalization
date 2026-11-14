import sys, pathlib
ROOT = pathlib.Path(sys.argv[1])
p = ROOT / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
old = "| C4 | Capozziello, Lazkoz, Salzano 2011 | — | → **F2** |\n"
new = old + ("| C32 | Bamba, Capozziello, Nojiri, Odintsov 2012 (arXiv:1205.3421), Eq. (11.46), the second-order η coefficients | "
             "Printed second-order coefficients of the F(R) series are wrong at every matter density Ω (Lean-checked in the same finding: "
             "the printed (11.42)–(11.45) fail at Ω = 0.041 and Ω = 0.25, and the printed denominator vanishes only at Ω ≈ 0.176) | "
             "=> **F10** (run 2028Z) |\n")
assert t.count(old) == 1
p.write_text(t.replace(old, new), encoding="utf-8")
