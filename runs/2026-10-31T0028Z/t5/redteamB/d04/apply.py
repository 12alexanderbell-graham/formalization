import sys, pathlib
root = pathlib.Path(sys.argv[1])
def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")
(root / "Checked/Cosmography/EdSDistance.lean").write_text('''import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Luminosity distance in Einstein-de Sitter (target 1, benchmark value)

Units `c = 1`. Einstein-de Sitter (flat, matter only, `a(t) = t^{2/3}`).
-/

namespace Checked.Cosmography.EdSDistance

/-- Einstein-de Sitter luminosity distance, closed form
`d_L(z) = (2/H₀) (1 + z) (1 - 1/√(1 + z))` (`c = 1`). -/
noncomputable def lumDistEdS (H₀ z : ℝ) : ℝ := 2 / H₀ * (1 - 1 / Real.sqrt (1 + z))

/-- Benchmark: in Einstein-de Sitter the luminosity distance at redshift `z = 3` is `c/H₀`. -/
theorem lumDistEdS_z3 : lumDistEdS 1 3 = 1 := by
  have h : Real.sqrt (1 + 3) = 2 := by
    rw [show (1 + 3 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  unfold lumDistEdS
  rw [h]
  norm_num

end Checked.Cosmography.EdSDistance
''', encoding="utf-8")
append("Checked.lean", "import Checked.Cosmography.EdSDistance\n")
append("scripts/trust/headlines.txt",
       "# Benchmarks\nChecked.Cosmography.EdSDistance.lumDistEdS_z3\n")
append("scripts/trust/def_kinds.txt",
       "Checked.Cosmography.EdSDistance.lumDistEdS FORMULA\n")
