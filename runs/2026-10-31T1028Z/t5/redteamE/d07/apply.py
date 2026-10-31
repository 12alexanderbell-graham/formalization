import sys, pathlib

root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:60], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")


def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")


LEAN = '''import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Einstein–de Sitter benchmark (target 1, benchmark value)

Units `c = 1`. Einstein–de Sitter: flat, matter only, `a(t) = t^{2/3}`; closed form in `z`.
-/

namespace Checked.Cosmography.EdSBenchmark

/-- Closed-form distance of an Einstein–de Sitter source at redshift `z` for the Hubble constant
`H₀`, as a local abbreviation. -/
local notation "edsFluxDist" H₀:max z:max => 2 / H₀ * (1 - 1 / Real.sqrt (1 + z))

/-- **Benchmark.** In an Einstein–de Sitter universe the bolometric (flux) distance to a source at
`z = 3` is exactly `c/H₀` (units `c = 1`, `H₀ = 1`). -/
theorem flux_distance_EdS_z3 : edsFluxDist 1 3 = 1 := by
  have h : Real.sqrt (1 + 3) = 2 := by
    rw [show (1 + 3 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h]
  norm_num

end Checked.Cosmography.EdSBenchmark
'''
create("Checked/Cosmography/EdSBenchmark.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.EdSBenchmark\n")
sub("scripts/trust/headlines.txt", "# B1 (run 2026-10-31T0428Z)",
    "# Benchmarks\nEdSBenchmark.flux_distance_EdS_z3\n# B1 (run 2026-10-31T0428Z)")
