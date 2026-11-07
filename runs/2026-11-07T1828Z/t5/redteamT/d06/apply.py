
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def append_line(rel, line, must_not_contain=None):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if must_not_contain is not None:
        assert must_not_contain not in s
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + line + "\n", encoding="utf-8")

def create(rel, text):
    p = root / rel
    assert not p.exists()
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")

def reading_line(src_headline_suffix, new_full):
    s = (root / "scripts/trust/literal_readings.txt").read_text(encoding="utf-8")
    ls = [l for l in s.splitlines() if l.startswith(src_headline_suffix + " ")]
    assert len(ls) == 1
    return new_full + ls[0][len(src_headline_suffix):]

FULL = "Checked.Math.GelfandPDEThreshold.gelfand_pde_radial_solvability_threshold"
LEAN = """import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Checked.Math.GelfandPDE

/-! Gelfand PDE, `GelfandPDEThreshold`: the bound on the parameter of radial classical solutions of the Gelfand problem in the unit ball of three-dimensional space, restated from `Checked.Math.GelfandPDE.gelfand_pde_radial_bound` with the same hypotheses and the same conclusion. -/

namespace Checked.Math.GelfandPDEThreshold
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, radial solutions: if u is twice
continuously differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere
and a function of ‖x‖ on the closed ball, and Δu + λ eᵘ = 0 on the open ball (Δ is Mathlib's Laplacian),
then λ ≤ 3.321992119. -/
theorem gelfand_pde_radial_solvability_threshold (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 3.321992119 :=
  Checked.Math.GelfandPDE.gelfand_pde_radial_bound lam u hu hc hb hrad hpde

end Checked.Math.GelfandPDEThreshold
"""
create("Checked/Math/GelfandPDEThreshold.lean", LEAN)
append_line("Checked.lean", "import Checked.Math.GelfandPDEThreshold", "GelfandPDEThreshold")
append_line("scripts/trust/headlines.txt", FULL, "GelfandPDEThreshold")
append_line("scripts/trust/literal_readings.txt",
            reading_line("Checked.Math.GelfandPDE.gelfand_pde_radial_bound", FULL), "GelfandPDEThreshold")
append_line("LEDGER.md",
    "- 2026-11-07, run 2026-11-07T1828Z — **New headline `Checked.Math.GelfandPDEThreshold.gelfand_pde_radial_solvability_threshold` "
    "(Gelfand PDE, bound on the parameter of radial solutions; only Mathlib definitions in the statement).** Statement "
    "byte-identical to `gelfand_pde_radial_bound` (proof: that theorem); NV witness shared with it (same obligation). "
    "Literal readings: `gelfand_pde_radial_solvability_threshold` registered in `scripts/trust/literal_readings.txt` "
    "with the same readers as `gelfand_pde_radial_bound` (gelfandPdeSpace, gelfandPdeBall, gelfandPdeClosedBall, "
    "gelfandPdeRegular, gelfandPdeContinuous). Relock, TRUST_MAP, CLAIMS, packet: regenerated.",
    "gelfand_pde_radial_solvability_threshold")
