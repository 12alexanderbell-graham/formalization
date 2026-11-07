
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

FULL = "Checked.Math.GelfandPDESolutions.gelfand_pde_radial_solutions"
LEAN = """import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Checked.Math.GelfandPDEExists

/-! Gelfand PDE, `GelfandPDESolutions`: radial classical solutions of the Gelfand problem in the unit ball of three-dimensional space, restated from `Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists` with the same hypothesis and the same conclusion. -/

namespace Checked.Math.GelfandPDESolutions
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, radial solutions: if 0 < λ ≤ 3.321992118,
there are two functions u, twice continuously differentiable on the open unit ball, continuous on the closed unit
ball, zero on the unit sphere and a function of ‖x‖ on the closed ball, with Δu + λ eᵘ = 0 on the open ball
(Δ is Mathlib's Laplacian). -/
theorem gelfand_pde_radial_solutions (lam : ℝ) (hpos : 0 < lam) (hle : lam ≤ 3.321992118) :
    ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
      ContDiffOn ℝ 2 u (ball 0 1) ∧
      ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :=
  Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists lam hpos hle

end Checked.Math.GelfandPDESolutions
"""
create("Checked/Math/GelfandPDESolutions.lean", LEAN)
append_line("Checked.lean", "import Checked.Math.GelfandPDESolutions", "GelfandPDESolutions")
append_line("scripts/trust/headlines.txt", FULL, "GelfandPDESolutions")
append_line("scripts/trust/literal_readings.txt",
            reading_line("Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists", FULL), "GelfandPDESolutions")
append_line("LEDGER.md",
    "- 2026-11-07, run 2026-11-07T1828Z — **New headline `Checked.Math.GelfandPDESolutions.gelfand_pde_radial_solutions` "
    "(Gelfand PDE, radial solutions; only Mathlib definitions in the statement).** Statement byte-identical to "
    "`gelfand_pde_radial_exists` (proof: that theorem); NV witness shared with it (same obligation). Literal readings: "
    "`gelfand_pde_radial_solutions` registered in `scripts/trust/literal_readings.txt` with the same readers as "
    "`gelfand_pde_radial_exists` (gelfandPdeSpace, gelfandPdeBall, gelfandPdeClosedBall, gelfandPdeRegular, "
    "gelfandPdeContinuous, gelfandPdeLamRange). Relock, TRUST_MAP, CLAIMS, packet: regenerated.",
    "gelfand_pde_radial_solutions")
