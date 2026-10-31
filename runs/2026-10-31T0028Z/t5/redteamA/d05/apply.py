import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
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

LEAN = '''import Checked.Cosmography.DemianskiZ

/-!
# The corrected Demianski et al. `d_L(z)` series (addendum to F11)

With the corrected `D⁴_L` (`+105 q₀⁴`), the flat `d_L(z)` series has an `o(z⁵)` remainder.
-/

namespace Checked.Cosmography.DemianskiZ

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaZ

/-- **The corrected series holds.** Flat `d_L(z)` with the corrected `D⁴_L = correctDL4z _ _ _ _ 0`:
the remainder is `o(z⁵)` (companion of `demDL4_fails_past`, which refutes the printed `D⁴_L`). -/
theorem demDL4_corrected_series :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), ContDiffAt ℝ 5 a t₀ ∧ a t₀ ≠ 0 ∧ hubble a t₀ ≠ 0 ∧
      (fun t => remLz correctDL4z 0 a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) :=
  ⟨Real.exp, 0, Real.contDiff_exp.contDiffAt, (Real.exp_pos 0).ne',
    by rw [BambaY.deSitter_vals.1]; norm_num,
    lumDist_z_fifth_order 0 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
      (by rw [BambaY.deSitter_vals.1]; norm_num)⟩

end Checked.Cosmography.DemianskiZ
'''
create("Checked/Cosmography/DemianskiCorrected.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.DemianskiCorrected\n")
append("scripts/trust/headlines.txt", "# F11 addendum\nDemianskiZ.demDL4_corrected_series\n")
sub("STATE.md", "- **Findings F1–F11** (FINDINGS.md)",
    "- **PROVED** (F11 addendum) `Checked.Cosmography.DemianskiZ.demDL4_corrected_series`: the corrected flat d_L(z) series (D⁴_L with +105q₀⁴) holds with an o(z⁵) remainder (cf. `lumDist_z_fifth_order`, which is the general statement): run 2026-10-31.\n- **Findings F1–F11** (FINDINGS.md)")
