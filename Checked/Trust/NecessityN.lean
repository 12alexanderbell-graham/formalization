import Checked.Trust.NonVacuity
import Checked.Trust.NecessityE
import Checked.Records.FalknerSkan

/-! Hypothesis necessity for the record `Checked.Records.F12_separation` (run 2026-11-12T1028Z). Its hypotheses
are those of `Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed`, copied verbatim, so the three
witness profiles of `Checked/Trust/NecessityE.lean` serve again: each meets every other hypothesis at
β = −0.1988376, and that β does not round to −0.1988377 at seven decimals (it is 10⁻⁷ away). -/

namespace Checked.Trust.NCP

open Set Filter Topology

theorem not_rounds_printed : ¬ Checked.Records.RoundsTo (-(1988376 / 10000000)) (-0.1988377) 7 := by
  unfold Checked.Records.RoundsTo; rw [abs_le]; norm_num

/-- `f' = p` is needed in `F12_separation`: the profile of `fs_separation_below_printed_h1`. -/
theorem F12_separation_h1 : necessity% Checked.Records.F12_separation 1 := by
  refine ⟨-(1988376 / 10000000), prG, prP, prQ, fun η _ => (prP_deriv η).hasDerivWithinAt,
    fun η hη => by rw [← prG_ode η hη]; exact (prQ_deriv η).hasDerivWithinAt, by simp [prG],
    prP_zero, prQ_zero, prP_lim, prQ_pos, pr_decay, not_rounds_printed⟩

/-- `p' = q` is needed in `F12_separation`: the profile of `fs_separation_below_printed_h2`. -/
theorem F12_separation_h2 : necessity% Checked.Records.F12_separation 2 := by
  refine ⟨-(1988376 / 10000000), f2, p2, q2, fun η _ => (f2_deriv η).hasDerivWithinAt,
    fun η _ => (q2_deriv η).hasDerivWithinAt, by simp [f2], by simp [p2], by simp [q2, G2],
    p2_lim, q2_pos, p2_decay, not_rounds_printed⟩

/-- The Falkner–Skan equation is needed in `F12_separation`: the profile of `fs_separation_below_printed_h3`. -/
theorem F12_separation_h3 : necessity% Checked.Records.F12_separation 3 := by
  refine ⟨-(1988376 / 10000000), prF, prP, prQ, fun η _ => (prF_deriv η).hasDerivWithinAt,
    fun η _ => (prP_deriv η).hasDerivWithinAt, by simp [prF],
    prP_zero, prQ_zero, prP_lim, prQ_pos, pr_decay, not_rounds_printed⟩

end Checked.Trust.NCP
