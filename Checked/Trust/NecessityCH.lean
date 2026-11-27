import Checked.Trust.NonVacuity
import Checked.FalknerSkan.Limit

/-! Hypothesis necessity for `Checked.FalknerSkan.Limit.fs_monotone_of_limit` (run 2026-11-27T1228Z): the limit of
the velocity at infinity is NEEDED (hypothesis 8). The witness is the exact polynomial solution at pressure-gradient
coefficient two thirds: the stream function is minus the cube of the height over nine, so the velocity is minus the
square of the height over three and the shear is minus two thirds of the height. It meets the third-order system on
the whole half-line with zero stream function, zero velocity and zero shear at the wall, but its velocity tends to
minus infinity, and its shear is zero at the wall and negative above it. The solution was seen in the scan of run
2026-11-27T0028Z (`runs/2026-11-27T0028Z/scripts/scan_h8_sep.py`) as the boundary between the velocities that run off
downward and upward. Module `NecessityCH`. -/

namespace Checked.Trust.NecessityCH
open Set Filter Topology

/-- The stream function of the exact solution: minus the cube of the height over nine. -/
noncomputable def chF : ℝ → ℝ := fun η => -(η ^ 3 / 9)
/-- Its velocity: minus the square of the height over three. -/
noncomputable def chP : ℝ → ℝ := fun η => -(η ^ 2 / 3)
/-- Its shear: minus two thirds of the height. -/
noncomputable def chQ : ℝ → ℝ := fun η => -(2 * η / 3)

lemma chF_hd (η : ℝ) : HasDerivAt chF (chP η) η :=
  (((hasDerivAt_pow 3 η).div_const 9).neg).congr_deriv (by simp only [chP]; push_cast; ring)

lemma chP_hd (η : ℝ) : HasDerivAt chP (chQ η) η :=
  (((hasDerivAt_pow 2 η).div_const 3).neg).congr_deriv (by simp only [chQ]; push_cast; ring)

lemma chQ_hd (η : ℝ) : HasDerivAt chQ (-(chF η * chQ η) - 2 / 3 * (1 - chP η ^ 2)) η :=
  ((((hasDerivAt_id' η).const_mul (2 : ℝ)).div_const 3).neg).congr_deriv
    (by simp only [chF, chQ, chP]; ring)

/-- The limit of the velocity at infinity is needed in `fs_monotone_of_limit`: the exact solution with stream
function minus the cube of the height over nine at coefficient two thirds. -/
theorem fs_monotone_of_limit_h8 : necessity% Checked.FalknerSkan.Limit.fs_monotone_of_limit 8 := by
  refine ⟨2 / 3, by norm_num, by norm_num, chF, chP, chQ, fun η _ => (chF_hd η).hasDerivWithinAt,
    fun η _ => (chP_hd η).hasDerivWithinAt, fun η _ => (chQ_hd η).hasDerivWithinAt,
    by simp [chF], by simp [chP], ?_⟩
  exact ⟨0, mem_Ici.2 le_rfl, by simp [chQ]⟩

end Checked.Trust.NecessityCH
