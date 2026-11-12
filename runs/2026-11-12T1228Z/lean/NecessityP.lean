import Checked.Trust.NonVacuity
import Checked.Data.FR13

/-!
# Hypothesis necessity for the Farooq–Ratra 2013 deceleration–acceleration redshift claims (run 2026-11-12T1228Z)

`Checked.Data.FR13.fr13_zda68` and `fr13_zda738` say: at every minimiser Ω over [0, 1] of the
marginalised chi-square (prior 68 ± 2.8 or 73.8 ± 2.4), every redshift z > −1 with
Ω (1 + z)³ = 2 (1 − Ω) lies in the stated window. Here:

* the minimiser condition is needed: Ω = 1/5 and z = 1 satisfy Ω (1 + z)³ = 2 (1 − Ω);
* the transition equation is needed: z = 0 at the certified minimiser;
* z > −1 is redundant: the minimiser lies strictly between 0 and 1, so the right side is positive
  and (1 + z)³ > 0 forces 1 + z > 0.
-/

namespace Checked.Trust.NecessityP
open Checked.Data.FR13

theorem fr13_zda68_h3 : necessity% Checked.Data.FR13.fr13_zda68 3 :=
  ⟨1 / 5, by norm_num, by norm_num, 1, by norm_num, by norm_num, by norm_num⟩

theorem fr13_zda738_h3 : necessity% Checked.Data.FR13.fr13_zda738 3 :=
  ⟨1 / 5, by norm_num, by norm_num, 1, by norm_num, by norm_num, by norm_num⟩

theorem fr13_zda68_h5 : necessity% Checked.Data.FR13.fr13_zda68 5 := by
  obtain ⟨Ω, hΩ, h⟩ := fr13_exists68
  exact ⟨Ω, hΩ.1, hΩ.2, h, 0, by norm_num, by norm_num⟩

theorem fr13_zda738_h5 : necessity% Checked.Data.FR13.fr13_zda738 5 := by
  obtain ⟨Ω, hΩ, h⟩ := fr13_exists738
  exact ⟨Ω, hΩ.1, hΩ.2, h, 0, by norm_num, by norm_num⟩

/-- A positive cube forces a positive base. -/
theorem gt_neg_one_of_cube {Ω z : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hda : Ω * (1 + z) ^ 3 = 2 * (1 - Ω)) :
    -1 < z := by
  by_contra h
  have hz : 1 + z ≤ 0 := by linarith [not_lt.1 h]
  have hc : (1 + z) ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) hz
  nlinarith [mul_nonpos_of_nonneg_of_nonpos h0.le hc]

theorem fr13_zda68_r4 : dropped% Checked.Data.FR13.fr13_zda68 4 := by
  intro Ω h0 h1 hmin z hda
  obtain ⟨a, b⟩ := bestfit68_aux Ω h0 h1 hmin
  exact fr13_zda68 Ω h0 h1 hmin z (gt_neg_one_of_cube (by linarith) (by linarith) hda) hda

theorem fr13_zda738_r4 : dropped% Checked.Data.FR13.fr13_zda738 4 := by
  intro Ω h0 h1 hmin z hda
  obtain ⟨a, b⟩ := bestfit738_aux Ω h0 h1 hmin
  exact fr13_zda738 Ω h0 h1 hmin z (gt_neg_one_of_cube (by linarith) (by linarith) hda) hda

end Checked.Trust.NecessityP
