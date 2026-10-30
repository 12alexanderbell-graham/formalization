import Checked.Fidelity.LumDistSpec
import Work.Fidelity.RedTeamLumDist

/-!
# Blind mutation benchmark for `LumDistSpec` (trust track T1)

`RedTeamLumDist.lean` was written by a red-team subagent that saw only the definition of
`lumDist` and was told not to read the specification. Its brief: twelve plausible, wrong
definitions, as hard to catch as possible (agree in flat space, at `a₀ = 1`, at `|K| = 1`,
to fifth order in χ, or except at junk values of Lean). Here each one is refuted against
`LumDistSpec` in Lean. Result: 12/12 rejected. Together with the author's own mutants
(`LumDistSpec.lean`, 10/10) the kill rate is 22/22, of which the blind part is the
unbiased number.
-/

namespace Work.Fidelity

open Checked.Fidelity

open Real Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.Transverse
open Checked.Cosmography.BambaK Work.Fidelity.RedTeam

/-- Rescaled static closed universe (`a ≡ 2`, `K = 4`): the specification forces
`d_L = sin π = 0` at `t₀ = π`, `t = 0`. -/
lemma rescaled_static_at (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec D) :
    D 4 (fun _ => 2) π 0 = 0 := by
  have := h.rescale 2 two_pos 1 (fun _ => 1) π 0
  norm_num at this
  rw [this, h.staticClosed π 0 pi_pos.le]; simp

lemma com_const2 : comoving (fun _ => 2) π 0 = π / 2 := by
  unfold comoving; simp; ring

lemma red_const2 : redshift (fun _ => (2 : ℝ)) π 0 = 0 := by
  simp [redshift]

lemma sinh_two_log2 : Real.sinh (2 * Real.log 2) = 15 / 8 := by
  rw [show 2 * Real.log 2 = Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num, sinh_log 4 (by norm_num)]
  norm_num

lemma sqrt_four : Real.sqrt (-(-4 : ℝ)) = 2 := by
  rw [neg_neg, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem reject_rt1 : ¬ LumDistSpec rt1 := fun h => by
  have := rescaled_milne_at _ h
  simp only [rt1, transverse, com_2id_half, red_2id_half, sqrt_four] at this
  norm_num at this
  rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring, sinh_log2] at this
  norm_num at this

lemma com_2s_half : comoving (fun s => 2 * s) 1 (1 / 2) = Real.log 2 / 2 := com_2id_half
lemma red_2s_half : redshift (fun s => 2 * s) 1 (1 / 2) = 1 := red_2id_half

theorem reject_rt2 : ¬ LumDistSpec rt2 := fun h => by
  have := rescaled_milne_at _ h
  simp only [rt2, transverse, id, com_2s_half, red_2s_half, sqrt_four] at this
  norm_num at this
  rw [show 2 * (2 * (Real.log 2 / 2)) = 2 * Real.log 2 by ring, sinh_two_log2] at this
  norm_num at this

theorem reject_rt3 : ¬ LumDistSpec rt3 := fun h => by
  have := rescaled_static_at _ h
  simp only [rt3, com_const2, red_const2, Real.sin_pi_div_two] at this
  norm_num at this

theorem reject_rt4 : ¬ LumDistSpec rt4 := fun h => by
  have := milne_at _ h
  simp only [rt4, transverse, com_id_half, red_id_half, id, neg_neg, Real.sqrt_one,
    one_mul, div_one] at this
  norm_num at this
  have h1 := Real.sin_lt (Real.log_pos one_lt_two)
  have h2 := Real.log_two_lt_d9
  norm_num at h2; linarith

theorem reject_rt5 : ¬ LumDistSpec rt5 := fun h => by
  have := deSitter_at _ h
  simp [rt5, com_exp, red_exp] at this

theorem reject_rt6 : ¬ LumDistSpec rt6 := fun h => by
  have := milne_at _ h
  have hs : Real.sqrt (-1 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
  simp [rt6, hs] at this
  norm_num at this

theorem reject_rt7 : ¬ LumDistSpec rt7 := fun h => by
  have := milne_at _ h
  simp only [rt7, com_id_half, red_id_half, id] at this
  have h0 := Real.log_pos one_lt_two
  have h2 := Real.log_two_lt_d9
  have h3 : Real.log 2 ^ 3 < 0.6931471808 ^ 3 := by gcongr
  have h5 : Real.log 2 ^ 5 < 0.6931471808 ^ 5 := by gcongr
  norm_num at this h2 h3 h5
  nlinarith

theorem reject_rt8 : ¬ LumDistSpec rt8 := fun h => by
  have := deSitter_at _ h
  have hr : redshift Real.exp (-Real.log 2) 0 = -1 / 2 := by
    simp only [redshift, Real.exp_zero, Real.exp_neg, Real.exp_log two_pos]; norm_num
  simp only [rt8, transverse, lt_irrefl, ite_false, com_exp, hr, Real.exp_zero] at this
  norm_num at this

theorem reject_rt9 : ¬ LumDistSpec rt9 := fun h => by
  have := milne_at _ h
  simp only [rt9, transverse, com_id_half, red_id_half, id] at this
  norm_num at this
  rw [show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], sinh_two_log2] at this
  norm_num at this

theorem reject_rt10 : ¬ LumDistSpec rt10 := fun h => by
  have := h.staticClosed 1 0 zero_le_one
  have hH : hubble (fun _ => (1 : ℝ)) 1 = 0 := by simp [hubble]
  simp only [rt10, hH, comoving_one, redshift] at this
  norm_num at this
  linarith [Real.sin_lt one_pos]

theorem reject_rt11 : ¬ LumDistSpec rt11 := fun h => by
  have := deSitter_at _ h
  have hc : (∫ τ in (0 : ℝ)..(0 - -Real.log 2), 1 / Real.exp τ) = 1 / 2 := by
    have : (fun s => 1 / Real.exp s) = fun s => Real.exp (-s) := by
      funext s; rw [Real.exp_neg, one_div]
    rw [this, intervalIntegral.integral_comp_neg (fun s => Real.exp s), integral_exp]
    simp [Real.exp_neg, Real.exp_log two_pos]; norm_num
  simp only [rt11, transverse, lt_irrefl, ite_false, red_exp, hc, Real.exp_zero] at this
  norm_num at this

theorem reject_rt12 : ¬ LumDistSpec rt12 := fun h => by
  have := deSitter_at _ h
  simp only [rt12, transverse, lt_irrefl, ite_false, red_exp, Real.exp_zero,
    intervalIntegral.integral_const, Real.exp_neg, Real.exp_log two_pos] at this
  have h2 := Real.log_two_gt_d9
  norm_num at this h2
  linarith

end Work.Fidelity
