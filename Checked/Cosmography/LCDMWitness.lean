import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Checked.Cosmography.LCDMCoefficients

/-!
# Flat ΛCDM models exist for every 0 < Ω < 1 (referee's point on F1)

PROMOTED from `Work/Cosmography/AvilesWitness.lean` (statements byte-identical); audit addendum in
`runs/2026-10-30T0220Z/audit.md`.

Witness: `a(t) = sinh(t)^{2/3}` at `t₀ > 0` is flat ΛCDM with `Ω = 1 / cosh²(t₀)`
(H = (2/3) coth t; H² = H₀²(Ω (a₀/a)³ + 1 − Ω) by cosh² = 1 + sinh²). Every Ω ∈ (0,1) arises:
take `t₀ = arsinh √(1/Ω − 1)`.

Consequence: the printed l₀ of Aviles et al. Eq. (15) is false at **every** Ω ∈ (0,1), and the
printed m₀ at every Ω ∈ (0,1) other than (√7 − 1)/3, not only at Ω = 1.
-/

namespace Checked.Cosmography.AvilesWitness

open Filter Topology Real Checked.Cosmography Checked.Cosmography.Aviles

noncomputable def lam : ℝ → ℝ := fun t => sinh t ^ (2 / 3 : ℝ)

lemma hasDerivAt_lam {t : ℝ} (ht : 0 < t) :
    HasDerivAt lam (cosh t * (2 / 3) * sinh t ^ ((2 / 3 : ℝ) - 1)) t :=
  (hasDerivAt_sinh t).rpow_const (Or.inl (sinh_pos_iff.2 ht).ne')

lemma hubble_lam {t : ℝ} (ht : 0 < t) : hubble lam t = 2 / 3 * cosh t / sinh t := by
  have hs : 0 < sinh t := sinh_pos_iff.2 ht
  unfold hubble
  rw [(hasDerivAt_lam ht).deriv, lam, rpow_sub hs, rpow_one]
  have : 0 < sinh t ^ (2 / 3 : ℝ) := rpow_pos_of_pos hs _
  field_simp

lemma lam_cube {t : ℝ} (ht : 0 < t) : lam t ^ 3 = sinh t ^ 2 := by
  unfold lam
  rw [← rpow_natCast, ← rpow_mul (sinh_pos_iff.2 ht).le]
  norm_num

theorem lam_isFlatLCDM {t₀ : ℝ} (h₀ : 0 < t₀) : IsFlatLCDM (1 / cosh t₀ ^ 2) lam t₀ := by
  have hs0 : 0 < sinh t₀ := sinh_pos_iff.2 h₀
  have hc0 : 0 < cosh t₀ := cosh_pos t₀
  refine ⟨by rw [hubble_lam h₀]; positivity, ?_⟩
  filter_upwards [lt_mem_nhds h₀] with t ht
  have hs : 0 < sinh t := sinh_pos_iff.2 ht
  have hc : 0 < cosh t := cosh_pos t
  refine ⟨rpow_pos_of_pos hs _, (hasDerivAt_lam ht).differentiableAt, ?_⟩
  rw [hubble_lam ht, hubble_lam h₀, redshift, add_sub_cancel]
  have e0 : 0 < lam t₀ := rpow_pos_of_pos hs0 _
  have e1 : 0 < lam t := rpow_pos_of_pos hs _
  have harg : 1 / cosh t₀ ^ 2 * (lam t₀ / lam t) ^ 3 + 1 - 1 / cosh t₀ ^ 2 =
      (sinh t₀ * cosh t / (cosh t₀ * sinh t)) ^ 2 := by
    rw [div_pow, lam_cube h₀, lam_cube ht]
    have h1 := cosh_sq t₀
    have h2 := cosh_sq t
    field_simp
    linear_combination (-sinh t₀ ^ 2) * h2 + (sinh t ^ 2) * h1
  rw [harg, sqrt_sq (by positivity)]
  field_simp

/-- Every Ω ∈ (0,1) is realised by a C^∞ flat ΛCDM model. -/
theorem exists_flatLCDM {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ ∧ ContDiffAt ℝ 6 a t₀ := by
  set u := √(1 / Ω - 1) with hu
  have hu0 : 0 < u := sqrt_pos.2 (by rw [lt_sub_iff_add_lt, zero_add, lt_div_iff₀ h0]; linarith)
  set t₀ := arsinh u
  have ht0 : 0 < t₀ := arsinh_pos_iff.2 hu0
  have hΩ : 1 / cosh t₀ ^ 2 = Ω := by
    rw [cosh_sq, sinh_arsinh, hu, sq_sqrt (by rw [sub_nonneg, le_div_iff₀ h0]; linarith)]
    field_simp
    ring
  refine ⟨lam, t₀, hΩ ▸ lam_isFlatLCDM ht0, ?_⟩
  exact (contDiff_sinh.contDiffAt).rpow_const_of_ne (sinh_pos_iff.2 ht0).ne'

/-- The printed l₀ of Eq. (15) is false at every Ω ∈ (0,1). -/
theorem printedL0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ¬ ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
      cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 2 * Ω ^ 2 := by
  intro h
  obtain ⟨a, t₀, hL, hs⟩ := exists_flatLCDM h0 h1
  have e := h a t₀ hL hs
  rw [(flatLCDM_coeffs Ω a t₀ hL hs).2.2.2.1] at e
  have : Ω ^ 2 = 0 := by linarith
  exact h0.ne' (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- The printed m₀ of Eq. (15) is false at every Ω ∈ (0,1) where it differs from the true
polynomial, i.e. every Ω ∈ (0,1) except the root (√7 − 1)/3 of 3Ω² + 2Ω − 2 = 0. -/
theorem printedM0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hr : 3 * Ω ^ 2 + 2 * Ω - 2 ≠ 0) :
    ¬ ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
      cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω ^ 2 - 81 * Ω ^ 2 - 81 / 2 * Ω ^ 3 := by
  intro h
  obtain ⟨a, t₀, hL, hs⟩ := exists_flatLCDM h0 h1
  have e := h a t₀ hL hs
  rw [(flatLCDM_coeffs Ω a t₀ hL hs).2.2.2.2] at e
  -- difference: (81/4) Ω (3Ω² + 2Ω − 2) / ... ; check: true − printed = 27/2 Ω(Ω − 1) + 81/4 Ω³
  have : Ω * (3 * Ω ^ 2 + 2 * Ω - 2) = 0 := by linear_combination (4 / 27) * e
  rcases mul_eq_zero.1 this with h' | h'
  · exact h0.ne' h'
  · exact hr h'

end Checked.Cosmography.AvilesWitness
