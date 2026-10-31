import Work.Cosmography.B1Truncation
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Work.Cosmography.B1

open Checked.Cosmography Checked.Cosmography.BambaY

/-- **Witness (global exact flat ΛCDM).** `a(t) = sinh(3t/2)^{2/3}` (so `H = coth(3t/2)`,
`H² = 1 + a⁻³`), observed at `t₀` with `sinh(3t₀/2) = 2`, is flat ΛCDM with `Ω = 1/5` on the
whole interval from a `z = 7` source (time `t₇`) through a `z = 3` source (`t₃`) to `t₀`. -/
theorem exists_flatLCDM_on :
    ∃ (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ), t₇ ≤ t₃ ∧ t₃ ≤ t₀ ∧
      (∀ s ∈ Set.Icc t₇ t₀, 0 < a s) ∧ (∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s) ∧
      0 < hubble a t₀ ∧
      (∀ s ∈ Set.Icc t₇ t₀,
        hubble a s = hubble a t₀ * √(1 / 5 * (1 + redshift a t₀ s) ^ 3 + 1 - 1 / 5)) ∧
      redshift a t₀ t₃ = 3 ∧ redshift a t₀ t₇ = 7 := by
  set S : ℝ → ℝ := fun s => Real.sinh (3 / 2 * s) with hS
  set a : ℝ → ℝ := fun s => S s ^ (2 / 3 : ℝ) with ha
  have hSt : ∀ y, S (2 / 3 * Real.arsinh y) = y := by
    intro y; simp only [hS]; rw [show 3 / 2 * (2 / 3 * Real.arsinh y) = Real.arsinh y by ring,
      Real.sinh_arsinh]
  have h8 : (0:ℝ) < 8 ^ (3 / 2 : ℝ) := by positivity
  have h8' : (8:ℝ) ≤ 8 ^ (3 / 2 : ℝ) := by
    calc (8:ℝ) = 8 ^ (1:ℝ) := by norm_num
      _ ≤ 8 ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  set y₇ : ℝ := 2 / 8 ^ (3 / 2 : ℝ) with hy₇
  have hy₇0 : 0 < y₇ := by positivity
  have hy₇1 : y₇ ≤ 1 / 4 := by
    rw [hy₇, div_le_iff₀ h8]; linarith
  set t₇ : ℝ := 2 / 3 * Real.arsinh y₇
  set t₃ : ℝ := 2 / 3 * Real.arsinh (1 / 4)
  set t₀ : ℝ := 2 / 3 * Real.arsinh 2
  have ht₇ : 0 < t₇ := by have := Real.arsinh_pos_iff.2 hy₇0; positivity
  have h73 : t₇ ≤ t₃ := by
    have := Real.arsinh_le_arsinh.2 hy₇1; simp only [t₇, t₃]; linarith
  have h30 : t₃ ≤ t₀ := by
    have := Real.arsinh_le_arsinh.2 (show (1 / 4 : ℝ) ≤ 2 by norm_num); simp only [t₃, t₀]; linarith
  have hSpos : ∀ s, 0 < s → 0 < S s := by
    intro s hs; simp only [hS]; exact Real.sinh_pos_iff.2 (by positivity)
  -- derivative and Hubble rate
  have hderS : ∀ s, HasDerivAt S (Real.cosh (3 / 2 * s) * (3 / 2)) s := by
    intro s
    have h := (Real.hasDerivAt_sinh (3 / 2 * s)).comp s ((hasDerivAt_id s).const_mul (3 / 2))
    rw [mul_one] at h; exact h
  have hdera : ∀ s, 0 < s →
      HasDerivAt a (Real.cosh (3 / 2 * s) * (3 / 2) * (2 / 3) * S s ^ ((2 / 3 : ℝ) - 1)) s := by
    intro s hs
    exact (hderS s).rpow_const (Or.inl (hSpos s hs).ne')
  have hhub : ∀ s, 0 < s → hubble a s = Real.cosh (3 / 2 * s) / S s := by
    intro s hs
    have hSs := hSpos s hs
    unfold hubble
    rw [(hdera s hs).deriv]
    simp only [ha]
    rw [Real.rpow_sub hSs, Real.rpow_one]
    have : 0 < S s ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hSs _
    field_simp
  have hcube : ∀ x : ℝ, 0 < x → (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hz3 : ∀ s, 0 < s → (1 + redshift a t₀ s) ^ 3 = 4 / S s ^ 2 := by
    intro s hs
    have hSs := hSpos s hs
    unfold redshift
    simp only [ha]
    rw [hSt 2, show 1 + ((2:ℝ) ^ (2 / 3 : ℝ) / S s ^ (2 / 3 : ℝ) - 1) =
      (2:ℝ) ^ (2 / 3 : ℝ) / S s ^ (2 / 3 : ℝ) by ring, div_pow, hcube 2 (by norm_num),
      hcube _ hSs]
    norm_num
  have hcosh : ∀ s, Real.cosh (3 / 2 * s) = √(1 + S s ^ 2) := by
    intro s
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (Real.cosh_pos _).le]
    simp only [hS]; rw [← sq, Real.cosh_sq]; ring
  have hpos0 : 0 < t₀ := lt_of_lt_of_le ht₇ (le_trans h73 h30)
  have hH0 : hubble a t₀ = √5 / 2 := by
    rw [hhub t₀ hpos0, hcosh, hSt 2]; norm_num
  refine ⟨a, t₇, t₃, t₀, h73, h30, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs; exact Real.rpow_pos_of_pos (hSpos s (lt_of_lt_of_le ht₇ hs.1)) _
  · intro s hs; exact (hdera s (lt_of_lt_of_le ht₇ hs.1)).differentiableAt
  · rw [hH0]; positivity
  · intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht₇ hs.1
    have hSs := hSpos s hs0
    rw [hhub s hs0, hH0, hz3 s hs0, hcosh]
    have e : 1 / 5 * (4 / S s ^ 2) + 1 - 1 / 5 = (2 * √(1 + S s ^ 2) / (√5 * S s)) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
      field_simp; ring
    rw [e, Real.sqrt_sq (by positivity)]
    have : (0:ℝ) < √5 := by positivity
    field_simp
  · unfold redshift; simp only [ha]
    rw [hSt 2, hSt, ← Real.div_rpow (by norm_num) (by norm_num),
      show (2:ℝ) / (1 / 4) = 2 ^ (3:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  · unfold redshift; simp only [ha]
    rw [hSt 2, hSt, ← Real.div_rpow (by norm_num) hy₇0.le, hy₇,
      show (2:ℝ) / (2 / 8 ^ (3 / 2 : ℝ)) = 8 ^ (3 / 2 : ℝ) by field_simp,
      ← Real.rpow_mul (by norm_num)]
    norm_num

end Work.Cosmography.B1
