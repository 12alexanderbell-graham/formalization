import Mathlib
import Checked.Chemistry.CubicEOS

/-!
# Critical point with a temperature-dependent attraction parameter (referee item A, run 0628Z)

`Checked.Chemistry.CubicEOS.exists_unique_critical` assumes a constant `a`. Real cubic EOSs use
`a(T)` (Redlich–Kwong `A/√T`; Soave and Peng–Robinson `a_c α(T)`). Here: if `a(T) > 0` and
`T ↦ T/a(T)` is strictly increasing on `T > 0` and takes every positive value, the critical
point (T, v) of `P = R T/(v − b) − a(T)/(v² + ubv + wb²)` exists and is unique; instance:
Redlich–Kwong `a(T) = A/√T`. Work only (not yet frozen/audited/promoted).
-/

namespace Work.Chemistry.CubicEOSTemp

open Checked.Chemistry.CubicEOS

theorem exists_unique_critical_T (R b u w : ℝ) (aT : ℝ → ℝ) (hR : 0 < R) (hb : 0 < b)
    (hu : -2 < u) (h1 : 0 < 1 + u + w) (hpos : ∀ T, 0 < T → 0 < aT T)
    (hmono : StrictMonoOn (fun T => T / aT T) (Set.Ioi 0))
    (hsurj : ∀ y, 0 < y → ∃ T, 0 < T ∧ T / aT T = y) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧ IsCriticalIsotherm (cubicP R (aT p.1) b u w p.1) p.2 := by
  have hD : ∀ v : ℝ, b ≤ v → 0 < v ^ 2 + u * b * v + w * b ^ 2 := by
    intro v hv
    have e : v ^ 2 + u * b * v + w * b ^ 2 = b ^ 2 * (1 + u + w) + (v - b) * (v + b + u * b) := by ring
    rw [e]
    have : 0 ≤ (v - b) * (v + b + u * b) := mul_nonneg (by linarith) (by nlinarith)
    have : 0 < b ^ 2 * (1 + u + w) := by positivity
    linarith
  obtain ⟨x, ⟨hx1, hx0⟩, hxu⟩ := critCubic_existsUnique u w hu h1
  set v := x * b with hvdef
  have hv : b < v := by rw [hvdef]; nlinarith
  have hDv := hD v hv.le
  have hs : 0 < 2 * v + u * b := by rw [hvdef]; nlinarith
  set y := (v - b) ^ 2 * (2 * v + u * b) / (R * (v ^ 2 + u * b * v + w * b ^ 2) ^ 2) with hydef
  have hy : 0 < y := by
    rw [hydef]; apply div_pos
    · have : 0 < v - b := by linarith
      positivity
    · positivity
  obtain ⟨T, hT, hTy⟩ := hsurj y hy
  have haT := hpos T hT
  -- criticality at (T', v') ↔ v' = v ∧ T'/a(T') = y
  have key : ∀ T' v', 0 < T' → b < v' →
      (IsCriticalIsotherm (cubicP R (aT T') b u w T') v' ↔ v' = v ∧ T' / aT T' = y) := by
    intro T' v' hT' hv'
    have ha' := hpos T' hT'
    have hDv' := hD v' hv'.le
    rw [isCritical_iff R (aT T') b u w T' v' ha' hv' hDv']
    constructor
    · rintro ⟨hC, hRT⟩
      have hx' : v' / b = x := by
        apply hxu
        refine ⟨by rw [lt_div_iff₀ hb]; linarith, ?_⟩
        have := cubic_scale u w b (v' / b)
        rw [div_mul_cancel₀ v' hb.ne', hC] at this
        exact (mul_eq_zero.1 this.symm).resolve_left (by positivity)
      have hvv : v' = v := by rw [hvdef, ← hx', div_mul_cancel₀ v' hb.ne']
      refine ⟨hvv, ?_⟩
      subst hvv
      rw [hydef, div_eq_div_iff ha'.ne' (by positivity)]
      linear_combination hRT
    · rintro ⟨hvv, hTy'⟩
      subst hvv
      refine ⟨by rw [hvdef, cubic_scale, hx0, mul_zero], ?_⟩
      rw [hydef, div_eq_div_iff ha'.ne' (by positivity)] at hTy'
      linear_combination hTy'
  refine ⟨(T, v), ⟨hT, hv, (key T v hT hv).2 ⟨rfl, hTy⟩⟩, ?_⟩
  rintro ⟨T', v'⟩ ⟨hT', hv', hc⟩
  obtain ⟨hvv, hTy'⟩ := (key T' v' hT' hv').1 hc
  have : T' = T := hmono.injOn hT' hT (by rw [hTy', hTy])
  rw [this, hvv]

/-- Redlich–Kwong with its original temperature dependence `a(T) = A/√T`: exactly one
critical point. -/
theorem rk_exists_unique_critical (R A b : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧
      IsCriticalIsotherm (cubicP R (A / Real.sqrt p.1) b 1 0 p.1) p.2 := by
  have hpos : ∀ T, 0 < T → 0 < A / Real.sqrt T := fun T hT => div_pos hA (Real.sqrt_pos.2 hT)
  have hform : ∀ T, 0 < T → T / (A / Real.sqrt T) = T * Real.sqrt T / A := by
    intro T hT; field_simp
  apply exists_unique_critical_T R b 1 0 (fun T => A / Real.sqrt T) hR hb (by norm_num)
    (by norm_num) hpos
  · intro s hs t ht hst
    simp only
    rw [hform s hs, hform t ht]
    apply div_lt_div_of_pos_right _ hA
    exact mul_lt_mul hst (Real.sqrt_le_sqrt hst.le) (Real.sqrt_pos.2 hs) (le_of_lt (lt_trans hs hst))
  · intro y hy
    -- T = (A y)^(2/3)
    refine ⟨(A * y) ^ ((2 : ℝ) / 3), by positivity, ?_⟩
    have hAy : 0 < A * y := mul_pos hA hy
    have hT : 0 < (A * y) ^ ((2 : ℝ) / 3) := by positivity
    show (A * y) ^ ((2 : ℝ) / 3) / (A / Real.sqrt ((A * y) ^ ((2 : ℝ) / 3))) = y
    rw [hform _ hT, Real.sqrt_eq_rpow, ← Real.rpow_mul hAy.le]
    rw [show (A * y) ^ ((2 : ℝ) / 3) * (A * y) ^ ((2 : ℝ) / 3 * (1 / 2)) = A * y by
      rw [← Real.rpow_add hAy]; norm_num]
    field_simp

end Work.Chemistry.CubicEOSTemp
