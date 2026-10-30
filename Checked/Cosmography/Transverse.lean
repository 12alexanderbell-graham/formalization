import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Checked.Cosmography.BambaDLy

/-!
# Fifth-order expansion of the curved transverse distance

Helper for C6/C7 (STATE next step 2). Generic ODE form: any `S`, `C` with `S′ = C`, `C′ = −K S`,
`S(0) = 0`, `C(0) = 1` satisfy `S(χ) = χ − Kχ³/6 + K²χ⁵/120 + o(χ⁵)`. This covers
`sin(√K χ)/√K` (K > 0), `χ` (K = 0) and `sinh(√−K χ)/√−K` (K < 0). Helper lemma, not a headline. PROMOTED in run 2026-10-30T1028Z from `Work/Cosmography/Transverse.lean`
(written run 2026-10-30T0828Z) together with C6.
-/

namespace Checked.Cosmography.Transverse

open Filter Asymptotics Topology Checked.Cosmography.BambaY

lemma ode_expansion (K : ℝ) (S C : ℝ → ℝ) (hS : ∀ x, HasDerivAt S (C x) x)
    (hC : ∀ x, HasDerivAt C (-K * S x) x) (hS0 : S 0 = 0) (hC0 : C 0 = 1) :
    (fun x => S x - (x - K * x ^ 3 / 6 + K ^ 2 * x ^ 5 / 120)) =o[𝓝 0] fun x => x ^ 5 := by
  set E1 : ℝ → ℝ := fun x => S x - (x - K * x ^ 3 / 6 + K ^ 2 * x ^ 5 / 120) with hE1
  set E2 : ℝ → ℝ := fun x => C x - (1 - K * x ^ 2 / 2 + K ^ 2 * x ^ 4 / 24) with hE2
  have d1 : ∀ x, HasDerivAt E1 (E2 x) x := by
    intro x
    have h := (hS x).sub ((((hasDerivAt_id' x).sub (((hasDerivAt_pow 3 x).const_mul K).div_const 6)).add
      (((hasDerivAt_pow 5 x).const_mul (K ^ 2)).div_const 120)))
    convert h using 1
    simp only [hE2]; push_cast; ring
  have d2 : ∀ x, HasDerivAt E2 (-K * E1 x - K ^ 3 * x ^ 5 / 120) x := by
    intro x
    have h := (hC x).sub (((hasDerivAt_const x (1 : ℝ)).sub (((hasDerivAt_pow 2 x).const_mul K).div_const 2)).add
      (((hasDerivAt_pow 4 x).const_mul (K ^ 2)).div_const 24))
    convert h using 1
    simp only [hE1]; push_cast; ring
  have e10 : E1 0 = 0 := by simp [hE1, hS0]
  have e20 : E2 0 = 0 := by simp [hE2, hC0]
  have ev1 : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt E1 (E2 x) x := Eventually.of_forall d1
  have ev2 : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt E2 (-K * E1 x - K ^ 3 * x ^ 5 / 120) x :=
    Eventually.of_forall d2
  have pw : ∀ {n m : ℕ}, n < m → (fun x : ℝ => (x - 0) ^ m) =o[𝓝 0] fun x => (x - 0) ^ n :=
    fun h => by
      have := isLittleO_pow_sub_pow_sub (0 : ℝ) h
      simp_rw [← norm_pow] at this
      exact isLittleO_norm_norm.1 this
  -- the forcing term K³x⁵/120 = o(xⁿ) for n < 5
  have force : ∀ {n : ℕ}, n < 5 → (fun x : ℝ => K ^ 3 * x ^ 5 / 120) =o[𝓝 0] fun x => (x - 0) ^ n := by
    intro n hn
    have := (pw hn).const_mul_left (K ^ 3 / 120)
    refine this.congr' (Eventually.of_forall fun x => ?_) EventuallyEq.rfl
    simp only [sub_zero]; ring
  have rhs : ∀ {n : ℕ}, n < 5 → E1 =o[𝓝 0] (fun x => (x - 0) ^ n) →
      (fun x => -K * E1 x - K ^ 3 * x ^ 5 / 120) =o[𝓝 0] fun x => (x - 0) ^ n :=
    fun hn h => (h.const_mul_left (-K)).sub (force hn)
  -- E1 = o(1)
  have o0 : E1 =o[𝓝 0] fun x => (x - 0) ^ 0 := by
    simp only [pow_zero]
    rw [isLittleO_one_iff]
    have := (d1 0).continuousAt.tendsto
    rwa [e10] at this
  have a1 := littleO_of_hasDerivAt e20 ev2 (rhs (by norm_num) o0)   -- E2 = o(x)
  have b2 := littleO_of_hasDerivAt e10 ev1 a1                       -- E1 = o(x²)
  have a3 := littleO_of_hasDerivAt e20 ev2 (rhs (by norm_num) b2)   -- E2 = o(x³)
  have b4 := littleO_of_hasDerivAt e10 ev1 a3                       -- E1 = o(x⁴)
  have a5 := littleO_of_hasDerivAt e20 ev2 (rhs (by norm_num) b4)   -- E2 = o(x⁵)
  have b6 := littleO_of_hasDerivAt e10 ev1 a5                       -- E1 = o(x⁶)
  have := b6.trans (pw (show 5 < 0 + 1 + 1 + 1 + 1 + 1 + 1 by norm_num))
  simpa [hE1] using this

/-- Comoving transverse distance factor `S_K(χ)` (Bamba et al. Eq. (10.28) with general `K`):
`sin(√K χ)/√K` for `K > 0`, `χ` for `K = 0`, `sinh(√−K χ)/√−K` for `K < 0`. -/
noncomputable def transverse (K χ : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * χ) / Real.sqrt K
  else if K < 0 then Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K) else χ

/-- `S_K(χ) = χ − Kχ³/6 + K²χ⁵/120 + o(χ⁵)` for every `K`. -/
theorem transverse_expansion (K : ℝ) :
    (fun x => transverse K x - (x - K * x ^ 3 / 6 + K ^ 2 * x ^ 5 / 120)) =o[𝓝 0]
      fun x => x ^ 5 := by
  rcases lt_trichotomy K 0 with hK | hK | hK
  · set r := Real.sqrt (-K) with hr
    have hr0 : r ≠ 0 := (Real.sqrt_pos.2 (neg_pos.2 hK)).ne'
    have hrr : r * r = -K := Real.mul_self_sqrt (neg_nonneg.2 hK.le)
    have e : ∀ x, transverse K x = Real.sinh (r * x) / r := by
      intro x; simp [transverse, hK, not_lt.2 hK.le, hr]
    simp only [e]
    refine ode_expansion K (fun x => Real.sinh (r * x) / r) (fun x => Real.cosh (r * x))
      (fun x => ?_) (fun x => ?_) (by simp) (by simp)
    · have := (((hasDerivAt_id' x).const_mul r).sinh).div_const r
      convert this using 1; field_simp
    · have := ((hasDerivAt_id' x).const_mul r).cosh
      convert this using 1
      field_simp
      linear_combination (-(Real.sinh (r * x))) * hrr
  · subst hK
    have e : ∀ x, transverse 0 x = x := by intro x; simp [transverse]
    simp only [e]
    refine ode_expansion 0 (fun x => x) (fun _ => 1) (fun x => hasDerivAt_id' x)
      (fun x => by simpa using hasDerivAt_const x (1 : ℝ)) (by simp) (by simp)
  · set r := Real.sqrt K with hr
    have hr0 : r ≠ 0 := (Real.sqrt_pos.2 hK).ne'
    have hrr : r * r = K := Real.mul_self_sqrt hK.le
    have e : ∀ x, transverse K x = Real.sin (r * x) / r := by
      intro x; simp [transverse, hK, hr]
    simp only [e]
    refine ode_expansion K (fun x => Real.sin (r * x) / r) (fun x => Real.cos (r * x))
      (fun x => ?_) (fun x => ?_) (by simp) (by simp)
    · have := (((hasDerivAt_id' x).const_mul r).sin).div_const r
      convert this using 1; field_simp
    · have := ((hasDerivAt_id' x).const_mul r).cos
      convert this using 1
      field_simp
      linear_combination (Real.sin (r * x)) * hrr

end Checked.Cosmography.Transverse
