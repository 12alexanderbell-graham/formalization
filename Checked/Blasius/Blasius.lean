import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Blasius.BTail
import Checked.Blasius.BQData
/-! Blasius boundary layer, `Blasius`: the wall shear of the Blasius boundary layer, as printed in the statement of `blasius_wall_shear`, from the scaling symmetry, the validated chain and the tail bound. Promoted from `Work/Blasius/Blasius.lean`. -/

namespace Checked.Blasius
open Set Filter Topology

/-- Blasius boundary layer, wall shear: for every solution f of f''' + f f''/2 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q/2, one-sided at 0) with
f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞, the wall value q(0) = f''(0) lies between
0.33205733621519 and 0.33205733621520. -/
theorem blasius_wall_shear (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η / 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.33205733621519 ≤ q 0 ∧ q 0 ≤ 0.33205733621520 := by
  have S : BTail.IsSol f p q := ⟨hf, hp, hq⟩
  set s := q 0 with hsdef
  have hs : 0 < s := BTail.shear_pos S hp0 hlim
  set c : ℝ := s ^ ((3 : ℕ)⁻¹ : ℝ) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hs _
  have hc3 : c ^ 3 = s := Real.rpow_inv_natCast_pow hs.le (by norm_num)
  have S' := BTail.scale S hc
  set G : ℝ → ℝ := fun t => f (t / c) / c with hG
  set P : ℝ → ℝ := fun t => p (t / c) / c ^ 2 with hP
  set Q : ℝ → ℝ := fun t => q (t / c) / c ^ 3 with hQ
  have hG0 : G 0 = 0 := by simp [hG, hf0]
  have hP0 : P 0 = 0 := by simp [hP, hp0]
  have hQ0 : Q 0 = 1 := by simp only [hQ, zero_div]; rw [hc3]; exact div_self hs.ne'
  have hsub : Icc (0 : ℝ) 9 ⊆ Ici 0 := Icc_subset_Ici_self
  obtain ⟨eg, ep, eq⟩ := BQData.chain (g := G) (p := P) (q := Q)
    (fun t ht => (S'.hf t ht.1).mono hsub) (fun t ht => (S'.hp t ht.1).mono hsub)
    (fun t ht => (S'.hq t ht.1).mono hsub) hG0 hP0 hQ0
  simp only [BQData.FG, BQData.FP, BQData.FQ, BQData.R] at eg ep eq
  push_cast at eg ep eq
  rw [abs_le] at eg ep eq
  have hQpos := BTail.q_pos S' (by rw [hQ0]; norm_num)
  set m : ℝ := 1628370244619923024327 / 100000000000000000000 - 3218827 / 2000000000000000000000
    with hm
  have htail := BTail.tail S' hQpos (L := 9) (m := m) (by norm_num) (by norm_num [hm])
    (by rw [hm]; linarith [eg.1]) (by linarith [ep.1])
  have hlimP : Tendsto P atTop (𝓝 (1 / c ^ 2)) :=
    (hlim.comp (tendsto_id.atTop_div_const hc)).div_const (c ^ 2)
  have hlo : P 9 ≤ 1 / c ^ 2 :=
    ge_of_tendsto hlimP ((eventually_ge_atTop 9).mono fun t ht => (htail t ht).1)
  have hhi : 1 / c ^ 2 ≤ P 9 + 2 / m * Q 9 :=
    le_of_tendsto hlimP ((eventually_ge_atTop 9).mono fun t ht => (htail t ht).2)
  set a : ℝ := 1 / c ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have hsa : s ^ 2 * a ^ 3 = 1 := by
    rw [← hc3, ha]; field_simp
  have hA1 : (26067614705473778303 / 12500000000000000000 : ℝ) - 3218827 / 2000000000000000000000
      ≤ a := by linarith [ep.1]
  have hA2 : a ≤ (26067614705473778303 / 12500000000000000000 : ℝ) + 3218827 / 2000000000000000000000
      + 2 / m * ((1102563 / 100000000000000000000 : ℝ) + 3218827 / 2000000000000000000000) := by
    have hm0 : 0 < 2 / m := by norm_num [hm]
    nlinarith [ep.2, eq.2, mul_le_mul_of_nonneg_left eq.2 hm0.le]
  have hA1p : (0 : ℝ) < (26067614705473778303 / 12500000000000000000 : ℝ)
      - 3218827 / 2000000000000000000000 := by norm_num
  have ha3lo := pow_le_pow_left₀ hA1p.le hA1 3
  have ha3hi := pow_le_pow_left₀ ha0.le hA2 3
  constructor
  · have k : (0.33205733621519 : ℝ) ^ 2 * ((26067614705473778303 / 12500000000000000000 : ℝ)
        + 3218827 / 2000000000000000000000 + 2 / m * ((1102563 / 100000000000000000000 : ℝ)
        + 3218827 / 2000000000000000000000)) ^ 3 ≤ 1 := by
      rw [hm]; norm_num
    have h2 : (0.33205733621519 : ℝ) ^ 2 ≤ s ^ 2 := by
      by_contra hc'
      push Not at hc'
      have := mul_lt_mul_of_pos_right hc' (pow_pos ha0 3)
      nlinarith [mul_le_mul_of_nonneg_left ha3hi (sq_nonneg (0.33205733621519 : ℝ))]
    nlinarith [h2, hs]
  · have k : 1 ≤ (0.33205733621520 : ℝ) ^ 2 * ((26067614705473778303 / 12500000000000000000 : ℝ)
        - 3218827 / 2000000000000000000000) ^ 3 := by norm_num
    have h2 : s ^ 2 ≤ (0.33205733621520 : ℝ) ^ 2 := by
      by_contra hc'
      push Not at hc'
      have := mul_lt_mul_of_pos_right hc' (pow_pos ha0 3)
      nlinarith [mul_le_mul_of_nonneg_left ha3lo (sq_nonneg (0.33205733621520 : ℝ))]
    nlinarith [h2, hs]

end Checked.Blasius
