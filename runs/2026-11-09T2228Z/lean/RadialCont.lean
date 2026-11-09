import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp

open Set Filter Topology

namespace Scratch.Radial

/-- Regular singular point, generic: if θ is differentiable on `[0, S]` with derivative φ and
φ' = −((m+1)/ξ) φ + F on `(0, S]` with F bounded, then φ is continuous at 0 (and φ(0) = 0). -/
theorem cont_at_zero (S : ℝ) (hS : 0 < S) (m : ℕ) (θ φ F : ℝ → ℝ) (M : ℝ)
    (h1 : ∀ ξ ∈ Icc 0 S, HasDerivWithinAt θ (φ ξ) (Icc 0 S) ξ)
    (h3 : ∀ ξ ∈ Ioc 0 S, HasDerivWithinAt φ (-(((m : ℝ) + 1) / ξ * φ ξ) + F ξ) (Icc 0 S) ξ)
    (hF : ∀ ξ ∈ Ioc 0 S, |F ξ| ≤ M) :
    ContinuousWithinAt φ (Icc 0 S) 0 := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hF S ⟨hS, le_rfl⟩)
  set g : ℝ → ℝ := fun ξ => ξ ^ (m + 1) * φ ξ with hg
  have hgd : ∀ ξ ∈ Ioc 0 S, HasDerivWithinAt g (ξ ^ (m + 1) * F ξ) (Icc 0 S) ξ := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := hξ.1.ne'
    have h := ((hasDerivAt_pow (m + 1) ξ).hasDerivWithinAt (s := Icc 0 S)).mul (h3 ξ hξ)
    simp only [Nat.add_sub_cancel] at h
    convert h using 1
    rw [pow_succ]
    field_simp
    push_cast
    ring
  -- Lipschitz bound for g on [a, b] ⊆ (0, S]
  have hlip : ∀ a b, 0 < a → a ≤ b → b ≤ S → |g b - g a| ≤ M * b ^ (m + 1) * (b - a) := by
    intro a b ha hab hbS
    have hsub : Icc a b ⊆ Ioc 0 S := fun x hx => ⟨lt_of_lt_of_le ha hx.1, hx.2.trans hbS⟩
    have hsub' : Icc a b ⊆ Icc 0 S := Icc_subset_Icc ha.le hbS
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g)
      (f' := fun ξ => ξ ^ (m + 1) * F ξ) (s := Icc a b) (C := M * b ^ (m + 1))
      (fun x hx => (hgd x (hsub hx)).mono hsub')
      (fun x hx => by
        have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx0, mul_comm M]
        exact mul_le_mul (pow_le_pow_left₀ hx0.le hx.2 _) (hF x (hsub hx)) (abs_nonneg _)
          (pow_nonneg (hx0.le.trans hx.2) _))
      (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at h
  -- θ is Lipschitz at 0 (differentiability at 0)
  obtain ⟨δ, hδ, hθ0⟩ : ∃ δ > 0, ∀ x ∈ Icc 0 S, x < δ → |θ x - θ 0| ≤ (|φ 0| + 1) * x := by
    have h := ((h1 0 ⟨le_rfl, hS.le⟩).isLittleO.bound one_pos)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδ, hδ'⟩ := h
    refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
    have hd : dist x 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; exact hxδ
    have := hδ' hd hx
    simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul, abs_of_nonneg hx.1] at this
    calc |θ x - θ 0| = |(θ x - θ 0 - x * φ 0) + x * φ 0| := by ring_nf
      _ ≤ |θ x - θ 0 - x * φ 0| + |x * φ 0| := abs_add_le _ _
      _ ≤ x + x * |φ 0| := by
          rw [abs_mul, abs_of_nonneg hx.1]; linarith
      _ = (|φ 0| + 1) * x := by ring
  set L := |φ 0| + 1 with hL
  have hL0 : 0 ≤ L := by positivity
  -- first bound: |g a| ≤ C a^(m+1) near 0
  set C := 2 ^ (m + 1) * (3 * L + M * S) with hC
  have hgC : ∀ a, 0 < a → 2 * a < δ → 2 * a ≤ S → |g a| ≤ C * a ^ (m + 1) := by
    intro a ha h2δ h2S
    have hlt : a < 2 * a := by linarith
    have hcont : ContinuousOn θ (Icc a (2 * a)) := fun x hx =>
      ((h1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousWithinAt).mono
        (Icc_subset_Icc ha.le h2S)
    have hder : ∀ x ∈ Ioo a (2 * a), HasDerivAt θ (φ x) x := fun x hx =>
      (h1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩).hasDerivAt
        (Icc_mem_nhds (by linarith [hx.1]) (by linarith [hx.2]))
    obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope θ φ hlt hcont hder
    have hA := hθ0 (2 * a) ⟨by linarith, h2S⟩ h2δ
    have hB := hθ0 a ⟨ha.le, by linarith⟩ (by linarith)
    have hφζ : |φ ζ| ≤ 3 * L := by
      rw [hζeq, show 2 * a - a = a by ring, abs_div, abs_of_pos ha, div_le_iff₀ ha]
      calc |θ (2 * a) - θ a| = |(θ (2 * a) - θ 0) - (θ a - θ 0)| := by ring_nf
        _ ≤ |θ (2 * a) - θ 0| + |θ a - θ 0| := abs_sub _ _
        _ ≤ L * (2 * a) + L * a := add_le_add hA hB
        _ = 3 * L * a := by ring
    have hζ0 : 0 < ζ := ha.trans hζ.1
    have hgζ : |g ζ| ≤ (2 * a) ^ (m + 1) * (3 * L) := by
      simp only [hg, abs_mul, abs_pow, abs_of_pos hζ0]
      exact mul_le_mul (pow_le_pow_left₀ hζ0.le hζ.2.le _) hφζ (abs_nonneg _) (by positivity)
    have hl := hlip a ζ ha hζ.1.le (by linarith [hζ.2])
    have hl' : |g ζ - g a| ≤ M * (2 * a) ^ (m + 1) * a := by
      calc |g ζ - g a| ≤ M * ζ ^ (m + 1) * (ζ - a) := hl
        _ ≤ M * (2 * a) ^ (m + 1) * a := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hζ0.le hζ.2.le _) hM)
            (by linarith [hζ.2]) (by linarith [hζ.1]) (by positivity)
    have haS : a ≤ S := by linarith
    calc |g a| = |g ζ - (g ζ - g a)| := by ring_nf
      _ ≤ |g ζ| + |g ζ - g a| := abs_sub _ _
      _ ≤ (2 * a) ^ (m + 1) * (3 * L) + M * (2 * a) ^ (m + 1) * a := add_le_add hgζ hl'
      _ = 2 ^ (m + 1) * (3 * L + M * a) * a ^ (m + 1) := by ring
      _ ≤ C * a ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
  -- refined bound: |g a| ≤ M a^(m+2) on (0, S]
  have hgM : ∀ a ∈ Ioc 0 S, |g a| ≤ M * a ^ (m + 1) * a := by
    intro a ha
    have hpos : 0 < min a (min (δ / 2) (S / 2)) := by
      have := ha.1; positivity
    have hlim : Tendsto (fun b : ℝ => M * a ^ (m + 1) * a + C * b ^ (m + 1)) (𝓝[>] 0)
        (𝓝 (M * a ^ (m + 1) * a + C * 0 ^ (m + 1))) :=
      ((continuous_const.add (continuous_const.mul (continuous_pow _))).tendsto 0).mono_left
        nhdsWithin_le_nhds
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, mul_zero, add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hpos] with b hb
    have hb0 : 0 < b := hb.1
    have hba : b ≤ a := hb.2.le.trans (min_le_left _ _)
    have hbδ : 2 * b < δ := by
      have := hb.2.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
    have hbS : 2 * b ≤ S := by
      have := hb.2.le.trans ((min_le_right _ _).trans (min_le_right _ _)); linarith
    have h1' := hlip b a hb0 hba ha.2
    have h2' := hgC b hb0 hbδ hbS
    calc |g a| = |(g a - g b) + g b| := by ring_nf
      _ ≤ |g a - g b| + |g b| := abs_add_le _ _
      _ ≤ M * a ^ (m + 1) * (a - b) + C * b ^ (m + 1) := add_le_add h1' h2'
      _ ≤ M * a ^ (m + 1) * a + C * b ^ (m + 1) := by
          have : 0 ≤ M * a ^ (m + 1) * b := by have := ha.1; positivity
          nlinarith
  have hφM : ∀ a ∈ Ioc 0 S, |φ a| ≤ M * a := by
    intro a ha
    have hapos : 0 < a ^ (m + 1) := pow_pos ha.1 _
    have h := hgM a ha
    simp only [hg, abs_mul, abs_pow, abs_of_pos ha.1] at h
    nlinarith
  -- θ(x) − θ(0) = O(x²), so φ(0) = 0
  have hθ2 : ∀ x ∈ Icc 0 S, |θ x - θ 0| ≤ M * x ^ 2 := by
    intro x hx
    rcases hx.1.eq_or_lt with h0 | hx0
    · subst h0; simp
    have hcont : ContinuousOn θ (Icc 0 x) := fun y hy =>
      ((h1 y ⟨hy.1, hy.2.trans hx.2⟩).continuousWithinAt).mono (Icc_subset_Icc le_rfl hx.2)
    have hder : ∀ y ∈ Ioo 0 x, HasDerivAt θ (φ y) y := fun y hy =>
      (h1 y ⟨hy.1.le, hy.2.le.trans hx.2⟩).hasDerivAt
        (Icc_mem_nhds hy.1 (hy.2.trans_le hx.2))
    obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope θ φ hx0 hcont hder
    have hb := hφM ζ ⟨hζ.1, hζ.2.le.trans hx.2⟩
    rw [hζeq, sub_zero, abs_div, abs_of_pos hx0, div_le_iff₀ hx0] at hb
    have hMx : M * ζ ≤ M * x := mul_le_mul_of_nonneg_left hζ.2.le hM
    nlinarith [mul_le_mul_of_nonneg_right hMx hx0.le]
  have h0 : HasDerivWithinAt θ 0 (Icc 0 S) 0 := by
    rw [hasDerivWithinAt_iff_isLittleO]
    simp only [sub_zero, smul_zero]
    have hO : (fun x => θ x - θ 0) =O[𝓝[Icc 0 S] 0] fun x : ℝ => x ^ 2 := by
      refine Asymptotics.IsBigO.of_bound M ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
      exact hθ2 x hx
    exact hO.trans_isLittleO ((Asymptotics.isLittleO_pow_id one_lt_two).mono nhdsWithin_le_nhds)
  have hφ0 : φ 0 = 0 :=
    (uniqueDiffOn_Icc hS 0 ⟨le_rfl, hS.le⟩).eq_deriv _ (h1 0 ⟨le_rfl, hS.le⟩) h0
  show Tendsto φ (𝓝[Icc 0 S] 0) (𝓝 (φ 0))
  rw [hφ0]
  have hlim : Tendsto (fun x : ℝ => M * x) (𝓝[Icc 0 S] 0) (𝓝 0) := by
    have := ((show Continuous fun x : ℝ => M * x by fun_prop).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Icc 0 S))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.norm_eq_abs]
  rcases hx.1.eq_or_lt with h0 | hx0
  · subst h0; simp [hφ0]
  · exact hφM x ⟨hx0, hx.2⟩

end Scratch.Radial
