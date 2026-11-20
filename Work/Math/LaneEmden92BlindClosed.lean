import Mathlib
import Work.Math.LaneEmden92

/-!
# Lane–Emden index nine halves: the blind restatement closed

The blind restatement (`runs/2026-11-20T0428Z/blind/LaneEmden92Blind.lean`, statement copied
verbatim by `runs/2026-11-20T0428Z/scripts/mk_blind_closed92.py`, run 2026-11-20T0428Z, from
`mk_blind_closed72.py` of run 2026-11-19T2228Z) asks for θ continuous on [0, 32], θ(0) = 1,
right-derivative 0 at 0, on the open interval (0, 32) differentiability of θ and of `deriv θ`
(`hdiff`), and there the equation in `deriv` form (`hode`); it concludes with the first zero as
the least zero in [0, 32] (`IsLeast`) and with `deriv θ` at that zero. It follows from the
program's helper `Work.Math.LaneEmden92.core` on [0, 796/25] with
φ ξ = if ξ = 0 then 0 else deriv θ ξ. The one point not given by the hypotheses is the continuity
of φ at 0 from the right, i.e. deriv θ ξ → 0 as ξ → 0+ (`tendsto_deriv_zero`): with
ψ ξ = ξ ^ 2 θ'(ξ) one has ψ' = -ξ ^ 2 θ ^ (9/2), bounded by K ξ ^ 2 on (0, 32), where K bounds
|θ ^ (9/2)| on the compact [0, 32] (θ is continuous there); the mean value theorem on [ξ, 2ξ]
gives c with θ'(c) = (θ(2ξ) - θ(ξ))/ξ, whence |θ'(ξ)| ≤ 4 |θ(2ξ) - θ(ξ)|/ξ + 4 K ξ
(`key_bound`), and the right side tends to 0 because θ has right-derivative 0 at 0. Every zero in
[0, 32] is at least ξ₁ because the helper gives θ > 0 on [0, ξ₁), which yields the `IsLeast`
form.
-/

namespace Work.Math.LaneEmden92BlindClosed
open Set Filter Topology

/-- Pointwise bound on θ' at ξ from the equation on (0, b) and the mean value theorem on
[ξ, 2ξ]. -/
theorem key_bound (θ θ' f : ℝ → ℝ) (b K : ℝ)
    (hθ : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt θ (θ' x) x)
    (hθ' : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt θ' (-(2 / x * θ' x) - f x) x)
    (hf : ∀ x ∈ Ioo (0 : ℝ) b, |f x| ≤ K) {ξ : ℝ} (hξ : 0 < ξ) (h2 : 2 * ξ < b) :
    |θ' ξ| ≤ 4 * (|θ (2 * ξ) - θ ξ| / ξ) + 4 * K * ξ := by
  have hsub : Icc ξ (2 * ξ) ⊆ Ioo (0 : ℝ) b := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf ξ (hsub ⟨le_rfl, by linarith⟩))
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope θ θ' (show ξ < 2 * ξ by linarith)
    (fun x hx => (hθ x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => hθ x (hsub (Ioo_subset_Icc_self hx)))
  have hcs' : θ' c = (θ (2 * ξ) - θ ξ) / ξ := by
    rw [hcs, show 2 * ξ - ξ = ξ by ring]
  have hc0 : 0 < c := by linarith [hc.1]
  have hψd : ∀ x ∈ Ioo (0 : ℝ) b,
      HasDerivAt (fun y => y ^ 2 * θ' y) (-(x ^ 2 * f x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h := (hasDerivAt_pow 2 x).mul (hθ' x hx)
    refine h.congr_deriv ?_
    field_simp
    ring
  have hseg : ∀ x ∈ Icc ξ c,
      HasDerivWithinAt (fun y => y ^ 2 * θ' y) (-(x ^ 2 * f x)) (Icc ξ c) x := fun x hx =>
    (hψd x (hsub ⟨hx.1, by linarith [hx.2, hc.2]⟩)).hasDerivWithinAt
  have hbd : ∀ x ∈ Ico ξ c, ‖-(x ^ 2 * f x)‖ ≤ 4 * K * ξ ^ 2 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hfx := hf x (hsub ⟨hx.1, by linarith [hx.2, hc.2]⟩)
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (pow_pos hx0 2)]
    have hx2 : x ^ 2 ≤ 4 * ξ ^ 2 := by nlinarith [hx.2, hc.2]
    calc x ^ 2 * |f x| ≤ (4 * ξ ^ 2) * K := mul_le_mul hx2 hfx (abs_nonneg _) (by positivity)
      _ = 4 * K * ξ ^ 2 := by ring
  have hψc : ‖c ^ 2 * θ' c - ξ ^ 2 * θ' ξ‖ ≤ 4 * K * ξ ^ 2 * (c - ξ) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hseg hbd c ⟨hc.1.le, le_rfl⟩
  rw [Real.norm_eq_abs] at hψc
  have h3 : |c ^ 2 * θ' c - ξ ^ 2 * θ' ξ| ≤ 4 * K * ξ ^ 3 := by
    refine hψc.trans ?_
    have hcξ : c - ξ ≤ ξ := by linarith [hc.2]
    calc 4 * K * ξ ^ 2 * (c - ξ) ≤ 4 * K * ξ ^ 2 * ξ :=
          mul_le_mul_of_nonneg_left hcξ (by positivity)
      _ = 4 * K * ξ ^ 3 := by ring
  have h5 : |c ^ 2 * θ' c| ≤ 4 * ξ ^ 2 * (|θ (2 * ξ) - θ ξ| / ξ) := by
    rw [abs_mul, abs_of_pos (pow_pos hc0 2), hcs', abs_div, abs_of_pos hξ]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hc.2]) (by positivity)
  have h6 : |ξ ^ 2 * θ' ξ| ≤ |c ^ 2 * θ' c| + 4 * K * ξ ^ 3 := by
    have := abs_sub_abs_le_abs_sub (ξ ^ 2 * θ' ξ) (c ^ 2 * θ' c)
    rw [abs_sub_comm] at this
    linarith
  rw [abs_mul, abs_of_pos (pow_pos hξ 2)] at h6
  have hξ2 : 0 < ξ ^ 2 := pow_pos hξ 2
  refine le_of_mul_le_mul_left ?_ hξ2
  calc ξ ^ 2 * |θ' ξ| ≤ 4 * ξ ^ 2 * (|θ (2 * ξ) - θ ξ| / ξ) + 4 * K * ξ ^ 3 := by linarith
    _ = ξ ^ 2 * (4 * (|θ (2 * ξ) - θ ξ| / ξ) + 4 * K * ξ) := by ring

/-- θ' tends to 0 at 0 from the right. -/
theorem tendsto_deriv_zero (θ θ' f : ℝ → ℝ) (b K : ℝ) (hb : 0 < b)
    (hθ : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt θ (θ' x) x)
    (hθ' : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt θ' (-(2 / x * θ' x) - f x) x)
    (hf : ∀ x ∈ Ioo (0 : ℝ) b, |f x| ≤ K) (hd0 : HasDerivWithinAt θ 0 (Ici 0) 0) :
    Tendsto θ' (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto (slope θ 0) (𝓝[>] 0) (𝓝 0) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
      (hd0.mono Ioi_subset_Ici_self)
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h2 : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hid.const_mul 2
      rwa [mul_zero] at this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos two_pos (show (0 : ℝ) < x from hx)
  have hs2 : Tendsto (fun x : ℝ => slope θ 0 (2 * x)) (𝓝[>] 0) (𝓝 0) := hs.comp h2
  have hA : Tendsto (fun x : ℝ => 4 * |2 * slope θ 0 (2 * x) - slope θ 0 x| + 4 * K * x)
      (𝓝[>] 0) (𝓝 0) := by
    have := ((((hs2.const_mul 2).sub hs).abs).const_mul 4).add (hid.const_mul (4 * K))
    rwa [show (4 : ℝ) * |2 * 0 - 0| + 4 * K * 0 = 0 by simp] at this
  refine squeeze_zero_norm' ?_ (hA.congr' ?_)
    (a := fun x => 4 * (|θ (2 * x) - θ x| / x) + 4 * K * x)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < b / 2 by linarith)] with x hx
    rw [Real.norm_eq_abs]
    exact key_bound θ θ' f b K hθ hθ' hf hx.1 (by linarith [hx.2])
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have e : 2 * slope θ 0 (2 * x) - slope θ 0 x = (θ (2 * x) - θ x) / x := by
      rw [slope_def_field, slope_def_field, sub_zero, sub_zero]
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hx0]

theorem blind_laneEmden92 (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 32))
    (h0 : θ 0 = 1)
    (hd0 : HasDerivWithinAt θ 0 (Set.Ici 0) 0)
    (hdiff : ∀ ξ ∈ Set.Ioo (0 : ℝ) 32, DifferentiableAt ℝ θ ξ ∧ DifferentiableAt ℝ (deriv θ) ξ)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 32,
      deriv (deriv θ) ξ + (2 / ξ) * deriv θ ξ + (θ ξ) ^ ((9 : ℝ) / 2) = 0) :
    ∃ ξ₁ : ℝ, IsLeast {ξ : ℝ | ξ ∈ Set.Icc (0 : ℝ) 32 ∧ θ ξ = 0} ξ₁ ∧
      (31.836463 ≤ ξ₁ ∧ ξ₁ ≤ 31.836464) ∧
      (1.7377988 ≤ -ξ₁ ^ 2 * deriv θ ξ₁ ∧ -ξ₁ ^ 2 * deriv θ ξ₁ ≤ 1.7377989) ∧
      (6189.4730 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ≤ 6189.4733) := by
  have hX : Icc (0 : ℝ) (796 / 25) ⊆ Icc 0 32 := Icc_subset_Icc le_rfl (by norm_num)
  obtain ⟨K, hK⟩ : ∃ K, ∀ x ∈ Icc (0 : ℝ) 32, ‖θ x ^ ((9 : ℝ) / 2)‖ ≤ K :=
    isCompact_Icc.exists_bound_of_continuousOn
      (hcont.rpow_const (fun _ _ => Or.inr (by norm_num)))
  set φ : ℝ → ℝ := fun x => if x = 0 then 0 else deriv θ x with hφ
  have hφx : ∀ x, x ≠ 0 → φ x = deriv θ x := fun x hx => by simp [hφ, hx]
  have hφ0v : φ 0 = 0 := by simp [hφ]
  have hθd : ∀ x ∈ Ioo (0 : ℝ) 32, HasDerivAt θ (φ x) x := fun x hx => by
    rw [hφx x hx.1.ne']; exact (hdiff x hx).1.hasDerivAt
  have hφd : ∀ x ∈ Ioo (0 : ℝ) 32,
      HasDerivAt φ (-(2 / x * φ x) - θ x ^ ((9 : ℝ) / 2)) x := by
    intro x hx
    have h2 := (hdiff x hx).2
    have h3 := hode x hx
    have heq : φ =ᶠ[𝓝 x] deriv θ := by
      filter_upwards [eventually_ne_nhds hx.1.ne'] with y hy using hφx y hy
    rw [hφx x hx.1.ne']
    have hv : deriv (deriv θ) x = -(2 / x * deriv θ x) - θ x ^ ((9 : ℝ) / 2) := by linarith
    rw [← hv]
    exact h2.hasDerivAt.congr_of_eventuallyEq heq
  have hlim : Tendsto φ (𝓝[>] 0) (𝓝 0) :=
    tendsto_deriv_zero θ φ (fun x => θ x ^ ((9 : ℝ) / 2)) 32 K (by norm_num) hθd hφd
      (fun x hx => by
        have := hK x (Ioo_subset_Icc_self hx)
        rwa [Real.norm_eq_abs] at this) hd0
  have hφ0 : ContinuousWithinAt φ (Icc 0 (796 / 25)) 0 := by
    have h1 : ContinuousWithinAt φ (Ioi 0) 0 := by
      rw [ContinuousWithinAt, hφ0v]; exact hlim
    exact (continuousWithinAt_Ioi_iff_Ici.mp h1).mono Icc_subset_Ici_self
  have hθ' : ∀ ξ ∈ Icc (0 : ℝ) (796 / 25),
      HasDerivWithinAt θ (φ ξ) (Icc 0 (796 / 25)) ξ := by
    intro ξ hξ
    rcases eq_or_lt_of_le hξ.1 with h | h
    · subst h
      rw [hφ0v]
      exact hd0.mono Icc_subset_Ici_self
    · exact (hθd ξ ⟨h, by linarith [hξ.2]⟩).hasDerivWithinAt
  have hφ' : ∀ ξ ∈ Ioc (0 : ℝ) (796 / 25),
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ ((9 : ℝ) / 2)) (Icc 0 (796 / 25)) ξ :=
    fun ξ hξ => (hφd ξ ⟨hξ.1, by linarith [hξ.2]⟩).hasDerivWithinAt
  obtain ⟨ξ₁, ha, hb, hz, hpos, hω1, hω2, hc1, hc2⟩ :=
    Work.Math.LaneEmden92.core θ φ hθ' hφ0 hφ' h0
  have hξ0 : 0 < ξ₁ := by linarith
  have en : -ξ₁ ^ 2 * deriv θ ξ₁ = -(ξ₁ ^ 2 * φ ξ₁) := by rw [hφx ξ₁ hξ0.ne']; ring
  refine ⟨ξ₁, ⟨⟨⟨hξ0.le, by linarith⟩, hz⟩, ?_⟩, ⟨ha, hb⟩, ?_, ?_⟩
  · rintro y ⟨⟨hy0, -⟩, hy⟩
    by_contra hlt
    exact (hpos y ⟨hy0, lt_of_not_ge hlt⟩).ne' hy
  · rw [en]; exact ⟨hω1, hω2⟩
  · rw [en]; exact ⟨hc1, hc2⟩

end Work.Math.LaneEmden92BlindClosed
