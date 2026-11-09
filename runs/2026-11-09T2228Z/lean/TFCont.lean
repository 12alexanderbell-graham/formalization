import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.FunProp

open Set Filter Topology

namespace Scratch.TF

/-- Thomas–Fermi form: if y is differentiable on `[0, ∞)` with derivative φ, y > 0, and
φ' = y^{3/2}/√x for x > 0, then φ is right-continuous at 0. -/
theorem tf_cont (y φ : ℝ → ℝ)
    (hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x)
    (hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x)
    (hpos : ∀ x, 0 ≤ x → 0 < y x) :
    ContinuousWithinAt φ (Ici 0) 0 := by
  -- bound of y^{3/2} on [0, 1]
  have hyc : ContinuousOn y (Icc 0 1) := fun x hx =>
    ((hy x hx.1).continuousWithinAt).mono Icc_subset_Ici_self
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hyc
  set K := B ^ ((3 : ℝ) / 2) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)) _
  have hyK : ∀ x ∈ Icc (0 : ℝ) 1, y x ^ ((3 : ℝ) / 2) ≤ K := fun x hx => by
    have h := hB x hx
    rw [Real.norm_eq_abs, abs_of_pos (hpos x hx.1)] at h
    exact Real.rpow_le_rpow (hpos x hx.1).le h (by norm_num)
  -- φ is monotone on (0, ∞)
  have hmono : MonotoneOn φ (Ioi 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => y x ^ ((3 : ℝ) / 2) / Real.sqrt x) (convex_Ioi 0)
      (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioi] at hx; exact (hφ x hx).hasDerivWithinAt
    · rw [interior_Ioi] at hx
      exact div_nonneg (Real.rpow_nonneg (hpos x (le_of_lt hx)).le _) (Real.sqrt_nonneg _)
  -- φ − 2K√x is antitone on (0, 1)
  have hanti : AntitoneOn (fun x => φ x - 2 * K * Real.sqrt x) (Ioo 0 1) := by
    have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => φ x - 2 * K * Real.sqrt x)
        (y x ^ ((3 : ℝ) / 2) / Real.sqrt x - 2 * K * (1 / (2 * Real.sqrt x))) x := fun x hx =>
      (hφ x hx.1).sub ((Real.hasDerivAt_sqrt hx.1.ne').const_mul _)
    refine antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun x => y x ^ ((3 : ℝ) / 2) / Real.sqrt x - 2 * K * (1 / (2 * Real.sqrt x))) (convex_Ioo 0 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioo] at hx; exact (hd x hx).hasDerivWithinAt
    · rw [interior_Ioo] at hx
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
      have := hyK x ⟨hx.1.le, hx.2.le⟩
      rw [show 2 * K * (1 / (2 * Real.sqrt x)) = K / Real.sqrt x by field_simp, ← sub_div]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le
  -- the two-sided squeeze: for 0 < a ≤ b < 1, 0 ≤ φ b − φ a ≤ 2K√b
  have hsq : ∀ a b, 0 < a → a ≤ b → b < 1 → |φ b - φ a| ≤ 2 * K * Real.sqrt b := by
    intro a b ha hab hb1
    have h1 := hmono (mem_Ioi.2 ha) (mem_Ioi.2 (ha.trans_le hab)) hab
    have h2 := hanti ⟨ha, hab.trans_lt hb1⟩ ⟨ha.trans_le hab, hb1⟩ hab
    simp only at h2
    rw [abs_of_nonneg (sub_nonneg.2 h1)]
    have := Real.sqrt_nonneg a
    nlinarith
  -- slope of y at 0 tends to φ 0
  have hslope : Tendsto (fun x => (y x - y 0) / x) (𝓝[>] 0) (𝓝 (φ 0)) := by
    have h := (hasDerivWithinAt_iff_tendsto_slope.1 (hy 0 le_rfl))
    rw [show Ici (0 : ℝ) \ {0} = Ioi 0 by ext x; simp [lt_iff_le_and_ne, eq_comm]] at h
    refine h.congr (fun x => ?_)
    simp [slope_def_field]
  -- |φ x − slope x| ≤ 2K√x for 0 < x < 1 (mean value theorem)
  have hclose : ∀ x, 0 < x → x < 1 → |φ x - (y x - y 0) / x| ≤ 2 * K * Real.sqrt x := by
    intro x hx hx1
    have hcont : ContinuousOn y (Icc 0 x) := fun z hz =>
      ((hy z hz.1).continuousWithinAt).mono (fun w hw => (mem_Ici.2 hw.1))
    have hder : ∀ z ∈ Ioo 0 x, HasDerivAt y (φ z) z := fun z hz =>
      (hy z hz.1.le).hasDerivAt (Ici_mem_nhds hz.1)
    obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope y φ hx hcont hder
    rw [sub_zero] at hζeq
    rw [← hζeq]
    exact hsq ζ x hζ.1 hζ.2.le hx1
  -- conclude
  rw [← Ioi_insert, continuousWithinAt_insert_self]
  show Tendsto φ (𝓝[>] 0) (𝓝 (φ 0))
  have hlim0 : Tendsto (fun x => 2 * K * Real.sqrt x) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun x => 2 * K * Real.sqrt x) (𝓝 0) (𝓝 (2 * K * Real.sqrt 0)) :=
      ((show Continuous fun x => 2 * K * Real.sqrt x by fun_prop).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun x => φ x - (y x - y 0) / x) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [Real.norm_eq_abs]
    exact hclose x hx.1 hx.2
  have := hdiff.add hslope
  simpa using this

end Scratch.TF
