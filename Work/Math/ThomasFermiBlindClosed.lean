import Mathlib
import Work.Math.ThomasFermi

/-! Audit of `Work.Math.ThomasFermi.tf_initial_slope`: the blind restatement
(`Work.Math.ThomasFermiBlind.thomas_fermi_initial_slope`: second derivative as `deriv (deriv y)`,
y continuous on [0, ∞), slope as a right derivative `d` at 0, no continuity hypothesis on y'
at 0) proved from the frozen headline. The headline's hypothesis that y' is continuous at 0 from
the right is derived here (`deriv_tendsto`): y' is monotone on (0, ∞) and squeezed between
difference quotients at 0. -/

namespace Work.Math.ThomasFermiBlindClosed
open Set Filter Topology

/-- y' tends to the right derivative d at 0 (within (0, ∞)). -/
theorem deriv_near (y : ℝ → ℝ) (d : ℝ)
    (hcont : ContinuousOn y (Ici 0))
    (hdiff1 : DifferentiableOn ℝ y (Ioi 0))
    (hmono : MonotoneOn (deriv y) (Ioi 0))
    (hd : HasDerivWithinAt y d (Ici 0) 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ u, 0 < u → u < δ → |deriv y u - d| < ε := by
  intro ε hε
  have hs := hasDerivWithinAt_iff_tendsto_slope.1 hd
  have hev : ∀ᶠ x in 𝓝[Ici 0 \ {0}] (0 : ℝ), |slope y 0 x - d| < ε := by
    have := (hs.eventually (Metric.ball_mem_nhds d hε))
    filter_upwards [this] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  obtain ⟨δ0, hδ0, hδ⟩ := Metric.mem_nhdsWithin_iff.1 hev
  -- slope bound at every 0 < x < δ0
  have hsl : ∀ x, 0 < x → x < δ0 → |(y x - y 0) / x - d| < ε := by
    intro x hx hxd
    have h1 : |slope y 0 x - d| < ε := hδ ⟨show dist x 0 < δ0 by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx]; exact hxd, ⟨le_of_lt hx, ne_of_gt hx⟩⟩
    simpa [slope_def_field, div_eq_mul_inv, mul_comm] using h1
  -- MVT on [0, x]
  have hmvt : ∀ x, 0 < x → ∃ ξ ∈ Ioo 0 x, deriv y ξ = (y x - y 0) / x := by
    intro x hx
    obtain ⟨ξ, hξ, he⟩ := exists_deriv_eq_slope y hx
      (hcont.mono Icc_subset_Ici_self)
      (hdiff1.mono fun t ht => ht.1)
    exact ⟨ξ, hξ, by rw [he, sub_zero]⟩
  obtain ⟨ξ, hξ, hξe⟩ := hmvt (δ0 / 2) (by linarith)
  refine ⟨ξ, hξ.1, fun u hu huξ => ?_⟩
  have hup : deriv y u ≤ deriv y ξ := hmono hu hξ.1 huξ.le
  have hupb := hsl (δ0 / 2) (by linarith) (by linarith)
  obtain ⟨η, hη, hηe⟩ := hmvt u hu
  have hlo : deriv y η ≤ deriv y u := hmono hη.1 hu hη.2.le
  have hlob := hsl u hu (by linarith [hξ.2])
  rw [abs_lt] at hupb hlob ⊢
  constructor <;> linarith

theorem blind_closed (y : ℝ → ℝ) (d : ℝ)
    (hcont : ContinuousOn y (Ici 0))
    (hpos : ∀ x, 0 ≤ x → 0 < y x)
    (hdiff1 : DifferentiableOn ℝ y (Ioi 0))
    (hdiff2 : DifferentiableOn ℝ (deriv y) (Ioi 0))
    (hode : ∀ x, 0 < x → deriv (deriv y) x = (y x) ^ ((3 : ℝ) / 2) / Real.sqrt x)
    (h0 : y 0 = 1)
    (hinf : Tendsto y atTop (𝓝 0))
    (hd : HasDerivWithinAt y d (Ici 0) 0) :
    (-1.58807103 : ℝ) ≤ d ∧ d ≤ -1.58807102 := by
  have hda : ∀ x, 0 < x → HasDerivAt y (deriv y x) x := fun x hx =>
    (hdiff1.differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
  have hdda : ∀ x, 0 < x → HasDerivAt (deriv y) (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x :=
    fun x hx => by
      rw [← hode x hx]
      exact (hdiff2.differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
  have hmono : MonotoneOn (deriv y) (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) hdiff2.continuousOn ?_ ?_
    · rw [interior_Ioi]; exact hdiff2
    · intro x hx
      rw [interior_Ioi] at hx
      rw [hode x hx]
      exact div_nonneg (Real.rpow_nonneg (hpos x (le_of_lt hx)).le _) (Real.sqrt_nonneg _)
  set φ : ℝ → ℝ := Function.update (deriv y) 0 d with hφdef
  have hφx : ∀ x, x ≠ 0 → φ x = deriv y x := fun x hx => Function.update_of_ne hx _ _
  have hφ0' : φ 0 = d := Function.update_self _ _ _
  have hy : ∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x := by
    intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · rw [← h, hφ0']; exact hd
    · rw [hφx x (ne_of_gt h)]; exact (hda x h).hasDerivWithinAt
  have hφ : ∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x := by
    intro x hx
    refine (hdda x hx).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact hφx t (ne_of_gt ht)
  have hφc : ContinuousWithinAt φ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := deriv_near y d hcont hdiff1 hmono hd ε hε
    refine ⟨δ, hδ, fun u hu hud => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ u from hu)] at hud
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ u from hu) with h | h
    · rw [← h, Real.dist_eq, sub_self, abs_zero]; exact hε
    · rw [Real.dist_eq, hφx u (ne_of_gt h), hφ0']; exact hb u h hud
  have := Work.Math.ThomasFermi.tf_initial_slope y φ hy hφ hφc h0 hpos hinf
  rw [hφ0'] at this
  exact this

end Work.Math.ThomasFermiBlindClosed
