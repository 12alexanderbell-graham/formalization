import Mathlib
import Work.Math.GelfandExtrema
import Work.Math.GelfandExtremaBlind

/-! Gelfand problem: the blind restatement `Work.Math.GelfandExtremaBlind.blind_gelfand_extrema`
(w C² on [0, ∞) as `ContDiffOn ℝ 2 w (Ici 0)`, w(0) = 0, one-sided derivative 0 at 0, the equation with
`deriv (deriv w)` for s > 0) closed from the frozen headline `Work.Math.GelfandExtrema.gelfand_extrema`
with φ the derivative of w within [0, ∞). Written by run 2026-11-15T1228Z. -/

namespace Work.Math.GelfandExtremaBlindClosed
open Set Filter Topology Work.Math.GelfandExtremaBlind

theorem blind_closed (w : ℝ → ℝ) (hw : IsRegularGelfandSolution w) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      (4.071496844 : ℝ) ≤ ζ 0 ∧ ζ 0 ≤ 4.071496845 ∧
      (3.321992118 : ℝ) ≤ gelfandLambda w (ζ 0) ∧
      gelfandLambda w (ζ 0) ≤ 3.321992119 ∧
      (∀ s : ℝ, 0 ≤ s → s ≠ ζ 0 → gelfandLambda w s < gelfandLambda w (ζ 0)) ∧
      (∀ k : ℕ, ∀ s : ℝ, ζ (2 * k) ≤ s → s ≠ ζ (2 * k + 1) →
        gelfandLambda w (ζ (2 * k + 1)) < gelfandLambda w s) ∧
      (∀ k : ℕ, ∀ s : ℝ, ζ (2 * k + 1) ≤ s → s ≠ ζ (2 * k + 2) →
        gelfandLambda w s < gelfandLambda w (ζ (2 * k + 2))) ∧
      (∀ k : ℕ, gelfandLambda w (ζ (2 * k + 1)) < 2 ∧ 2 < gelfandLambda w (ζ (2 * k))) ∧
      Tendsto (gelfandLambda w) atTop (nhds 2) ∧
      StrictMonoOn (gelfandLambda w) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (gelfandLambda w) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (gelfandLambda w) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) := by
  obtain ⟨hcd, h0, -, hode⟩ := hw
  set φ : ℝ → ℝ := derivWithin w (Ici 0) with hφdef
  have hdiff : DifferentiableOn ℝ w (Ici 0) := hcd.differentiableOn (by norm_num)
  have hW : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s :=
    fun s hs => (hdiff s hs).hasDerivWithinAt
  have hφc : ContinuousOn φ (Ici 0) :=
    hcd.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
  have hφ0 : ContinuousWithinAt φ (Ici 0) 0 := hφc 0 (le_refl (0 : ℝ))
  have hcdI : ContDiffOn ℝ 2 w (Ioi 0) := hcd.mono Ioi_subset_Ici_self
  have hd1 : ContDiffOn ℝ 1 (deriv w) (Ioi 0) := hcdI.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hΦ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have heq : ∀ t ∈ Ioi (0 : ℝ), φ t = deriv w t := fun t ht =>
      derivWithin_of_mem_nhds (Ici_mem_nhds ht)
    have hev : φ =ᶠ[𝓝 s] deriv w :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs') (fun t ht => heq t ht)
    have hdd : HasDerivAt (deriv w) (deriv (deriv w) s) s :=
      ((hd1.differentiableOn (by norm_num)) s hs).differentiableAt (Ioi_mem_nhds hs')
        |>.hasDerivAt
    have hval : deriv (deriv w) s = -(2 / s * φ s) - Real.exp (w s) := by
      have := hode s hs'
      rw [heq s hs]
      linarith
    rw [← hval]
    exact (hdd.congr_of_eventuallyEq hev).hasDerivWithinAt
  obtain ⟨ζ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    Work.Math.GelfandExtrema.gelfand_extrema w φ hW hφ0 hΦ h0
  refine ⟨ζ, h1, h2, h3, h4, h5, h6, fun s hs hne => h7 s hs hne, fun k s hs hne => h8 k s hs hne,
    fun k s hs hne => h9 k s hs hne, h10, h11, h12, h13, h14⟩

end Work.Math.GelfandExtremaBlindClosed
