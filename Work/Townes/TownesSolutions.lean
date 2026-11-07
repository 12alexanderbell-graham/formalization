import Mathlib
import Work.Townes.TExAssemble

/-!
# Townes radial equation: solutions of the initial-value problem exist for every central value
# in [2.2, 2.21] (non-vacuity of the shooting statements; run 2026-11-07T0628Z)

The hypotheses of `Work.Townes.Shooting.townes_under` / `townes_over` (θ differentiable on [0, S]
with derivative φ, φ continuous at 0, φ' = −(1/r)φ + θ − θ³ on (0, S], θ(0) = c) are satisfiable:
for every c ∈ [2.2, 2.21] and every S > 1/5 the singular start of `Work.Townes.TExLeft.left`
glued to the clamped flow of `Work.Townes.TExFlow.exists_flow` (clamps inactive by
`TExFlow.bounds`) is such a pair. In particular both shooting statements are about solutions that
exist (c = 2.2062008646 and c = 2.2062008647 lie in [2.2, 2.21]); this is the non-vacuity witness
needed when they are promoted.
-/

namespace Work.Townes.Solutions
open Set

/-- Townes radial equation, initial-value problem at the singular point: for every c in
[2.2, 2.21] and every S > 1/5 there are θ, φ with θ differentiable on [0, S] with derivative φ,
φ continuous at 0, φ' = −(1/r)φ + θ − θ³ on (0, S] and θ(0) = c. -/
theorem ivp_exists (c : ℝ) (hc : c ∈ Icc (2.2 : ℝ) 2.21) (S : ℝ) (hS : 1 / 5 < S) :
    ∃ θ φ : ℝ → ℝ,
      (∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r) ∧
      ContinuousWithinAt φ (Icc 0 S) 0 ∧
      (∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r) ∧
      θ 0 = c := by
  obtain ⟨Θ, Φ, hL, -⟩ := TExLeft.left
  obtain ⟨α, hα, -⟩ := TExFlow.exists_flow S hS
  obtain ⟨h0, hΦ0, hdΘ, hcΦ, hdΦ, hΘb, -, hΦb⟩ := hL c hc
  have m15 : (1 / 5 : ℝ) ∈ Icc (0 : ℝ) (1 / 5) := ⟨by norm_num, le_rfl⟩
  set p : ℝ × ℝ := (Θ c (1 / 5), Φ c (1 / 5)) with hp
  have hp1 : |p.1| ≤ 5 / 2 := by
    have := hΘb _ m15
    rw [abs_le]; constructor <;> simp only [hp] <;> linarith [this.1, this.2]
  have hp2 : |p.2| ≤ 3 := hΦb _ m15
  have hpball : p ∈ Metric.closedBall (0 : ℝ × ℝ) 3 := by
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (hp1.trans (by norm_num)) hp2
  obtain ⟨hα0, hαd⟩ := hα p hpball
  have hbd := TExFlow.bounds (α p) hαd (by rw [hα0]; exact hp1) (by rw [hα0]; exact hp2)
  have hderR : ∀ t ∈ Icc (1 / 5 : ℝ) S,
      HasDerivWithinAt (fun r => (α p r).1) (α p t).2 (Icc (1 / 5) S) t ∧
      HasDerivWithinAt (fun r => (α p r).2)
        (-(1 / t * (α p t).2) + (α p t).1 - (α p t).1 ^ 3) (Icc (1 / 5) S) t := by
    intro t ht
    have hd := hαd t ht
    rw [TExFlow.F_eq ht.1 (hbd t ht).1 (hbd t ht).2] at hd
    exact ⟨TExFlow.fst_derivW hd, TExFlow.snd_derivW hd⟩
  have e1 : Θ c (1 / 5) = (α p (1 / 5)).1 := by rw [hα0]
  have e2 : Φ c (1 / 5) = (α p (1 / 5)).2 := by rw [hα0]
  set θ : ℝ → ℝ := fun t => if t ≤ 1 / 5 then Θ c t else (α p t).1 with hθ
  set φ : ℝ → ℝ := fun t => if t ≤ 1 / 5 then Φ c t else (α p t).2 with hφ
  have φL : ∀ t, t ≤ 1 / 5 → φ t = Φ c t := fun t ht => by simp only [hφ, if_pos ht]
  have θL : ∀ t, t ≤ 1 / 5 → θ t = Θ c t := fun t ht => by simp only [hθ, if_pos ht]
  have φR : ∀ t, 1 / 5 ≤ t → φ t = (α p t).2 := by
    intro t ht
    rcases ht.lt_or_eq with h | h
    · simp only [hφ, if_neg (not_le.2 h)]
    · subst h; rw [φL _ le_rfl, e2]
  have θR : ∀ t, 1 / 5 ≤ t → θ t = (α p t).1 := by
    intro t ht
    rcases ht.lt_or_eq with h | h
    · simp only [hθ, if_neg (not_le.2 h)]
    · subst h; rw [θL _ le_rfl, e1]
  refine ⟨θ, φ, fun t ht => ?_, ?_, fun t ht => ?_, by rw [θL 0 (by norm_num)]; exact h0⟩
  · refine TExAssemble.glue e1 ht (fun h => ?_) (fun h => ?_)
    · rw [φL t h]; exact hdΘ t ⟨ht.1, h⟩
    · rw [φR t h]; exact (hderR t ⟨h, ht.2⟩).1
  · have h1 : ContinuousWithinAt (Φ c) (Icc 0 (1 / 5)) 0 := hcΦ 0 ⟨le_rfl, by norm_num⟩
    have h2 : ContinuousWithinAt φ (Icc 0 (1 / 5)) 0 :=
      h1.congr (fun t ht => φL t ht.2) (φL 0 (by norm_num))
    refine h2.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Iio (1 / 5), isOpen_Iio, by norm_num, fun t ht => ⟨ht.2.1, ht.1.le⟩⟩
  · have hg := TExAssemble.glue (fL := Φ c) (fR := fun r => (α p r).2)
      (d := -(1 / t * φ t) + θ t - θ t ^ 3) e2 ⟨ht.1.le, ht.2⟩ (fun h => ?_) (fun h => ?_)
    · exact hg
    · rw [φL t h, θL t h]; exact hdΦ t ⟨ht.1, h⟩
    · rw [φR t h, θR t h]; exact (hderR t ⟨h, ht.2⟩).2

end Work.Townes.Solutions
