import Mathlib

/-!
# Scratch (run 2026-11-08T1228Z, auditor role while run 1028Z holds the LOCK)

From the class "f'' > 0 on [0, ∞)" to the class "−1 < f' < 1 on [0, ∞)" (Coppel's class
0 ≤ f' < 1 is inside it). For f''' + k f f'' + 1 − f'² = 0 written as f' = p, p' = q,
q' = −k f q − 1 + p², any solution with p → 1 and |p| < 1 on [0, ∞) has q > 0 on [0, ∞).

Argument: at a zero of q the equation gives q' = −1 + p² < 0, so q can only cross zero
downwards (fencing theorem with the barrier 0). If q(η₀) ≤ 0 for some η₀ ≥ 0, then q ≤ 0 on
[η₀, ∞), p is non-increasing there, p ≤ p(η₀) < 1, and p cannot tend to 1. Neither k nor the
boundary values f(0), p(0) are used.
-/

namespace Scratch1228
open Set Filter Topology

/-- q has a right derivative on [0, ∞) whose value is negative wherever q vanishes: once
q ≤ 0, it stays ≤ 0. -/
theorem stays_nonpos {q q' : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (q' η) (Ici 0) η)
    (hz : ∀ η ∈ Ici (0 : ℝ), q η = 0 → q' η < 0)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (hle : q η₀ ≤ 0) : ∀ η, η₀ ≤ η → q η ≤ 0 := by
  intro η hη
  have hcont : ContinuousOn q (Icc η₀ η) := fun x hx =>
    ((hq x (h0.trans hx.1)).continuousWithinAt).mono (fun y hy => h0.trans hy.1)
  have hder : ∀ x ∈ Ico η₀ η, HasDerivWithinAt q (q' x) (Ici x) x := fun x hx =>
    (hq x (h0.trans hx.1)).mono (fun y hy => h0.trans (hx.1.trans hy))
  have := image_le_of_deriv_right_lt_deriv_boundary' (B := fun _ => (0 : ℝ))
    (B' := fun _ => (0 : ℝ)) hcont hder hle continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hqx => hz x (h0.trans hx.1) hqx)
  exact this ⟨hη, le_rfl⟩

/-- p has right derivative q ≤ 0 on [η₀, ∞): p is not larger than p(η₀) there. -/
theorem le_start {p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    {η₀ : ℝ} (h0 : 0 ≤ η₀) (hneg : ∀ η, η₀ ≤ η → q η ≤ 0) :
    ∀ η, η₀ ≤ η → p η ≤ p η₀ := by
  intro η hη
  have hcont : ContinuousOn p (Icc η₀ η) := fun x hx =>
    ((hp x (h0.trans hx.1)).continuousWithinAt).mono (fun y hy => h0.trans hy.1)
  have hder : ∀ x ∈ Ico η₀ η, HasDerivWithinAt p (q x) (Ici x) x := fun x hx =>
    (hp x (h0.trans hx.1)).mono (fun y hy => h0.trans (hx.1.trans hy))
  have := image_le_of_deriv_right_le_deriv_boundary (B := fun _ => p η₀)
    (B' := fun _ => (0 : ℝ)) hcont hder le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx => hneg x hx.1)
  exact this ⟨hη, le_rfl⟩

/-- Falkner–Skan-type system f' = p, p' = q, q' = −k f q − 1 + p² (any real k): a solution with
p → 1 and −1 < p < 1 on [0, ∞) has q > 0 on [0, ∞). -/
theorem pos_of_abs_lt_one {k : ℝ} {f p q : ℝ → ℝ}
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 < p η ∧ p η < 1) :
    ∀ η ∈ Ici (0 : ℝ), 0 < q η := by
  intro η₀ hη₀
  have h0 : (0 : ℝ) ≤ η₀ := hη₀
  by_contra hcon
  have hle : q η₀ ≤ 0 := not_lt.1 hcon
  have hz : ∀ η ∈ Ici (0 : ℝ), q η = 0 → -(k * f η * q η) - 1 + p η ^ 2 < 0 := by
    intro η hη hqη
    obtain ⟨h1, h2⟩ := hb η hη
    rw [hqη]
    nlinarith
  have hneg := stays_nonpos hq hz h0 hle
  have hpl := le_start hp h0 hneg
  have hlt1 : p η₀ < 1 := (hb η₀ hη₀).2
  have hev : ∀ᶠ η in atTop, p η₀ < p η :=
    hlim.eventually (lt_mem_nhds hlt1)
  obtain ⟨η, hη⟩ := (hev.and (eventually_ge_atTop η₀)).exists
  exact absurd (hpl η hη.2) (not_le.2 hη.1)

end Scratch1228
