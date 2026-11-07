import Mathlib

open Filter Topology Set

/-- `f, f1, f2, f3` with `f' = f1`, `f1' = f2`, `f2' = f3` (one-sided at endpoints) on `S`,
satisfying the Hiemenz equation `f''' + f f'' + 1 - (f')^2 = 0` on `S`. -/
def HiemenzODE (S : Set ℝ) (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ t ∈ S, HasDerivWithinAt f (f1 t) S t) ∧
  (∀ t ∈ S, HasDerivWithinAt f1 (f2 t) S t) ∧
  (∀ t ∈ S, HasDerivWithinAt f2 (f3 t) S t) ∧
  (∀ t ∈ S, f3 t + f t * f2 t + 1 - (f1 t) ^ 2 = 0)

theorem blind_under (f f1 f2 f3 : ℝ → ℝ)
    (h : HiemenzODE (Icc 0 7.5) f f1 f2 f3)
    (h0 : f 0 = 0) (h1 : f1 0 = 0) (h2 : f2 0 = 1.2325876568) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 7.5 ∧ f2 η < 0 ∧ ∀ s ∈ Icc 0 η, f1 s < 1 := by
  sorry

theorem blind_over (f f1 f2 f3 : ℝ → ℝ)
    (h : HiemenzODE (Icc 0 7.5) f f1 f2 f3)
    (h0 : f 0 = 0) (h1 : f1 0 = 0) (h2 : f2 0 = 1.2325876569) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 7.5 ∧ 1 < f1 η ∧ ∀ s ∈ Icc 0 η, 0 < f2 s := by
  sorry

theorem blind_exists :
    ∃ f f1 f2 f3 : ℝ → ℝ, HiemenzODE (Ici 0) f f1 f2 f3 ∧
      f 0 = 0 ∧ f1 0 = 0 ∧ Tendsto f1 atTop (𝓝 1) ∧
      (1.2325876568 : ℝ) < f2 0 ∧ f2 0 < 1.2325876569 := by
  sorry
