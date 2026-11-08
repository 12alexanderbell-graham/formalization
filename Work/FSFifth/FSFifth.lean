import Mathlib
import Work.FSFifth.F5UData
import Work.FSFifth.F5OData
import Work.FSFifth.F5ExAssemble

/-!
# Falkner–Skan β = 1/5 in scaled form: two shooting events and existence (run 2026-11-08T2028Z)

The Falkner–Skan equation f''' + f f'' + β (1 − f'²) = 0 becomes F''' + (1/β) F F'' + 1 − F'² = 0
under F(s) = c f(s/c) with c = √β (`Checked.FalknerSkan.FSScale.scale`); for β = 1/5 the coefficient
is 5. This module is the Homann stack (coefficient 2, `Work.Homann`) ported to the coefficient 5 by
`runs/2026-11-08T2028Z/scripts/port_k.py`, with cells from `gen_k_w.py`/`gen_k_wc.py` (FS_K = 5):
* `k5_under`: started with q(0) = 1.5355261734, every solution on [0, S] (S ≥ 4) has a point
  η ∈ (0, 4] where q(η) < 0 while p < 1 on [0, η];
* `k5_over`: started with q(0) = 1.5355261735, every solution has a point η ∈ (0, 4] where
  p(η) > 1 while q > 0 on [0, η];
* `k5_exists`: a solution on [0, ∞) of the boundary-value problem with 1.5355261734 < F''(0) < 1.5355261735.
These are tools for the frozen Falkner–Skan β = 1/5 statements of `Work.FalknerSkan.FifthBounded`.
-/

namespace Work.FSFifth
open Set Filter Topology

/-- Falkner–Skan β = 1/5 in scaled form (coefficient 5), undershoot: for every S ≥ 4 and every solution of
f''' + 5 f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−5 f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.5355261734, there is
η in (0, 4] with q(η) < 0 and p < 1 on [0, η]. -/
theorem k5_under (S : ℝ) (hS : 4 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(5 * f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.5355261734) :
    ∃ η ∈ Ioc (0 : ℝ) 4, q η < 0 ∧ ∀ s ∈ Icc 0 η, p s < 1 := by
  have hsub : Icc (0 : ℝ) 4 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hq', hp'⟩ := Work.FSFifth.F5UData.chain (g := f) (p := p) (q := q)
    (fun t ht => (hf t (hsub ht)).mono hsub) (fun t ht => (hp t (hsub ht)).mono hsub)
    (fun t ht => (hq t (hsub ht)).mono hsub) hf0 hp0 hq0
  exact ⟨4, ⟨by norm_num, le_rfl⟩, hq', hp'⟩

/-- Falkner–Skan β = 1/5 in scaled form (coefficient 5), overshoot: for every S ≥ 4 and every solution of
f''' + 5 f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−5 f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.5355261735, there is
η in (0, 4] with p(η) > 1 and q > 0 on [0, η]. -/
theorem k5_over (S : ℝ) (hS : 4 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(5 * f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.5355261735) :
    ∃ η ∈ Ioc (0 : ℝ) 4, 1 < p η ∧ ∀ s ∈ Icc 0 η, 0 < q s := by
  have hsub : Icc (0 : ℝ) 4 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hp', hq'⟩ := Work.FSFifth.F5OData.chain (g := f) (p := p) (q := q)
    (fun t ht => (hf t (hsub ht)).mono hsub) (fun t ht => (hp t (hsub ht)).mono hsub)
    (fun t ht => (hq t (hsub ht)).mono hsub) hf0 hp0 hq0
  exact ⟨4, ⟨by norm_num, le_rfl⟩, hp', hq'⟩

/-- Falkner–Skan β = 1/5 in scaled form (coefficient 5), existence: there is a solution of
f''' + 5 f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has derivative q, q has derivative
−5 f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ whose wall value
q(0) = f''(0) lies strictly between 1.5355261734 and 1.5355261735. -/
theorem k5_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(5 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.5355261734 < q 0 ∧ q 0 < 1.5355261735 :=
  Work.FSFifth.F5ExAssemble.exists_bvp

end Work.FSFifth
