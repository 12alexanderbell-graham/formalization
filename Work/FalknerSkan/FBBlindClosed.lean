import Mathlib
import Work.FalknerSkan.FifthBounded

/-!
# Falkner–Skan β = 1/5, bounded class: the blind restatement, closed (run 2026-11-08T2028Z)

The definitions `IsSol`, `Bdd` and the three theorems are the blind restater's text (Sonnet, from the claims
in words only; `runs/2026-11-08T2028Z/blind/FSFifthBlind.lean`), copied verbatim with their placeholder
proofs replaced by proofs from `Work.FalknerSkan.FifthBounded`; `toSys` and `bddI` (program text) turn the
blind equation and class into the program's form.
-/

namespace Blind.FSFifth

open Filter Topology Set

/-- `IsSol f f1 f2 f3`: f, f1 = f', f2 = f'', f3 = f''' are explicit functions with
one-sided (within `Ici 0`) derivatives at every η ≥ 0, satisfying the Falkner–Skan ODE
with β = 1/5 and the boundary conditions. -/
def IsSol (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ η ∈ Ici (0:ℝ), HasDerivWithinAt f (f1 η) (Ici 0) η) ∧
  (∀ η ∈ Ici (0:ℝ), HasDerivWithinAt f1 (f2 η) (Ici 0) η) ∧
  (∀ η ∈ Ici (0:ℝ), HasDerivWithinAt f2 (f3 η) (Ici 0) η) ∧
  (∀ η ∈ Ici (0:ℝ), f3 η + f η * f2 η + (1/5 : ℝ) * (1 - (f1 η)^2) = 0) ∧
  f 0 = 0 ∧ f1 0 = 0 ∧ Tendsto f1 atTop (𝓝 1)

/-- velocity profile bounded in [-1,1] on [0,∞) -/
def Bdd (f1 : ℝ → ℝ) : Prop := ∀ η, 0 ≤ η → -1 ≤ f1 η ∧ f1 η ≤ 1

/-- From the blind `IsSol` to the program's first-order system (program lemma, not part of the blind text). -/
theorem toSys {f f1 f2 f3 : ℝ → ℝ} (h : IsSol f f1 f2 f3) :
    ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f2 (-(f x * f2 x) - 1 / 5 * (1 - f1 x ^ 2)) (Ici 0) x :=
  fun x hx => (h.2.2.1 x hx).congr_deriv (by linarith [h.2.2.2.1 x hx])

/-- The blind class in the program's form (program lemma). -/
theorem bddI {f1 : ℝ → ℝ} (hb : Bdd f1) : ∀ x ∈ Ici (0 : ℝ), -1 ≤ f1 x ∧ f1 x ≤ 1 :=
  fun x hx => hb x hx

theorem fs_W (f f1 f2 f3 : ℝ → ℝ) (h : IsSol f f1 f2 f3) (hb : Bdd f1) :
    (0.6867081809 : ℝ) < f2 0 ∧ f2 0 < 0.6867081811 := by
  exact Work.FalknerSkan.FifthBounded.fs_fifth_bounded_window f f1 f2 h.1 h.2.1 (toSys h)
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 (bddI hb)

theorem fs_U (f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ)
    (h : IsSol f f1 f2 f3) (hb : Bdd f1) (k : IsSol g g1 g2 g3) (kb : Bdd g1) :
    ∀ η, 0 ≤ η → f η = g η ∧ f1 η = g1 η ∧ f2 η = g2 η := by
  intro η hη
  exact Work.FalknerSkan.FifthBounded.fs_fifth_bounded_equal f f1 f2 g g1 g2 h.1 h.2.1 (toSys h)
    h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 (bddI hb) k.1 k.2.1 (toSys k)
    k.2.2.2.2.1 k.2.2.2.2.2.1 k.2.2.2.2.2.2 (bddI kb) η hη

theorem fs_E : ∃ f f1 f2 f3 : ℝ → ℝ, IsSol f f1 f2 f3 ∧
    (∀ η, 0 ≤ η → 0 ≤ f1 η ∧ f1 η < 1) ∧
    (0.6867081809 : ℝ) < f2 0 ∧ f2 0 < 0.6867081811 := by
  obtain ⟨f, p, q, hf, hp, hq, f0, p0, lim, hb, lo, hi⟩ :=
    Work.FalknerSkan.FifthBounded.fs_fifth_exists_bounded
  exact ⟨f, p, q, fun x => -(f x * q x) - 1 / 5 * (1 - p x ^ 2),
    ⟨hf, hp, hq, fun x _ => by ring, f0, p0, lim⟩, fun x hx => hb x hx, lo, hi⟩

end Blind.FSFifth
