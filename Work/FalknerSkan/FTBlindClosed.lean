import Mathlib
import Work.FalknerSkan.TenthBounded

/-!
# Falkner–Skan β = 1/10, bounded class: the blind restatement, closed (run 2026-11-08T2028Z)

The structure `IsSol` and the three theorems are the blind restater's text (Sonnet, from the claims in words
only; `runs/2026-11-08T2028Z/blind10/FSTenthBlind.lean`), copied verbatim with their placeholder proofs replaced by
proofs from `Work.FalknerSkan.TenthBounded`; `toSys` (program text) turns the blind equation into the program's
first-order system.
-/

namespace Blind.FSTenth

open Set Filter Topology

/-- `f` solves Falkner–Skan with `β = 1/10` on `[0,∞)`; `f1 f2 f3` are its first three
derivatives (one-sided at `0`, given explicitly to avoid junk values of `deriv`). -/
structure IsSol (f f1 f2 f3 : ℝ → ℝ) : Prop where
  d0 : ∀ η, 0 ≤ η → HasDerivWithinAt f (f1 η) (Ici 0) η
  d1 : ∀ η, 0 ≤ η → HasDerivWithinAt f1 (f2 η) (Ici 0) η
  d2 : ∀ η, 0 ≤ η → HasDerivWithinAt f2 (f3 η) (Ici 0) η
  ode : ∀ η, 0 ≤ η → f3 η + f η * f2 η + (1/10 : ℝ) * (1 - (f1 η)^2) = 0
  bc0 : f 0 = 0
  bc1 : f1 0 = 0
  bcInf : Tendsto f1 atTop (𝓝 1)

/-- From the blind `IsSol` to the program's first-order system (program lemma, not part of the blind text). -/
theorem toSys {f f1 f2 f3 : ℝ → ℝ} (h : IsSol f f1 f2 f3) :
    ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f2 (-(f x * f2 x) - 1 / 10 * (1 - f1 x ^ 2)) (Ici 0) x :=
  fun x hx => (h.d2 x hx).congr_deriv (by linarith [h.ode x hx])

theorem fs_W (f f1 f2 f3 : ℝ → ℝ) (h : IsSol f f1 f2 f3)
    (hb : ∀ η, 0 ≤ η → -1 ≤ f1 η ∧ f1 η ≤ 1) :
    (0.5870352191 : ℝ) < f2 0 ∧ f2 0 < 0.5870352193 := by
  exact Work.FalknerSkan.TenthBounded.fs_tenth_bounded_window f f1 f2 (fun x hx => h.d0 x hx)
    (fun x hx => h.d1 x hx) (toSys h) h.bc0 h.bc1 h.bcInf (fun x hx => hb x hx)

theorem fs_U (f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ)
    (h : IsSol f f1 f2 f3) (hg : IsSol g g1 g2 g3)
    (hb : ∀ η, 0 ≤ η → -1 ≤ f1 η ∧ f1 η ≤ 1)
    (hgb : ∀ η, 0 ≤ η → -1 ≤ g1 η ∧ g1 η ≤ 1) :
    ∀ η, 0 ≤ η → f η = g η ∧ f1 η = g1 η ∧ f2 η = g2 η := by
  intro η hη
  exact Work.FalknerSkan.TenthBounded.fs_tenth_bounded_equal f f1 f2 g g1 g2 (fun x hx => h.d0 x hx)
    (fun x hx => h.d1 x hx) (toSys h) h.bc0 h.bc1 h.bcInf (fun x hx => hb x hx)
    (fun x hx => hg.d0 x hx) (fun x hx => hg.d1 x hx) (toSys hg) hg.bc0 hg.bc1 hg.bcInf
    (fun x hx => hgb x hx) η hη

theorem fs_E : ∃ f f1 f2 f3 : ℝ → ℝ, IsSol f f1 f2 f3 ∧
    (∀ η, 0 ≤ η → 0 ≤ f1 η ∧ f1 η < 1) ∧
    (0.5870352191 : ℝ) < f2 0 ∧ f2 0 < 0.5870352193 := by
  obtain ⟨f, p, q, hf, hp, hq, f0, p0, lim, hb, lo, hi⟩ :=
    Work.FalknerSkan.TenthBounded.fs_tenth_exists_bounded
  exact ⟨f, p, q, fun x => -(f x * q x) - 1 / 10 * (1 - p x ^ 2),
    ⟨fun x hx => hf x hx, fun x hx => hp x hx, fun x hx => hq x hx, fun x _ => by ring, f0, p0, lim⟩,
    fun x hx => hb x hx, lo, hi⟩

end Blind.FSTenth
