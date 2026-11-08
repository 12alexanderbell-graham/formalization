import Mathlib
import Work.FalknerSkan.HalfBounded

/-!
# Falkner–Skan β = 1/2, bounded class: the blind restatement, closed (run 2026-11-08T1628Z)

The structure `IsSol` and the three theorems are the blind restater's text (Sonnet, from the claims
in words only; `runs/2026-11-08T1628Z/blind/FSBlind.lean`), copied verbatim with their placeholder
proofs replaced by proofs from the program's `Work.FalknerSkan.HalfBounded` headlines; `toSys`
(program text) turns the blind equation for the third derivative into the program's first-order
system.
-/

namespace Blind.FSHalf

open Set Filter Topology

/-- `f, f1, f2, f3` : `f1 = f'`, `f2 = f''`, `f3 = f'''` on `[0,∞)` (one-sided derivatives at 0). -/
structure IsSol (f f1 f2 f3 : ℝ → ℝ) : Prop where
  d0 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f (f1 x) (Ici 0) x
  d1 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f1 (f2 x) (Ici 0) x
  d2 : ∀ x ∈ Ici (0:ℝ), HasDerivWithinAt f2 (f3 x) (Ici 0) x
  ode : ∀ x ∈ Ici (0:ℝ), f3 x + f x * f2 x + (1/2) * (1 - (f1 x)^2) = 0
  bc0 : f 0 = 0
  bc1 : f1 0 = 0
  bcinf : Tendsto f1 atTop (𝓝 1)

/-- From the blind `IsSol` to the program's first-order system (program lemma, not part of the
blind text). -/
theorem toSys {f f1 f2 f3 : ℝ → ℝ} (h : IsSol f f1 f2 f3) :
    ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f2 (-(f x * f2 x) - 1 / 2 * (1 - f1 x ^ 2)) (Ici 0) x :=
  fun x hx => (h.d2 x hx).congr_deriv (by linarith [h.ode x hx])

theorem fs_W (f f1 f2 f3 : ℝ → ℝ) (h : IsSol f f1 f2 f3)
    (hb : ∀ x ∈ Ici (0:ℝ), -1 ≤ f1 x ∧ f1 x ≤ 1) :
    (0.927680039 : ℝ) < f2 0 ∧ f2 0 < 0.927680040 := by
  exact Work.FalknerSkan.HalfBounded.fs_half_bounded_window f f1 f2 h.d0 h.d1 (toSys h)
    h.bc0 h.bc1 h.bcinf hb

theorem fs_U (f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ)
    (h : IsSol f f1 f2 f3) (h' : IsSol g g1 g2 g3)
    (hb : ∀ x ∈ Ici (0:ℝ), -1 ≤ f1 x ∧ f1 x ≤ 1)
    (hb' : ∀ x ∈ Ici (0:ℝ), -1 ≤ g1 x ∧ g1 x ≤ 1) :
    ∀ x ∈ Ici (0:ℝ), f x = g x ∧ f1 x = g1 x ∧ f2 x = g2 x := by
  exact Work.FalknerSkan.HalfBounded.fs_half_bounded_equal f f1 f2 g g1 g2 h.d0 h.d1 (toSys h)
    h.bc0 h.bc1 h.bcinf hb h'.d0 h'.d1 (toSys h') h'.bc0 h'.bc1 h'.bcinf hb'

theorem fs_E : ∃ f f1 f2 f3 : ℝ → ℝ, IsSol f f1 f2 f3 ∧
    (∀ x ∈ Ici (0:ℝ), 0 ≤ f1 x ∧ f1 x < 1) ∧
    (0.927680039 : ℝ) < f2 0 ∧ f2 0 < 0.927680040 := by
  obtain ⟨f, p, q, hf, hp, hq, f0, p0, lim, hb, lo, hi⟩ :=
    Work.FalknerSkan.HalfBounded.fs_half_exists_bounded
  exact ⟨f, p, q, fun x => -(f x * q x) - 1 / 2 * (1 - p x ^ 2),
    ⟨hf, hp, hq, fun x _ => by ring, f0, p0, lim⟩, hb, lo, hi⟩

end Blind.FSHalf
