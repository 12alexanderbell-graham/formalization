import Mathlib

/-!
# Falkner–Skan at β = −0.1988: the reversed-flow branch (FROZEN, run 2026-11-11T1228Z; proofs pending)

Parts 2/5. Written in `runs/2026-11-11T1228Z/lean/` (auditor role under the LOCK of run 0828Z); to move to
`Work/FalknerSkan/Neg1988Rev.lean` unchanged when the LOCK is released.

Fazio (2012, arXiv:1212.5057v1, typeset p. 16, read blind in run 1028Z) prints for β = −0.1988 the attached
wall shear 0.005221 and the reversed-flow wall shear −0.005158. Independent numerics: run 1028Z referee
(collocation with the parabolic-cylinder tail) −0.0051574; this run (mpmath Taylor shooting, scaled
K = 2500/497) −0.00515742018. The printed reversed value is off in the fourth significant digit.

Statements: `fs_neg1988_reversed` is `Work.FalknerSkan.NegReversed.fs_neg_tenth_reversed` with
β = −1988/10000 and the window (−0.00515743, −0.00515741); `fs_neg1988_printed_reversed_overshoots`
says that the initial-value problem with Fazio's printed reversed wall value overshoots (f' > 1 somewhere),
so that value is the wall shear of no solution with f' ≤ 1 (both branches have f' ≤ 1);
`fs_neg1988_two_decay` is `fs_neg_tenth_two_decay` with β = −1988/10000 (non-uniqueness in the decay class
just above separation). Do not change them; prove them.
-/

namespace Work.FalknerSkan.Neg1988Rev

open Set Filter Topology

/-- Falkner–Skan with β = −1988/10000: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, whose wall value satisfies −0.00515743 < q(0) < −0.00515741 (reversed flow at the wall). -/
theorem fs_neg1988_reversed :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.00515743 < q 0 ∧ q 0 < -0.00515741 := by
  sorry

/-- Falkner–Skan with β = −1988/10000, the printed reversed-flow wall value: every solution (f, p, q) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0, p(0) = 0 and q(0) = −0.005158 has p(η) > 1 at
some η > 0. -/
theorem fs_neg1988_printed_reversed_overshoots (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = -0.005158) :
    ∃ η > 0, 1 < p η := by
  sorry

/-- Falkner–Skan with β = −1988/10000: there are two solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on
[0, ∞) and, for every M, eventually M (1 − p) ≤ q, whose values q(0) and q₂(0) differ. -/
theorem fs_neg1988_two_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-1988 / 10000) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  sorry

end Work.FalknerSkan.Neg1988Rev
