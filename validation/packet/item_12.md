# Item 12

**Area:** Fluid mechanics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `f : ℝ → ℝ` such that there is `p : ℝ → ℝ` such that there is `q : ℝ → ℝ` such that (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Set.Ici 0) η`) and (`f 0 = 0`) and (`p 0 = 0`) and (`Filter.Tendsto p Filter.atTop (nhds 1)`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then (`0 ≤ p η`) and (`p η < 1`)) and (`0.927680039 < q 0`) and (`q 0 < 0.927680040`)

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan β = 1/2: there is a solution of f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − (1 − p²)/2, one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 0.927680039 and 0.927680040.

## Formal statement (Lean 4)

```lean
theorem fs_half_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/HalfBounded.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 12
