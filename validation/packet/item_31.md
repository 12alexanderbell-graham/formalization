# Item 31

**Area:** Falkner–Skan attached rows β = −0.13, −0.14, −0.15, −0.16

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**It holds that**

- there is `f : ℝ → ℝ` such that there is `p : ℝ → ℝ` such that there is `q : ℝ → ℝ` such that (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - -14 / 100 * (1 - p η ^ 2)) (Set.Ici 0) η`) and (`f 0 = 0`) and (`p 0 = 0`) and (`Filter.Tendsto p Filter.atTop (nhds 1)`) and (for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `0 < q η`) and (for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`)

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan with β = −14/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`.

## Formal statement (Lean 4)

```lean
theorem fs_neg_wall_shear_14_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-14 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/NegWallShearRowsTop.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 31
