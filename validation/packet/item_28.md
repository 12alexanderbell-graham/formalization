# Item 28

**Area:** run 2026-11-09T0428Z

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `β : ℝ`, `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`, `η : ℝ`:

**assuming**

1. `0 < β`
2. `β ≤ 1`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
4. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
5. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Set.Ici 0) η`
6. `f 0 = 0`
7. `p 0 = 0`
8. `Filter.Tendsto p Filter.atTop (nhds 1)`
9. `η ∈ Set.Ici 0`

**then**

- `0 < q η`

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan with pressure-gradient coefficient β, 0 < β ≤ 1: every solution of
f''' + f f'' + β (1 − f'²) = 0 on [0, ∞) (f has derivative p, p has derivative q, q has derivative
−f q − β (1 − p²), one-sided at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ has q(η) = f''(η)
positive for every η ≥ 0.

## Formal statement (Lean 4)

```lean
theorem fs_monotone_of_limit (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), 0 < q η := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `fs_monotone_of_limit`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/Limit.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 28
