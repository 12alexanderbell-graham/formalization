# Item 35

**Area:** Falkner–Skan separation value

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `β₁ : ℝ`, `β₂ : ℝ`, `f₁ : ℝ → ℝ`, `p₁ : ℝ → ℝ`, `q₁ : ℝ → ℝ`, `f₂ : ℝ → ℝ`, `p₂ : ℝ → ℝ`, `q₂ : ℝ → ℝ`:

**assuming**

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f₁ (p₁ η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p₁ (q₁ η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q₁ (-(f₁ η * q₁ η) - β₁ * (1 - p₁ η ^ 2)) (Set.Ici 0) η`
4. `f₁ 0 = 0`
5. `p₁ 0 = 0`
6. `q₁ 0 = 0`
7. `Filter.Tendsto p₁ Filter.atTop (nhds 1)`
8. for every `η : ℝ`, if `η ∈ Set.Ioi 0`, then `0 < q₁ η`
9. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₁ η) ≤ q₁ η`
10. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f₂ (p₂ η) (Set.Ici 0) η`
11. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p₂ (q₂ η) (Set.Ici 0) η`
12. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β₂ * (1 - p₂ η ^ 2)) (Set.Ici 0) η`
13. `f₂ 0 = 0`
14. `p₂ 0 = 0`
15. `q₂ 0 = 0`
16. `Filter.Tendsto p₂ Filter.atTop (nhds 1)`
17. for every `η : ℝ`, if `η ∈ Set.Ioi 0`, then `0 < q₂ η`
18. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`

**then**

- `β₁ = β₂`

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan separation: for every solution (f₁, p₁, q₁) of f''' + f f'' + β₁(1 − f'²) = 0 and every
solution (f₂, p₂, q₂) of f''' + f f'' + β₂(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, wall
shear q(0) = 0, p → 1, q > 0 on (0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₁ η) ≤ q₁ η` and
`∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`: β₁ = β₂.

## Formal statement (Lean 4)

```lean
theorem fs_separation_equal {β₁ β₂ : ℝ} {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ}
    (hf₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₁ (p₁ η) (Ici 0) η)
    (hp₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₁ (q₁ η) (Ici 0) η)
    (hq₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₁ (-(f₁ η * q₁ η) - β₁ * (1 - p₁ η ^ 2)) (Ici 0) η)
    (hf₁0 : f₁ 0 = 0) (hp₁0 : p₁ 0 = 0) (hq₁0 : q₁ 0 = 0) (hl₁ : Tendsto p₁ atTop (𝓝 1))
    (hpos₁ : ∀ η ∈ Ioi (0 : ℝ), 0 < q₁ η) (hdec₁ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₁ η) ≤ q₁ η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β₂ * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hq₂0 : q₂ 0 = 0) (hl₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ioi (0 : ℝ), 0 < q₂ η) (hdec₂ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) :
    β₁ = β₂ := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `fs_separation_equal`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/SeparationEqual.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 35
