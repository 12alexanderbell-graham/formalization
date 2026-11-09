# Item 41

**Area:** Falkner–Skan with adverse pressure gradient, β < 0

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `β : ℝ`, `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`, `f₂ : ℝ → ℝ`, `p₂ : ℝ → ℝ`, `q₂ : ℝ → ℝ`, `η : ℝ`:

**assuming**

1. `β < 0`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
4. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Set.Ici 0) η`
5. `f 0 = 0`
6. `p 0 = 0`
7. `Filter.Tendsto p Filter.atTop (nhds 1)`
8. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `0 < q η`
9. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`
10. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f₂ (p₂ η) (Set.Ici 0) η`
11. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p₂ (q₂ η) (Set.Ici 0) η`
12. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Set.Ici 0) η`
13. `f₂ 0 = 0`
14. `p₂ 0 = 0`
15. `Filter.Tendsto p₂ Filter.atTop (nhds 1)`
16. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `0 < q₂ η`
17. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`
18. `η ∈ Set.Ici 0`

**then**

1. `f η = f₂ η`
2. `p η = p₂ η`
3. `q η = q₂ η`

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan with β < 0: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and,
for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`: f η = f₂ η, p η = p₂ η and q η = q₂ η for every η ≥ 0.

## Formal statement (Lean 4)

```lean
theorem fs_neg_decay_equal (β : ℝ) (hβ : β < 0) (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η)
    (hdec₂ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `fs_neg_decay_equal`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/NegDecay.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 41
