# Item 26

**Area:** Falkner–Skan printed separation value

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `β : ℝ`, `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`:

**assuming**

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Set.Ici 0) η`
4. `f 0 = 0`
5. `p 0 = 0`
6. `q 0 = 0`
7. `Filter.Tendsto p Filter.atTop (nhds 1)`
8. for every `η : ℝ`, if `η ∈ Set.Ioi 0`, then `0 < q η`
9. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`

**then**

- `β < -(1988376 / 10000000)`

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan separation: for every solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0,
p(0) = 0, wall shear q(0) = 0, p → 1, q > 0 on (0, ∞) and, for every M,
`∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`: β < `-(1988376 / 10000000)`, the value Fazio printed for the
parameter of the solution with zero wall shear.

## Formal statement (Lean 4)

```lean
theorem fs_separation_below_printed {β : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 0) (hl : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ioi (0 : ℝ), 0 < q η) (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    β < -(1988376 / 10000000) := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `fs_separation_below_printed`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/FalknerSkan/SeparationPrinted.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 26
