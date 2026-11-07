# Item 07

**Area:** Fluid mechanics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`:

**assuming**

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η / 2)) (Set.Ici 0) η`
4. `f 0 = 0`
5. `p 0 = 0`
6. `Filter.Tendsto p Filter.atTop (nhds 1)`

**then**

1. `0.33205733621519 ≤ q 0`
2. `q 0 ≤ 0.33205733621520`

## Author's paraphrase (hand-written; checked only by prose rules)

Blasius boundary layer, wall shear: for every solution f of f''' + f f''/2 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q/2, one-sided at 0) with
f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞, the wall value q(0) = f''(0) lies between
0.33205733621519 and 0.33205733621520.

## Formal statement (Lean 4)

```lean
theorem blasius_wall_shear (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η / 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.33205733621519 ≤ q 0 ∧ q 0 ≤ 0.33205733621520 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `blasius_wall_shear`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Blasius/Blasius.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 07
