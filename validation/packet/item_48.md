# Item 48

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `S : ℝ → ℝ → ℝ`:

**assuming**

1. `TransverseSpec S`

**then**

- `S = transverse`

Program definitions in this claim:

- `TransverseSpec` — SPEC, not pinned: inductive type with constructors `TransverseSpec.mk : ∀ {S : ℝ → ℝ → ℝ}, (∀ (K : ℝ), ∃ S', (∀ (χ : ℝ), HasDerivAt (S K) (S' χ) χ) ∧ (∀ (χ : ℝ), HasDerivAt S' (-K * S K χ) χ) ∧ S K 0 = 0 ∧ S' 0 = 1) → (∀ (χ : ℝ), S 0 χ = χ) → (∀ (K : ℝ), 0 < K → ∀ (χ : ℝ), S K χ = Real.sin (√K * χ) / √K) → (∀ K < 0, ∀ (χ : ℝ), S K χ = Real.sinh (√(-K) * χ) / √(-K)) → (∀ (χ : ℝ), S 1 χ = Real.sin χ) → (∀ (χ : ℝ), S (-1) χ = Real.sinh χ) → (∀ (K χ : ℝ), S K (-χ) = -S K χ) → TransverseSpec S`
- `transverse K χ` — **PINNED** (pin theorem `transverseSpec_pins`): phrase (hand-written, linted): the FLRW transverse distance function S_K(χ) for the spatial curvature constant `K` at the comoving radial distance `χ` (sine form for positive, identity for zero, hyperbolic sine form for negative curvature; positive curvature constant gives sine, closed spherical case); by definition, `transverse K χ` is `if 0 < K then Real.sin (√K * χ) / √K else if K < 0 then Real.sinh (√(-K) * χ) / √(-K) else χ`

## Author's paraphrase (hand-written; checked only by prose rules)

**Pin.** Any `S` obeying the blind determining law `ode` is the program's `transverse`.

## Formal statement (Lean 4)

```lean
theorem transverseSpec_pins (S : ℝ → ℝ → ℝ) (h : TransverseSpec S) : S = transverse := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Transverse.transverse`, `Fidelity.TransverseSpec`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: transverse.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `transverseSpec_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/TransverseSpec.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 48
