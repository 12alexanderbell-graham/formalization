# Item 18

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

**Pinning:** any `Rc` meeting `RicciFlatFLRWSpec` is `curv` wherever `a > 0` is twice
differentiable at `t`.

## Formal statement (Lean 4)

```lean
theorem ricciSpec_pins (Rc : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatFLRWSpec Rc) (a a' a'' : ℝ → ℝ)
    (t : ℝ) (ha : 0 < a t) (h1 : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s)
    (h2 : HasDerivAt a' (a'' t) t) : Rc a t = curv a t := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.FRCosmo.curv`, `Cosmography.hubble`, `Fidelity.RicciFlatFLRWSpec`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: curv.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `ricciSpec_pins`.
- Source file: `Checked/Fidelity/FRSpecs.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 18
