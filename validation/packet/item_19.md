# Item 19

**Area:** T1 fidelity

**Source:** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim in plain words (the system's own text)

No gap in `DecelSpec`: on every positive scale factor, twice differentiable at `t` with
`ȧ(t) ≠ 0`, any `Q` meeting the spec equals `decel`.

## Formal statement (Lean 4)

```lean
theorem decelSpec_pins (Q : (ℝ → ℝ) → ℝ → ℝ) (h : DecelSpec Q) (a a' : ℝ → ℝ) (a'' t : ℝ)
    (h1 : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) (h2 : HasDerivAt a' a'' t) (ha : 0 < a t)
    (hd : a' t ≠ 0) : Q a t = decel a t := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.decel`, `Cosmography.Aviles.eds`, `Fidelity.DecelSpec`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: decel.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `decelSpec_pins`.
- Source file: `Checked/Fidelity/Pins.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 19
