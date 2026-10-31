# Item 35

**Area:** Certified numbers of the findings

**Source:** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim in plain words (the system's own text)

The paper's toy model `(Ω, w₀, wₐ) = (0.245, −0.93, −0.41)`: in every flat matter + CPL model
with these parameters `l₀ = 0.809`, while the printed formula gives `−0.906`.

## Formal statement (Lean 4)

```lean
theorem F2_toy (a : ℝ → ℝ) (t₀ : ℝ)
    (hL : CPL.IsFlatCPL (245 / 1000) (-93 / 100) (-41 / 100) a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    RoundsTo (cosmoCoeff 5 a t₀) 0.809 3 ∧
      RoundsTo (printedCPLl0 (245 / 1000 : ℝ) (-93 / 100 : ℝ) (-41 / 100 : ℝ)) (-0.906) 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `F2_toy`.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 35
