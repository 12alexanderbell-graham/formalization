# Item 25

**Area:** F5

**Source:** Cattoën & Visser, Class. Quantum Grav. 24, 5985 (2007), arXiv:0710.1887v1, Eq. (59) (also gr-qc/0703122 v1–v3 and arXiv:0809.0537v1 Eq. (32)): deceleration-distance y² coefficient 1/12 should be 1/24

## Claim in plain words (the system's own text)

**Deceleration distance to third order in `y`** (flat FLRW, coefficient over 24).

## Formal statement (Lean 4)

```lean
theorem dQ_y_third_order (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remainderQ correctQ2 a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaY.lumDistFlat`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.CVdQ.dQFlat`, `Cosmography.BambaY.comoving`, `Cosmography.CCS.D2`, `Cosmography.CVdQ.correctQ2`, `Cosmography.CVdQ.remainderQ`, `Cosmography.CVdQ.seriesQ`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDistFlat, yred, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): dQFlat.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `dQ_y_third_order`.
- Source file: `Checked/Cosmography/CVdQ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 25
