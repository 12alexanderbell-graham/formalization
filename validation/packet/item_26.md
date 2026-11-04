# Item 26

**Area:** F5

**Source:** Cattoën & Visser, Class. Quantum Grav. 24, 5985 (2007), arXiv:0710.1887v1, Eq. (59) (also gr-qc/0703122 v1–v3 and arXiv:0809.0537v1 Eq. (32)): deceleration-distance y² coefficient 1/12 should be 1/24

## Claim in plain words (the system's own text)

The printed coefficient fails (past emission) in every flat `C³` model with
`−1 − 2q₀ + 12q₀² − 4j₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem printedQ2_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : -1 - 2 * decel a t₀ + 12 * decel a t₀ ^ 2 - 4 * cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => remainderQ printedQ2 a t₀ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 3) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaY.lumDistFlat`, `Cosmography.BambaY.yred`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.CVdQ.dQFlat`, `Cosmography.CVdQ.printedQ2`, `Cosmography.BambaY.comoving`, `Cosmography.CCS.D2`, `Cosmography.CVdQ.remainderQ`, `Cosmography.CVdQ.seriesQ`, `changed;.Checked.Chemistry.CoexistenceReduced.q`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, lumDistFlat, yred, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): dQFlat, printedQ2².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedQ2_fails_past`.
- Source file: `Checked/Cosmography/CVdQ.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 26
