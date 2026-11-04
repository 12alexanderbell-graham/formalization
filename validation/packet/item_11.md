# Item 11

**Area:** F3

**Source:** Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583v2, App. A, Eq. (A2): lookback-distance z⁵ coefficient, 7/2 q₀⁴ should be 7/8 q₀⁴

## Claim in plain words (the system's own text)

**Lookback time to fifth order in redshift** (correct version of Eq. (A2)): for every
scale factor that is `C⁵` at `t₀`, with `a(t₀) ≠ 0` and `H₀ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem lookback_fifth_order (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remainder correctD4 a t₀ t) =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 5) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.CCS.D1`, `Cosmography.CCS.D2`, `Cosmography.CCS.D3`, `Cosmography.CCS.correctD4`, `Cosmography.CCS.remainder`, `Cosmography.CCS.series`, `changed;.Checked.Chemistry.CoexistenceReduced.q`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): D1², D2², D3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lookback_fifth_order`.
- Source file: `Checked/Cosmography/CCSLookback.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 11
