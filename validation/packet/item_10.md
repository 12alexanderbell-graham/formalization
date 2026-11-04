# Item 10

**Area:** F9

**Source:** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421, Sec. XI ("testing F(R) gravity by cosmography"), Eq. (11.31), from Capozziello, Cardone, Salzano 2008 (arXiv:0802.1583, PRD 78, 063504) Eq. (33): the common denominator R of the F(R₀), F″(R₀), F‴(R₀) formulas is wrong, so the printed F(R₀) formula (11.21) fails the paper's own ΛCDM check (11.40); also (11.13) d³R₀/dt³ has a sign error

## Claim in plain words (the system's own text)

(11.40), the paper's own check: for every `Ω ∈ (0,1)` there is a flat ΛCDM scale factor
which, with `F(R) = R + 2Λ`, `Λ = 3H₀²(1 − Ω)`, satisfies every hypothesis of `IsFRCosmo`.

## Formal statement (Lean 4)

```lean
theorem exists_LCDM_model {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ ∧
      IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀ := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.FRCosmo.FriedmannEq`, `Cosmography.FRCosmo.MasterEq`, `Cosmography.FRCosmo.curv`, `Cosmography.hubble`, `Cosmography.FRCosmo.IsFRCosmo`, `Cosmography.FRCosmo.rhoM`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, FriedmannEq, MasterEq, curv, hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `exists_LCDM_model`.
- Source file: `Checked/Cosmography/FRCosmo.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 10
