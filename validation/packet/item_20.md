# Item 20

**Area:** B1

**Source:** Risaliti & Lusso, Nat. Astron. 3, 272 (2019); Lusso et al., A&A 628, L4 (2019), Eq. (8): third-order log-polynomial distance and its ΛCDM-implied coefficients

## Claim in plain words (the system's own text)

**B1 separation.** In every flat ΛCDM model with `Ω ∈ [0.2, 0.4]` (sources at `z = 3`, `z = 7`),
any cubic log-polynomial (coefficients `a₂, a₃`, normalisation `H > 0`, positive at both
redshifts) whose distance modulus agrees with the exact one up to a common offset `c` within
0.05 mag at `z = 3` and at `z = 7` has `(a₂, a₃)` at Euclidean distance more than `5/4` from the
ΛCDM-implied point `(lusA2 Ω, lusA3 Ω)`.

## Formal statement (Lean 4)

```lean
theorem cubic_separation (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₇ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₇))
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₇ : |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₇)) - c|
      ≤ 1 / 20) :
    (5 / 4) ^ 2 < (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1.logPolyDL3`, `Cosmography.B1.lusA2`, `Cosmography.B1.lusA3`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL3², lusA2², lusA3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `cubic_separation`.
- Source file: `Checked/Cosmography/B1Separation.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 20
