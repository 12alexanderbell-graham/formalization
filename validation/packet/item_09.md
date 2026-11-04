# Item 09

**Area:** B1

**Source:** Risaliti & Lusso, Nat. Astron. 3, 272 (2019); Lusso et al., A&A 628, L4 (2019), Eq. (8): third-order log-polynomial distance and its ΛCDM-implied coefficients

## Claim in plain words (the system's own text)

**Bridge.** In a flat ΛCDM model on `[t, t₀]` the luminosity distance is
`(1+z)/H₀ · ∫_{√(a(t)/a(t₀))}^{1} 2/√(Ω + (1−Ω)v⁶) dv`.

## Formal statement (Lean 4)

```lean
theorem lumDistFlat_flatLCDM (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    lumDistFlat a t₀ t = (1 + redshift a t₀ t) / hubble a t₀ *
      ∫ v in √(a t / a t₀)..1, 2 / √(Ω + (1 - Ω) * v ^ 6) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lumDistFlat_flatLCDM`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Cosmography/B1Truncation.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 09
