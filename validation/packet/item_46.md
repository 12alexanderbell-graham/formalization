# Item 46

**Area:** F0

**Source:** textbook definition of lookback time and the cosmographic parameters (e.g. Visser 2004, Class. Quantum Grav. 21, 2603)

## Claim in plain words (the system's own text)

**Milestone 1b** (frozen in commit e5b5372, audited in runs/2026-10-30T0028Z/audit.md). If `a` is `C³` near `t₀`, the lookback time satisfies
`t₀ - t = H₀⁻¹ (z - (1 + q₀/2) z²) + O(z³)` as `t → t₀`.

## Formal statement (Lean 4)

```lean
theorem lookback_second_order_bigO (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ContDiffAt ℝ 3 a t₀) (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =O[𝓝 t₀] (fun t => redshift a t₀ t ^ 3) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.decel`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: decel, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `lookback_second_order_bigO`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Cosmography/LookbackThird.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 46
