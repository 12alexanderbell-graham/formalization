# Item 03

**Area:** Data claim

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `Ω : ℝ`, `z : ℝ`:

**assuming**

1. `0 ≤ Ω`
2. `Ω ≤ 1`
3. for every `Ω' : ℝ`, if `Ω' ∈ Set.Icc 0 1`, then `margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω'`
4. `-1 < z`
5. `Ω * (1 + z) ^ 3 = 2 * (1 - Ω)`

**then**

1. `0.703 < z`
2. `z < 0.706`

Program definitions in this claim:

- `chiSqHz tbl H₀ Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_chiSqHz`) (for `n : ℕ`, `tbl : Fin n → ℝ × ℝ × ℝ`, `H₀ : ℝ`, `Ω : ℝ`): is defined as `∑ i, ((H₀ * √(Ω * (1 + (tbl i).1) ^ 3 + 1 - Ω) - (tbl i).2.1) / (tbl i).2.2) ^ 2`
- `fr13Table` — PRINTED, not pinned, so only the formula shown is checked, not its name: is defined as `![(70e-3, 69, 19.6), (0.100, 69, 12), (0.120, 68.6, 26.2), (0.170, 83, 8), (0.179, 75, 4), (0.199, 75, 5), (0.200, 72.9, 29.6), (0.270, 77, 14), (0.280, 88.8, 36.6), (0.350, 76.3, 5.6), (0.352, 83, 14), (0.400, 95, 17), (0.440, 82.6, 7.8), (0.480, 97, 62), (0.593, 104, 13), (0.600, 87.9, 6.1), (0.680, 92, 8), (0.730, 97.3, 7.0), (0.781, 105, 12), (0.875, 125, 17), (0.880, 90, 40), (0.900, 117, 23), (1.037, 154, 20), (1.300, 168, 17), (1.430, 177, 18), (1.530, 140, 14), (1.750, 202, 40), (2.300, 224, 8)]`
- `margChiSq tbl Hbar σ Ω` — FORMULA, not pinned, so only the formula shown is checked, not its name (for `n : ℕ`, `tbl : Fin n → ℝ × ℝ × ℝ`, `Hbar : ℝ`, `σ : ℝ`, `Ω : ℝ`): is defined as `-2 * Real.log (∫ (H₀ : ℝ), Real.exp (-chiSqHz tbl H₀ Ω / 2) * (Real.exp (-(H₀ - Hbar) ^ 2 / (2 * σ ^ 2)) / √(2 * Real.pi * σ ^ 2)))`

## Author's paraphrase (hand-written; checked only by prose rules)

With the prior 68 ± 2.8, at every minimiser Ω over [0, 1] of the marginalised chi-square
of the Farooq–Ratra 2013 table, the z > −1 solving Ω(1+z)³ = 2(1 − Ω) lies strictly between
0.703 and 0.706.

## Formal statement (Lean 4)

```lean
theorem fr13_zda68 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1, margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω')
    (z : ℝ) (hz : -1 < z) (hda : Ω * (1 + z) ^ 3 = 2 * (1 - Ω)) :
    0.703 < z ∧ z < 0.706 := …
```

## Definitions it uses

See GLOSSARY.md: `Data.FR13.fr13Table`, `Data.FR13.chiSqHz`, `Data.FR13.margChiSq`, `Data.FR13Certs.tbl`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): fr13Table.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `fr13_zda68`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): margChiSq: Hbar = 68, σ = 2.8.
- Source file: `Checked/Data/FR13.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 03
