# Item 13

**Area:** Data claim

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Data.FR13` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source):** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; statement literals: no blind second reading registered; 8 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); the statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

- there is `Ω : ℝ` such that (`Ω ∈ Set.Icc 0 1`) and (for every `Ω' : ℝ`, if `Ω' ∈ Set.Icc 0 1`, then `margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω'`)

Program definitions in this claim:

- `chiSqHz tbl H₀ Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_chiSqHz`) (for `n : ℕ`, `tbl : Fin n → ℝ × ℝ × ℝ`, `H₀ : ℝ`, `Ω : ℝ`): is defined as `∑ i, ((H₀ * √(Ω * (1 + (tbl i).1) ^ 3 + 1 - Ω) - (tbl i).2.1) / (tbl i).2.2) ^ 2`
- `fr13Table` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_fr13Table`); its name is not checked: is defined as `![(70e-3, 69, 19.6), (0.100, 69, 12), (0.120, 68.6, 26.2), (0.170, 83, 8), (0.179, 75, 4), (0.199, 75, 5), (0.200, 72.9, 29.6), (0.270, 77, 14), (0.280, 88.8, 36.6), (0.350, 76.3, 5.6), (0.352, 83, 14), (0.400, 95, 17), (0.440, 82.6, 7.8), (0.480, 97, 62), (0.593, 104, 13), (0.600, 87.9, 6.1), (0.680, 92, 8), (0.730, 97.3, 7.0), (0.781, 105, 12), (0.875, 125, 17), (0.880, 90, 40), (0.900, 117, 23), (1.037, 154, 20), (1.300, 168, 17), (1.430, 177, 18), (1.530, 140, 14), (1.750, 202, 40), (2.300, 224, 8)]`
- `margChiSq tbl Hbar σ Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_margChiSq`) (for `n : ℕ`, `tbl : Fin n → ℝ × ℝ × ℝ`, `Hbar : ℝ`, `σ : ℝ`, `Ω : ℝ`): is defined as `-2 * Real.log (∫ (H₀ : ℝ), Real.exp (-chiSqHz tbl H₀ Ω / 2) * (Real.exp (-(H₀ - Hbar) ^ 2 / (2 * σ ^ 2)) / √(2 * Real.pi * σ ^ 2)))`

## Author's paraphrase (hand-written; checked only by prose rules)

With the prior 68 ± 2.8, the marginalised chi-square of the Farooq–Ratra 2013 table attains
its smallest value over Ω in [0, 1]: there is a minimiser.

## Formal statement (Lean 4)

```lean
theorem fr13_exists68 : ∃ Ω ∈ Set.Icc (0 : ℝ) 1,
    ∀ Ω' ∈ Set.Icc (0 : ℝ) 1, margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω' := …
```

## Definitions it uses

See GLOSSARY.md: `Data.FR13.fr13Table`, `Data.FR13.chiSqHz`, `Data.FR13.margChiSq`, `Data.FR13Certs.tbl`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): fr13Table².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): margChiSq: Hbar = 68, σ = 2.8.
- Source file: `Checked/Data/FR13.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 13
