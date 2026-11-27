# Item 32

**Area:** B1

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** Risaliti & Lusso, Nat. Astron. 3, 272 (2019); Lusso et al., A&A 628, L4 (2019), Eq. (8): third-order log-polynomial distance and its ΛCDM-implied coefficients

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Cosmography.B1Truncation` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: the Checked theorem `Checked.Trust.NV.cubic_misses_z3` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 8 numbered; 4 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 4 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: no blind second reading registered; 10 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); program definitions the claim uses (listed under the claim): 3 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 3 of them also determined by a blind reader's specification that they meet (on the domain printed with the definition), 3 with a blind second reading or formulation, 0 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `Ω : ℝ`, `a : ℝ → ℝ`, `t : ℝ`, `t₀ : ℝ`:

**assuming**

1. `1 / 5 ≤ Ω`
2. `Ω ≤ 2 / 5`
3. `t ≤ t₀`
4. for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `0 < a s`
5. for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `DifferentiableAt ℝ a s`
6. `0 < hubble a t₀`
7. for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)`
8. `redshift a t₀ t = 3`

**then**

1. `0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)`
2. `9 / 10 < 5 * Real.logb 10 (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t))`

Program definitions in this claim:

- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t`. Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader A AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_hubble_A`) and the reader's specification `Checked.Trust.SecondReadingSpecA.HubbleSpecA` determines it (`Checked.Trust.SpecAgreement.pins_hubble_A`) assuming `0 < a t`; `DifferentiableAt ℝ a t`; reader B AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_hubble_B`) and the reader's specification `Checked.Trust.SecondReadingSpecB.HubbleSpecB` determines it (`Checked.Trust.SpecAgreement.pins_hubble_B`) assuming `a t ≠ 0`; `DifferentiableAt ℝ a t`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «logarithmic derivative of the scale factor with respect to cosmic time» only assuming `0 < a t`; `DifferentiableAt ℝ a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `0 < deriv a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `deriv a t < 0`
- `logPolyDL3 a₂ a₃ H₀ z` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_logPolyDL3`); its name is not checked (for `a₂ : ℝ`, `a₃ : ℝ`, `H₀ : ℝ`, `z : ℝ`): is defined as `Real.log 10 / H₀ * (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3)`
- `lumDistFlat a t₀ t` — **PINNED** (pin theorem `lumDistFlat_pins`): phrase (hand-written, linted): the luminosity distance in flat FLRW with the scale factor `a`, the observation time `t₀` and the emission time `t` (units in which the speed of light is one); by definition, `lumDistFlat a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t`. Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader A AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_lumDistFlat_A`) and the reader's specification `Checked.Trust.SecondReadingSpecA.LumDistFlatSpecA` determines it (`Checked.Trust.SpecAgreement.pins_lumDistFlat_A`) assuming `t ≤ t₀`; `ContinuousOn a (Set.Icc t t₀)`; for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `0 < a s`; reader B AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_lumDistFlat_B`) and the reader's specification `Checked.Trust.SecondReadingSpecB.LumDistFlatSpecB` determines it (`Checked.Trust.SpecAgreement.pins_lumDistFlat_B`) assuming `t ≤ t₀`; `ContinuousOn a (Set.Icc t t₀)`; for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `0 < a s`
- `lusA2 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lusA2`); its name is not checked (for `Ω : ℝ`): is defined as `Real.log 10 * (3 / 2 - 3 / 4 * Ω)`
- `lusA3 Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_lusA3`); its name is not checked (for `Ω : ℝ`): is defined as `Real.log 10 ^ 2 * (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6)`
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the cosmological redshift with the scale factor `a`, the observation time `t₀` and the emission time `t` (positive when emission precedes observation in an expanding universe; one plus redshift is the scale factor at observation over that at emission; negative redshift is blueshift; zero when emission and observation coincide); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`. Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader A AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_redshift_A`) and the reader's specification `Checked.Trust.SecondReadingSpecA.RedshiftSpecA` determines it (`Checked.Trust.SpecAgreement.pins_redshift_A`) assuming `0 < a t`; `0 < a t₀`; reader B AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_redshift_B`) and the reader's specification `Checked.Trust.SecondReadingSpecB.RedshiftSpecB` determines it (`Checked.Trust.SpecAgreement.pins_redshift_B`) assuming `t ≤ t₀`; `0 < a t`; `0 < a t₀`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «positive when emission precedes observation in an expanding universe» only assuming for every `s : ℝ`, `0 < a s`; `StrictMono a`; `t < t₀`, «one plus redshift is the scale factor at observation over that at emission», «zero when emission and observation coincide» only assuming `a t₀ ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

**B1, z = 3.** For every flat ΛCDM model with `Ω ∈ [0.2, 0.4]`, the third-order
log-polynomial at the ΛCDM-implied coefficients (same `H₀`) is positive at `z = 3` and
underestimates the exact distance modulus there by more than 0.9 mag.

## Formal statement (Lean 4)

```lean
theorem cubic_misses_z3 (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz : redshift a t₀ t = 3) :
    0 < logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t) ∧
    9 / 10 < 5 * Real.logb 10
      (lumDistFlat a t₀ t / logPolyDL3 (lusA2 Ω) (lusA3 Ω) (hubble a t₀) (redshift a t₀ t)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaY.lumDistFlat`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1.logPolyDL3`, `Cosmography.B1.lusA2`, `Cosmography.B1.lusA3`, `Cosmography.BambaY.comoving`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDistFlat, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL3², lusA2², lusA3².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `cubic_misses_z3`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): redshift(t) = 3.
- Source file: `Checked/Cosmography/B1Truncation.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 32
