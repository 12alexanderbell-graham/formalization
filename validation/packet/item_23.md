# Item 23

**Area:** B1 fourth order

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Cosmography.B1L19Curved` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: the Checked theorem `Checked.Trust.NV.l19_sq_curved` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 13 numbered; 9 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 4 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: no blind second reading registered; 25 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); program definitions the claim uses (listed under the claim): 4 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 4 of them also determined by a blind reader's specification that they meet (on the domain printed with the definition), 1 with a blind second reading or formulation, 0 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `Ω : ℝ`, `K : ℝ`, `a : ℝ → ℝ`, `t₅ : ℝ`, `t₃ : ℝ`, `t₀ : ℝ`, `H : ℝ`:

**assuming**

1. `1 / 10 ≤ Ω`
2. `Ω ≤ 1`
3. `t₅ ≤ t₃`
4. `t₃ ≤ t₀`
5. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `0 < a s`
6. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `DifferentiableAt ℝ a s`
7. `0 < hubble a t₀`
8. `1 ≤ omega0 K a t₀`
9. `omega0 K a t₀ ≤ 11 / 10`
10. for every `s : ℝ`, if `s ∈ Set.Icc t₅ t₀`, then `hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω)`
11. `redshift a t₀ t₃ = 2 * √2 - 1`
12. `redshift a t₀ t₅ = 4 * √2 - 1`
13. `0 < H`

**then**

- `1 / 4 < 5 * Real.logb 10 (lumDist K a t₀ t₅ / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₅)) - 5 * Real.logb 10 (lumDist K a t₀ t₃ / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₃))`

Program definitions in this claim:

- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t`. Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader A AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_hubble_A`) and the reader's specification `Checked.Trust.SecondReadingSpecA.HubbleSpecA` determines it (`Checked.Trust.SpecAgreement.pins_hubble_A`) assuming `0 < a t`; `DifferentiableAt ℝ a t`; reader B AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_hubble_B`) and the reader's specification `Checked.Trust.SecondReadingSpecB.HubbleSpecB` determines it (`Checked.Trust.SpecAgreement.pins_hubble_B`) assuming `a t ≠ 0`; `DifferentiableAt ℝ a t`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «logarithmic derivative of the scale factor with respect to cosmic time» only assuming `0 < a t`; `DifferentiableAt ℝ a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `0 < deriv a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `deriv a t < 0`
- `logPolyDL4 a₂ a₃ a₄ H₀ z` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_logPolyDL4`); its name is not checked (for `a₂ : ℝ`, `a₃ : ℝ`, `a₄ : ℝ`, `H₀ : ℝ`, `z : ℝ`): is defined as `Real.log 10 / H₀ * (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3 + a₄ * Real.logb 10 (1 + z) ^ 4)`
- `lumDist K a t₀ t` — **PINNED** (pin theorem `lumDistSpec2_pins`): phrase (hand-written, linted): the luminosity distance in FLRW with curvature with the spatial curvature constant `K`, the scale factor `a`, the observation time `t₀` and the emission time `t` (positive curvature constant means closed, negative means open; units in which the speed of light is one; positive `K` is closed and negative `K` is open); by definition, `lumDist K a t₀ t` is `a t₀ * (1 + redshift a t₀ t) * transverse K (comoving a t₀ t)`. Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader C AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_lumDist_C`) and the reader's specification `Checked.Trust.SecondReadingSpecC.LumDistSpecC` determines it (`Checked.Trust.SpecAgreement.pins_lumDist_C`) assuming `t ≤ t₀`; `ContinuousOn a (Set.Icc t t₀)`; for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `0 < a s`; reader D AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_lumDist_D`) and the reader's specification `Checked.Trust.SecondReadingSpecD.LumDistSpecD` determines it (`Checked.Trust.SpecAgreement.pins_lumDist_D`) assuming `t ≤ t₀`; `ContinuousOn a (Set.Icc t t₀)`; for every `s : ℝ`, if `s ∈ Set.Icc t t₀`, then `0 < a s`
- `omega0 K a t₀` — **PINNED** (pin theorem `omega0Spec_pins`): phrase (hand-written, linted): the present total density parameter Ω0 with the spatial curvature constant `K`, the scale factor `a` and the observation time `t₀` (one plus curvature term, positive curvature constant gives above one; total density parameter and not the matter fraction alone; equals one for zero curvature); by definition, `omega0 K a t₀` is `1 + K / (hubble a t₀ ^ 2 * a t₀ ^ 2)`. Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader A AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_omega0_A`) and the reader's specification `Checked.Trust.SecondReadingSpecA.Omega0SpecA` determines it (`Checked.Trust.SpecAgreement.pins_omega0_A`) assuming `0 < a t₀`; `DifferentiableAt ℝ a t₀`; `deriv a t₀ ≠ 0`; reader B AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_omega0_B`) and the reader's specification `Checked.Trust.SecondReadingSpecB.Omega0SpecB` determines it (`Checked.Trust.SpecAgreement.pins_omega0_B`) assuming `a t₀ ≠ 0`; `DifferentiableAt ℝ a t₀`; `deriv a t₀ ≠ 0`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «one plus curvature term, positive curvature constant gives above one», «one plus curvature term, positive curvature constant gives above one» only assuming `0 < K`; `hubble a t₀ ≠ 0`; `a t₀ ≠ 0`, «equals one for zero curvature»
- `redshift a t₀ t` — **PINNED** (pin theorem `redshiftCore_pins`): phrase (hand-written, linted): the cosmological redshift with the scale factor `a`, the observation time `t₀` and the emission time `t` (positive when emission precedes observation in an expanding universe; one plus redshift is the scale factor at observation over that at emission; negative redshift is blueshift; zero when emission and observation coincide); by definition, `redshift a t₀ t` is `a t₀ / a t - 1`. Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader A AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_redshift_A`) and the reader's specification `Checked.Trust.SecondReadingSpecA.RedshiftSpecA` determines it (`Checked.Trust.SpecAgreement.pins_redshift_A`) assuming `0 < a t`; `0 < a t₀`; reader B AGREES: the definition meets the reader's specification (`Checked.Trust.SpecAgreement.meets_redshift_B`) and the reader's specification `Checked.Trust.SecondReadingSpecB.RedshiftSpecB` determines it (`Checked.Trust.SpecAgreement.pins_redshift_B`) assuming `t ≤ t₀`; `0 < a t`; `0 < a t₀`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «positive when emission precedes observation in an expanding universe» only assuming for every `s : ℝ`, `0 < a s`; `StrictMono a`; `t < t₀`, «one plus redshift is the scale factor at observation over that at emission», «zero when emission and observation coincide» only assuming `a t₀ ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

**Lusso et al. 2019, SNe + quasars, central fit, closed or flat curvature.** For every matter density
`Ω ∈ [1/10, 1]`, every curvature constant `K` whose total density parameter `Ω₀ = 1 + K/(H₀²a₀²)`
lies in `[1, 11/10]`, and every scale factor obeying
`H = H₀ √(Ω(1+z)³ + (1 − Ω₀)(1+z)² + Ω₀ − Ω)` (with `H₀ > 0`) on the whole interval back to the
farther source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`,
the quartic log-polynomial distance with the printed central coefficients `a₂ = 3.075`,
`a₃ = 4.466`, `a₄ = −3.716` has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact
luminosity distance `d_L` (`lumDist K`) that exceeds at `1 + z = 4√2` the one at `1 + z = 2√2` by
more than 1/4 mag.

## Formal statement (Lean 4)

```lean
theorem l19_sq_curved (Ω K : ℝ) (hΩ₀ : 1 / 10 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hK₀ : 1 ≤ omega0 K a t₀) (hK₁ : omega0 K a t₀ ≤ 11 / 10)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    1 / 4 < 5 * Real.logb 10 (lumDist K a t₀ t₅
        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDist K a t₀ t₃
        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₃)) := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.BambaK.lumDist`, `Cosmography.BambaK.omega0`, `Cosmography.hubble`, `Cosmography.redshift`, `Cosmography.B1L19.logPolyDL4`, `Cosmography.BambaY.comoving`, `Cosmography.Transverse.transverse`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: lumDist, omega0, hubble, redshift.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): logPolyDL4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `l19_sq_curved`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): logPolyDL4: a₂ = 3.075, a₃ = 4.466, a₄ = -3.716; redshift(t₃) = 2 * √2 - 1; redshift(t₅) = 4 * √2 - 1.
- Source file: `Checked/Cosmography/B1L19Curved.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 23
