# Item 10

**Area:** F2

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 (v1 and v2), Eq. (22): flat matter + CPL l₀, w_a² term missing a factor 9

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Cosmography.CPLCoefficients` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: the Checked theorem `Checked.Trust.NV.printedL0_ne` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 3 numbered; 2 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 1 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: no blind second reading registered; 37 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); program definitions the claim uses (listed under the claim): 2 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 0 with a blind second reading or formulation, 0 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `Ω : ℝ`, `w₀ : ℝ`, `wₐ : ℝ`, `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding)
2. `ContDiffAt ℝ 5 a t₀`
3. `(1 - Ω) * (7 - Ω) * wₐ = 0`

**then**

- `cosmoCoeff 5 a t₀ ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀ + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2 + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3 + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4`

Program definitions in this claim:

- `IsFlatCPL Ω w₀ wₐ a t₀` — **PINNED** (pin theorem `flatCPL_pins`): phrase (hand-written, linted): the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding); by definition, means (`0 < hubble a t₀`) and (`∀ᶠ (t : ℝ) in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) * Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))`). Phrase lines proved in Lean (statements in PHRASE_LINES.md): «present Hubble rate is positive so the universe is expanding» only assuming the scale factor `a` obeys the flat matter plus CPL dark energy Friedmann expansion law with the present matter density parameter `Ω`, the present dark energy equation of state `w₀`, the equation of state evolution parameter `wₐ` and the observation time `t₀` (spatially flat universe with dust and separately conserved dark energy; redshift z is measured from `t₀`; `Ω` is the present matter density parameter; holds on a whole neighbourhood of `t₀`; present Hubble rate is positive so the universe is expanding)
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «orders 0 and 1 coefficients are one» only assuming `a t ≠ 0`; `deriv a t ≠ 0`, «The order 2 coefficient is minus the deceleration parameter usually written q» only assuming `a t ≠ 0`

## Author's paraphrase (hand-written; checked only by prose rules)

The printed `l₀` is wrong in every flat CPL model with `(1 − Ω)(7 − Ω) wₐ ≠ 0`.

## Formal statement (Lean 4)

```lean
theorem printedL0_ne (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatCPL Ω w₀ wₐ a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) (hne : (1 - Ω) * (7 - Ω) * wₐ = 0) :
    cosmoCoeff 5 a t₀ ≠ 35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.CPL.IsFlatCPL`, `Cosmography.hubble`, `Cosmography.redshift`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, IsFlatCPL.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `printedL0_ne`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cosmoCoeff: n = 5.
- Source file: `Checked/Cosmography/CPLCoefficients.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 10
