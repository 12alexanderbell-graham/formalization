# Item 08

**Area:** F4–F7

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421 (v1–v3), Eqs. (10.55)–(10.57), copied verbatim from Capozziello & Salzano, Adv. Astron. 2009, 217420, arXiv:0902.0088, Eqs. (56)–(58): curvature terms of the y-redshift d_L coefficients D³_{L,y}, D⁴_{L,y} wrong

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Records.Findings` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: nothing to witness (the statement has no hypothesis to meet); hypotheses: none numbered; no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: no blind second reading registered; no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); program definitions the claim uses (listed under the claim): 3 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 3 with a blind second reading or formulation, 0 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**It holds that**

1. `RoundsTo (printedD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0) (cosmoCoeff 5 Real.exp 0) (omega0 1 Real.exp 0)) 3.75 2`
2. `RoundsTo (correctD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0) (cosmoCoeff 5 Real.exp 0) (omega0 1 Real.exp 0)) 3.3417 4`
3. `RoundsTo (printedD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0) (cosmoCoeff 5 Real.exp 0) (omega0 1 Real.exp 0) - correctD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0) (cosmoCoeff 5 Real.exp 0) (omega0 1 Real.exp 0)) 0.4083 4`

Program definitions in this claim:

- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `correctD4y q j s l Ω` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctD4y`) (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `Ω : ℝ`): is defined as `printedD4y q j s l Ω + (Ω - 1) ^ 2 / 120 + 5 * q * (Ω - 1) / 12`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): phrase (hand-written, linted): the cosmographic coefficient with the derivative order of the coefficient `n`, the scale factor `a` and the time of evaluation `t` (`n`-th time derivative of the scale factor over the scale factor divided by the `n`-th power of the Hubble rate; orders 0 and 1 coefficients are one; The order 2 coefficient is minus the deceleration parameter usually written q; The order 3 coefficient is the jerk parameter usually written j; The order 4 coefficient is the snap parameter usually written s; The order 5 coefficient is the lerk parameter usually written l); by definition, `cosmoCoeff n a t` is `iteratedDeriv n a t / (a t * hubble a t ^ n)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «orders 0 and 1 coefficients are one» only assuming `a t ≠ 0`; `deriv a t ≠ 0`, «The order 2 coefficient is minus the deceleration parameter usually written q» only assuming `a t ≠ 0`
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): phrase (hand-written, linted): the deceleration parameter with the scale factor `a` and the cosmic time of evaluation `t` (minus acceleration times scale factor over velocity squared; minus the second time derivative times the scale factor divided by the squared first time derivative; negative value means accelerating expansion); by definition, `decel a t` is `-(deriv (deriv a) t * a t) / deriv a t ^ 2`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «negative value means accelerating expansion» only assuming `0 < a t`; `0 < deriv a t`
- `omega0 K a t₀` — **PINNED** (pin theorem `omega0Spec_pins`): phrase (hand-written, linted): the present total density parameter Ω0 with the spatial curvature constant `K`, the scale factor `a` and the observation time `t₀` (one plus curvature term, positive curvature constant gives above one; total density parameter and not the matter fraction alone; equals one for zero curvature); by definition, `omega0 K a t₀` is `1 + K / (hubble a t₀ ^ 2 * a t₀ ^ 2)`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «one plus curvature term, positive curvature constant gives above one», «one plus curvature term, positive curvature constant gives above one» only assuming `0 < K`; `hubble a t₀ ≠ 0`; `a t₀ ≠ 0`, «equals one for zero curvature»
- `printedD4y q j s l Ω` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedD4y`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`, `Ω : ℝ`): is defined as `1 / 120 * (359 - 184 * q + 186 * q ^ 2 - 135 * q ^ 3 + 105 * q ^ 4 + 90 * q * j - 105 * q ^ 2 * j - 15 * q * s + -57 * j + 10 * j ^ 2 + 9 * s - l - 5 * Ω * (17 - 6 * q + 9 * q ^ 2 - 2 * j))`

## Author's paraphrase (hand-written; checked only by prose rules)

With the scale factor `Real.exp`, the time `0` and the curvature constant `1`: `printedD4y` rounds to
`3.75`, `correctD4y` to `3.3417`, and `printedD4y` less `correctD4y` to `0.4083`.

## Formal statement (Lean 4)

```lean
theorem F6_fourth :
    RoundsTo (BambaK.printedD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 1 Real.exp 0)) 3.75 2 ∧
    RoundsTo (BambaK.correctD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 1 Real.exp 0)) 3.3417 4 ∧
    RoundsTo (BambaK.printedD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 1 Real.exp 0) - BambaK.correctD4y (decel Real.exp 0)
      (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0) (cosmoCoeff 5 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) 0.4083 4 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.cosmoCoeff`, `Cosmography.BambaK.omega0`, `Cosmography.decel`, `Cosmography.BambaK.printedD4y`, `Cosmography.BambaK.correctD4y`, `Cosmography.hubble`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: cosmoCoeff, omega0, decel.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedD4y².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): unconditional.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = 3.75, k = 2, d = 3.3417, k = 4, d = 0.4083; decel: t = 0; cosmoCoeff: n = 3, t = 0, n = 4, n = 5; omega0: K = 1, t₀ = 0.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 08
