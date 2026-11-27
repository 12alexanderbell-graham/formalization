# Item 11

**Area:** Chemistry

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Chemistry.CubicEOS` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: the Checked theorem `Checked.Trust.NV.rk_constants` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 4 numbered; 4 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: no blind second reading registered; 9 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); program definitions the claim uses (listed under the claim): 1 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 0 of them also determined by a blind reader's specification that they meet (on the domain printed with the definition), 2 with a blind second reading or formulation, 0 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `R : ℝ`, `a : ℝ`, `b : ℝ`, `T : ℝ`, `v : ℝ`:

**assuming**

1. `0 < a`
2. `0 < b`
3. `b < v`
4. the isotherm pressure function of molar volume `p := cubicP R a b 1 0 T` satisfies the critical point condition of an isotherm with the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature; first and second volume derivatives of pressure both vanish; a mere stationary point is not critical)

**then**

1. `cubicP R a b 1 0 T v * v / (R * T) = 1 / 3`
2. `RoundsTo (b * cubicP R a b 1 0 T v / (R * T)) 7780e-5 5`
3. `RoundsTo (a * cubicP R a b 1 0 T v / (R * T) ^ 2) 0.42748 5`

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): phrase (hand-written, linted): the isotherm pressure function of molar volume `p` satisfies the critical point condition of an isotherm with the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature; first and second volume derivatives of pressure both vanish; a mere stationary point is not critical); by definition, means (`deriv p v = 0`) and (`deriv (deriv p) v = 0`). Blind specification readings (part B: a reader who did not see the pinning specification wrote one from the source; `Checked/Trust/SpecAgreement*.lean`): reader E DISAGREES: the definition does not meet the reader's specification (`Checked.Trust.SpecAgreement.not_meets_IsCriticalIsotherm_E`); the reader's specification `Checked.Trust.SecondReadingSpecE.CriticalSpecE` determines it (`Checked.Trust.SpecAgreement.pins_IsCriticalIsotherm_E`) assuming `DifferentiableAt ℝ p v`; `DifferentiableAt ℝ (deriv p) v`; reader F DISAGREES: the definition does not meet the reader's specification (`Checked.Trust.SpecAgreement.not_meets_IsCriticalIsotherm_F`); the reader's specification `Checked.Trust.SecondReadingSpecF.CriticalSpecF` determines it (`Checked.Trust.SpecAgreement.pins_IsCriticalIsotherm_F`) assuming `DifferentiableAt ℝ p v`; `DifferentiableAt ℝ (deriv p) v`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «first and second volume derivatives of pressure both vanish», «a mere stationary point is not critical»
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

Redlich–Kwong / Soave–Redlich–Kwong: at every critical point, Z_c = 1/3 exactly,
Ω_b = 0.07780 and Ω_a = 0.42748 to five decimals.

## Formal statement (Lean 4)

```lean
theorem rk_constants (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 1 0 T) v) :
    cubicP R a b 1 0 T v * v / (R * T) = 1 / 3 ∧
      RoundsTo (b * cubicP R a b 1 0 T v / (R * T)) 0.07780 5 ∧
      RoundsTo (a * cubicP R a b 1 0 T v / (R * T) ^ 2) 0.42748 5 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `rk_constants`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 1, w = 0; RoundsTo: d = 0.08664, k = 5, d = 0.42748.
- Source file: `Checked/Chemistry/CubicEOS.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 11
