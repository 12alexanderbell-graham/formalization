# Item 36

**Area:** Chemistry

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** generalized two-parameter cubic equation of state: van der Waals (1873), Redlich & Kwong, Chem. Rev. 44, 233 (1949), Soave, Chem. Eng. Sci. 27, 1197 (1972), Peng & Robinson, Ind. Eng. Chem. Fundam. 15, 59 (1976)

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** **The source's own form, as a blind reader wrote it from the source without seeing this statement (each body occurs in the statement below, `check_literals.py`):** `Checked.Trust.SecondReading.kappaPR76` := `fun ω => 0.37464 + 1.54226 * ω - 0.26992 * ω ^ 2`. the statement is proved in module `Checked.Chemistry.PRAcentric` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: the Checked theorem `Checked.Trust.NV.pr_omega1_exists` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 4 numbered; 4 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); assumptions the numbering does not reach or reaches only formally (`TRUST_MAP.md`, shape): bundled 4; PART A INCOMPLETE (shape entries). **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: 1 definitions written by a blind second reader of the source are registered for this statement in `scripts/trust/literal_readings.txt` and occur in it (`check_literals.py`) (printed at the head of this line); 15 literals of the statement are grandfathered as never read twice (`scripts/trust/literal_baseline.txt`); program definitions the claim uses (listed under the claim): 2 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 0 of them also determined by a blind reader's specification that they meet (on the domain printed with the definition), 3 with a blind second reading or formulation, 0 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `R : ℝ`, `ac : ℝ`, `b : ℝ`, `Tc : ℝ`, `v : ℝ` (renamed by the generator after the pinned slot it fills; the statement calls it `vc`):

**assuming**

1. `0 < ac`
2. `0 < b`
3. `b < v`
4. the isotherm pressure function of molar volume `p := cubicP R ac b 2 (-1) Tc` satisfies the critical point condition of an isotherm with the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature; first and second volume derivatives of pressure both vanish; a mere stationary point is not critical)

**then**

- there is `vl : ℝ` such that there is `vg : ℝ` such that there is `ps : ℝ` such that (`b < vl`) and (the isotherm pressure function of molar volume `p := cubicP R (ac * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - √(7 / 10))) ^ 2) b 2 (-1) (7 / 10 * Tc)` satisfies the Maxwell equal area coexistence condition with the liquid molar volume `vl`, the gas molar volume `vg` and the saturation pressure `ps` (liquid volume is less than gas volume; pressure equals the saturation pressure at both volumes; equal areas between the isotherm and the saturation pressure line; pressure is a function of molar volume at fixed temperature)) and (`RoundsTo (ps / cubicP R ac b 2 (-1) Tc v) 114e-4 4`) and (`RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc v)) 0.942 3`)

Program definitions in this claim:

- `IsCriticalIsotherm p v` — **PINNED** (pin theorem `criticalSpec_pins`): phrase (hand-written, linted): the isotherm pressure function of molar volume `p` satisfies the critical point condition of an isotherm with the molar volume at the point `v` (pressure as a function of molar volume at fixed temperature; first and second volume derivatives of pressure both vanish; a mere stationary point is not critical); by definition, means (`deriv p v = 0`) and (`deriv (deriv p) v = 0`). Phrase lines proved in Lean (statements in PHRASE_LINES.md): «first and second volume derivatives of pressure both vanish», «a mere stationary point is not critical»
- `IsMaxwellCoexistence p vl vg ps` — **PINNED** (pin theorem `maxwellSpec_pins`): phrase (hand-written, linted): the isotherm pressure function of molar volume `p` satisfies the Maxwell equal area coexistence condition with the liquid molar volume `vl`, the gas molar volume `vg` and the saturation pressure `ps` (liquid volume is less than gas volume; pressure equals the saturation pressure at both volumes; equal areas between the isotherm and the saturation pressure line; pressure is a function of molar volume at fixed temperature); by definition, means (`vl < vg`) and (`p vl = ps`) and (`p vg = ps`) and (`∫ (v : ℝ) in vl..vg, p v = ps * (vg - vl)`). Phrase lines proved in Lean (statements in PHRASE_LINES.md): «liquid volume is less than gas volume» only assuming the isotherm pressure function of molar volume `p` satisfies the Maxwell equal area coexistence condition with the liquid molar volume `vl`, the gas molar volume `vg` and the saturation pressure `ps` (liquid volume is less than gas volume; pressure equals the saturation pressure at both volumes; equal areas between the isotherm and the saturation pressure line; pressure is a function of molar volume at fixed temperature), «pressure equals the saturation pressure at both volumes» only assuming the isotherm pressure function of molar volume `p` satisfies the Maxwell equal area coexistence condition with the liquid molar volume `vl`, the gas molar volume `vg` and the saturation pressure `ps` (liquid volume is less than gas volume; pressure equals the saturation pressure at both volumes; equal areas between the isotherm and the saturation pressure line; pressure is a function of molar volume at fixed temperature), «equal areas between the isotherm and the saturation pressure line» only assuming the isotherm pressure function of molar volume `p` satisfies the Maxwell equal area coexistence condition with the liquid molar volume `vl`, the gas molar volume `vg` and the saturation pressure `ps` (liquid volume is less than gas volume; pressure equals the saturation pressure at both volumes; equal areas between the isotherm and the saturation pressure line; pressure is a function of molar volume at fixed temperature)
- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `acentric ps pc` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_acentric`) (for `ps : ℝ`, `pc : ℝ`): is defined as `-Real.logb 10 (ps / pc) - 1`
- `cubicP R a b u w T v` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_cubicP`) (for `R : ℝ`, `a : ℝ`, `b : ℝ`, `u : ℝ`, `w : ℝ`, `T : ℝ`, `v : ℝ`): is defined as `R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)`

## Author's paraphrase (hand-written; checked only by prose rules)

Peng–Robinson fluid with Soave's temperature function and the published κ(ω) at ω = 1: at
any critical point (v_c > b) there is a Maxwell coexistence state at T = 0.7 T_c with liquid
volume above the co-volume b, and its pressure is 0.0114 times the critical pressure
(4 decimals) and its acentric factor 0.942 (3 decimals).

## Formal statement (Lean 4)

```lean
theorem pr_omega1_exists (R ac b Tc vc : ℝ) (hac : 0 < ac) (hb : 0 < b) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence
        (cubicP R (ac * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
          b 2 (-1) (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R ac b 2 (-1) Tc vc) 0.0114 4 ∧
      RoundsTo (acentric ps (cubicP R ac b 2 (-1) Tc vc)) 0.942 3 := …
```

## Definitions it uses

See GLOSSARY.md: `Chemistry.Coexistence.IsMaxwellCoexistence`, `Chemistry.CubicEOS.IsCriticalIsotherm`, `Chemistry.Coexistence.acentric`, `Chemistry.CubicEOS.cubicP`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsMaxwellCoexistence, IsCriticalIsotherm.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `pr_omega1_exists`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): cubicP: u = 2, w = -1; RoundsTo: d = 0.0114, k = 4, d = 0.942, k = 3.
- Source file: `Checked/Chemistry/PRAcentric.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 36
