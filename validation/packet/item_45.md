# Item 45

**Area:** Certified numbers of the findings

**Source:** Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583v2, App. A, Eq. (A2): lookback-distance z⁵ coefficient, 7/2 q₀⁴ should be 7/8 q₀⁴

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `a : ℝ → ℝ`, `t₀ : ℝ`:

**assuming**

1. the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`3 / 10`·(1 + z)³ + 1 − `3 / 10`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood
2. `ContDiffAt ℝ 6 a t₀`

**then**

1. `RoundsTo (correctD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) 0.2153 4`
2. `RoundsTo (printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) 0.4555 4`
3. `RoundsTo (printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) - correctD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) 0.24 2`
4. `RoundsTo (decel a t₀) (-0.55) 2`

Program definitions in this claim:

- `IsFlatLCDM Ω a t₀` — **PINNED** (pin theorem `flatLCDMSpec2_pins`): the scale factor `a` obeys the flat ΛCDM expansion law H = H₀·√(`Ω`·(1 + z)³ + 1 − `Ω`) on some neighbourhood of the time `t₀`, where H₀ = H(`t₀`) > 0, z is the redshift observed at `t₀`, and a is positive and differentiable on that neighbourhood
- `RoundsTo x d k` — MATH, not pinned, so only the formula shown is checked, not its name (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `correctD4 q j s l` — FORMULA, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_correctD4`) (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 8 * q ^ 4 - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j - j + j ^ 2 / 12 - 1 / 8 * q * s - s / 6 - l / 120`
- `cosmoCoeff n a t` — **PINNED** (pin theorem `cosmoCoeffCore_pins`): the `n`-th cosmographic coefficient a⁽ⁿ⁾(t)/(a(t)·H(t)ⁿ) of the scale factor `a` at time `t` (n = `n`; j, s, l, m for n = 3, 4, 5, 6; the deceleration parameter is minus the n = 2 coefficient)
- `decel a t` — **PINNED** (pin theorem `decelSpec_pins`): the deceleration parameter −a″(t)·a(t)/a′(t)² of the scale factor `a` at time `t`
- `printedD4 q j s l` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedD4`); its name is not checked (for `q : ℝ`, `j : ℝ`, `s : ℝ`, `l : ℝ`): is defined as `1 + 2 * q + 3 * q ^ 2 + 5 / 2 * q ^ 3 + 7 / 2 * q ^ 4 - 5 / 3 * q * j - 7 / 8 * q ^ 2 * j - j + j ^ 2 / 12 - 1 / 8 * q * s - s / 6 - l / 120`

## Author's paraphrase (hand-written; checked only by prose rules)

In every flat ΛCDM model with `Ω_m = 0.3` (q₀ = −0.55): the correct lookback `D⁴` is
`0.4555`, the printed one `0.2153`, the excess `printed − correct` is `0.24`, and `q₀ = −0.55`.

## Formal statement (Lean 4)

```lean
theorem F3_D4_LCDM (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM (3 / 10) a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) :
    RoundsTo (CCS.correctD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.2153 4 ∧
    RoundsTo (CCS.printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.4555 4 ∧
    RoundsTo (CCS.printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀) - CCS.correctD4 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀)) 0.24 2 ∧
    RoundsTo (decel a t₀) (-0.55) 2 := …
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.Aviles.IsFlatLCDM`, `Cosmography.Aviles.cosmoCoeff`, `Cosmography.decel`, `Cosmography.CCS.printedD4`, `Cosmography.CCS.correctD4`, `Cosmography.hubble`, `Cosmography.redshift`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: IsFlatLCDM, cosmoCoeff, decel.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedD4².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `F3_D4_LCDM`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): IsFlatLCDM: Ω = 3/10; RoundsTo: d = 0.2153, k = 4, d = 0.4555, d = 0.24, k = 2, d = -0.55; cosmoCoeff: n = 3, n = 4, n = 5.
- Source file: `Checked/Records/Findings.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 45
