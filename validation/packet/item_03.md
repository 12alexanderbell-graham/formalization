# Item 03

**Area:** Astrophysics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `S : ℝ`, `w : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. `7 ≤ S`
2. for every `s : ℝ`, if `s ∈ Set.Icc 0 S`, then `HasDerivWithinAt w (φ s) (Set.Icc 0 S) s`
3. `ContinuousWithinAt φ (Set.Icc 0 S) 0`
4. for every `s : ℝ`, if `s ∈ Set.Ioc 0 S`, then `HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Set.Icc 0 S) s`
5. `w 0 = 0`

**then**

- there is `ξ₁ : ℝ` such that (`6.4507514 ≤ ξ₁`) and (`ξ₁ ≤ 6.4507515`) and (`StrictMonoOn (fun s => s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi)) (Set.Icc 0 ξ₁)`) and (`StrictAntiOn (fun s => s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi)) (Set.Icc ξ₁ 7)`) and (`1.1822265 ≤ ξ₁ ^ 2 * -φ ξ₁ * Real.exp (w ξ₁ / 2) / √(4 * Real.pi)`) and (`ξ₁ ^ 2 * -φ ξ₁ * Real.exp (w ξ₁ / 2) / √(4 * Real.pi) ≤ 1.1822266`) and (`14.042032 ≤ Real.exp (-w ξ₁)`) and (`Real.exp (-w ξ₁) ≤ 14.042033`)

## Author's paraphrase (hand-written; checked only by prose rules)

Bonnor–Ebert critical sphere: for every S ≥ 7 and every solution w of w'' + (2/s)w' + e^w = 0 on
(0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous at 0, there is a radius ξ₁
between 6.4507514 and 6.4507515 such that the dimensionless mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π)
increases strictly on [0, ξ₁] and decreases strictly on [ξ₁, 7]; there the mass lies between 1.1822265 and
1.1822266 and the centre-to-edge density contrast e^{−w(ξ₁)} between 14.042032 and 14.042033.

## Formal statement (Lean 4)

```lean
theorem bonnor_ebert_critical (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc 0 ξ₁) ∧
      StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc ξ₁ 7) ∧
      1.1822265 ≤ ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 ∧
      14.042032 ≤ Real.exp (-w ξ₁) ∧ Real.exp (-w ξ₁) ≤ 14.042033 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `bonnor_ebert_critical`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/BonnorEbert.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 03
