# Item 29

**Area:** Astrophysics

**Source:** see the claim

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `S : ℝ`, `w : ℝ → ℝ`, `φ : ℝ → ℝ`:

**assuming**

1. `150 ≤ S`
2. for every `s : ℝ`, if `s ∈ Set.Icc 0 S`, then `HasDerivWithinAt w (φ s) (Set.Icc 0 S) s`
3. `ContinuousWithinAt φ (Set.Icc 0 S) 0`
4. for every `s : ℝ`, if `s ∈ Set.Ioc 0 S`, then `HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Set.Icc 0 S) s`
5. `w 0 = 0`

**then**

- there is `ξ₁ : ℝ` such that there is `ξ₂ : ℝ` such that (`6.4507514 ≤ ξ₁`) and (`ξ₁ ≤ 6.4507515`) and (`67.0075 ≤ ξ₂`) and (`ξ₂ ≤ 67.0076`) and (for every `s : ℝ`, if `s ∈ Set.Icc 0 S`, then if `s ≠ ξ₁`, then `s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi) < ξ₁ ^ 2 * -φ ξ₁ * Real.exp (w ξ₁ / 2) / √(4 * Real.pi)`) and (for every `s : ℝ`, if `s ∈ Set.Icc ξ₁ S`, then if `s ≠ ξ₂`, then `ξ₂ ^ 2 * -φ ξ₂ * Real.exp (w ξ₂ / 2) / √(4 * Real.pi) < s ^ 2 * -φ s * Real.exp (w s / 2) / √(4 * Real.pi)`) and (`0.694366 ≤ ξ₂ ^ 2 * -φ ξ₂ * Real.exp (w ξ₂ / 2) / √(4 * Real.pi)`) and (`ξ₂ ^ 2 * -φ ξ₂ * Real.exp (w ξ₂ / 2) / √(4 * Real.pi) ≤ 0.694367`) and (`2579.69 ≤ Real.exp (-w ξ₂)`) and (`Real.exp (-w ξ₂) ≤ 2579.71`)

## Author's paraphrase (hand-written; checked only by prose rules)

Bonnor–Ebert sphere, min of the mass: for every S ≥ 150 and every solution w of
w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with derivative φ and φ continuous
at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there are ξ₁ between 6.4507514 and 6.4507515 and ξ₂
between 67.0075 and 67.0076 such that m(s) < m(ξ₁) for s in [0, S] with s ≠ ξ₁, m(ξ₂) < m(s) for s in [ξ₁, S]
with s ≠ ξ₂, m(ξ₂) lies between 0.694366 and 0.694367, and the density contrast e^{−w(ξ₂)} lies between
2579.69 and 2579.71.

## Formal statement (Lean 4)

```lean
theorem bonnor_ebert_min (S : ℝ) (hS : 150 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.694366 ≤ ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.694367 ∧
      2579.69 ≤ Real.exp (-w ξ₂) ∧ Real.exp (-w ξ₂) ≤ 2579.71 := …
```

## Definitions it uses

Only Mathlib notions.

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `bonnor_ebert_min`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Math/BonnorEbertMin.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 29
