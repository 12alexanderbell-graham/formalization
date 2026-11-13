# Item 01

**Area:** Falkner–Skan findings F12–F14

**Source:** Fazio, arXiv:1212.5057v1 (2012), Fig. 4 caption (p. 28), and arXiv:2011.07725v1 (2020), Fig. 7 caption (p. 22): the Falkner–Skan separation parameter of the zero-wall-shear solution is printed wrong in its last digit

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `β : ℝ`, `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`:

**assuming**

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Set.Ici 0) η`
4. `f 0 = 0`
5. `p 0 = 0`
6. `q 0 = 0`
7. `Filter.Tendsto p Filter.atTop (nhds 1)`
8. for every `η : ℝ`, if `η ∈ Set.Ioi 0`, then `0 < q η`
9. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`

**then**

- `RoundsTo (printedFazioSeparation - β) 14e-8 8`

Program definitions in this claim:

- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `printedFazioSeparation` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedFazioSeparation`); its name is not checked: is defined as `-(1988376 / 10000000)`

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan separation: for every solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0,
p(0) = 0, wall shear q(0) = 0, p → 1, q > 0 on (0, ∞) and, for every M,
`∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`: `RoundsTo (printedFazioSeparation - β) 14e-8 8`, with
`printedFazioSeparation` the value Fazio printed for that parameter.

## Formal statement (Lean 4)

```lean
theorem F12_separation {β : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 0) (hl : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ioi (0 : ℝ), 0 < q η) (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    RoundsTo (printedFazioSeparation - β) 0.00000014 8 := …
```

## Definitions it uses

See GLOSSARY.md: `Records.printedFazioSeparation`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedFazioSeparation².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `F12_separation`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = 0.00000014, k = 8.
- Source file: `Checked/Records/FalknerSkan.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 01
