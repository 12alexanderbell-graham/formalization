# Item 28

**Area:** Falkner–Skan findings F12–F14

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** Fazio, arXiv:1212.5057v1 (2012), p. 16, and the values tabulated in Asaithambi, Fluids 6 (2021) 153, Table 2 (Asaithambi 2005, Zhang–Chen 2009, Salama 2004), and Zhu–Cheng–Wu (2009 preprint), Table 5: five printed values of the attached Falkner–Skan wall shear at β = −0.1988[src=F13_wall_shear] are too large in the fourth significant digit

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**For every** `f : ℝ → ℝ`, `p : ℝ → ℝ`, `q : ℝ → ℝ`:

**assuming**

1. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt f (p η) (Set.Ici 0) η`
2. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt p (q η) (Set.Ici 0) η`
3. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `HasDerivWithinAt q (-(f η * q η) - -1988 / 10000 * (1 - p η ^ 2)) (Set.Ici 0) η`
4. `f 0 = 0`
5. `p 0 = 0`
6. `Filter.Tendsto p Filter.atTop (nhds 1)`
7. for every `η : ℝ`, if `η ∈ Set.Ici 0`, then `0 < q η`
8. for every `M : ℝ`, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`

**then**

- `RoundsTo (printedFazioWall - q 0) 3e-6 6`

Program definitions in this claim:

- `RoundsTo x d k` — MATH, not pinned; name and body agree with a blind second formulation (`Checked.Trust.Formulations.agree_RoundsTo`) (for `x : ℝ`, `d : ℝ`, `k : ℕ`): means `|x - d| ≤ 1 / (2 * 10 ^ k)`
- `printedFazioWall` — PRINTED, not pinned; an independent blind second reading of the source agrees with this transcription (`Checked.Trust.Transcriptions.agree_printedFazioWall`); its name is not checked: is defined as `5221e-6`

## Author's paraphrase (hand-written; checked only by prose rules)

Falkner–Skan with β = −1988/10000: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then `RoundsTo (printedFazioWall - q 0) 3e-6 6`, with `printedFazioWall` the wall shear value Fazio printed
for that β.

## Formal statement (Lean 4)

```lean
theorem F13_wall_shear (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    RoundsTo (printedFazioWall - q 0) 0.000003 6 := …
```

## Definitions it uses

See GLOSSARY.md: `Records.printedFazioWall`, `Records.RoundsTo`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: —.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): printedFazioWall².
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `F13_wall_shear`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): RoundsTo: d = 0.000003, k = 6.
- Source file: `Checked/Records/FalknerSkan.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 28
