# Item 17

**Area:** T1 fidelity

**Source (hand-written: the author's title of the finding or a fixed source line; no check reads it):** standard FLRW cosmology definitions (e.g. Weinberg, Cosmology, 2008; Hogg 1999, astro-ph/9905116); the specification each definition is pinned by is in the statement

## Claim generated from the Lean statement (machine-produced; this is what was proved)

**Status (generated):** the statement is proved in module `Checked.Fidelity.Pins` of `Checked`; axioms, computed by Lean when this page was generated: `Classical.choice`, `Quot.sound`, `propext`. This status is decided by Lean and the registry `scripts/trust/headlines.txt`, never by prose: a headline is withdrawn only by removing it from `Checked` and the registry, which removes it from this page. **Fidelity record (generated; what has been machine-checked about what the statement means, not a proof that it matches its source), in two parts. (A) Re-derived by the kernel from the statement; holds whoever wrote the statement, its witnesses and its proofs; shows the statement is not vacuous and which hypotheses matter, not that it says what its source says:** non-vacuity: the Checked theorem `Checked.Trust.NV.hubbleSpec_pins` states the obligation `Checked.Trust.nvObligation` computes from the statement (data exist that meet its hypotheses); hypotheses: 3 numbered; 3 shown needed (a Checked example meets every other hypothesis and the conclusion fails), 0 shown redundant (the statement is proved without it, one at a time), 0 with no obligation (instance or proof used as data), 0 open (per hypothesis: `TRUST_MAP.md`, section "Hypothesis necessity"); no assumption outside the numbering (`TRUST_MAP.md`, shape); part A complete. **(B) Rests on who wrote a statement; CI checks the route of each item (commit order, briefs without the answer), not that its writer was independent of the authors, so each item is evidence of meaning only as far as that independence holds:** open fidelity objections on record (`scripts/trust/objections.txt`, where every objection to the meaning of a listed headline is entered when it is first written anywhere): none; statement literals: no blind second reading registered; no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof); program definitions the claim uses (listed under the claim): 1 pinned by a specification the program wrote (the kernel checks that the specification determines the definition, not that it says what the source means), 0 with a blind second reading or formulation, 1 with neither (only the formula printed is checked). The statement is frozen (`scripts/trust/frozen.txt`): changing it needs a `LEDGER.md` entry naming it (`check_relock.py`), and a changed statement changes the claim on this page. CI regenerates this page on every push and fails if the committed copy differs, so it cannot lag the Lean sources.

**For every** `H : (ℝ → ℝ) → ℝ → ℝ`, `a : ℝ → ℝ`, `t : ℝ`:

**assuming**

1. `HubbleSpec H`
2. `0 < a t`
3. `DifferentiableAt ℝ a t`

**then**

- `H a t = hubble a t`

Program definitions in this claim:

- `HubbleSpec` — SPEC, not pinned: inductive type with constructors `HubbleSpec.mk : ∀ {H : (ℝ → ℝ) → ℝ → ℝ}, (∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → DifferentiableAt ℝ a t → HasDerivAt (fun s => Real.log (a s)) (H a t) t) → (∀ (h t : ℝ), H (fun s => Real.exp (h * s)) t = h) → (∀ (n t : ℝ), 0 < t → H (fun s => s ^ n) t = n / t) → (∀ (R t : ℝ), 0 < R → H (fun x => R) t = 0) → (∀ (c : ℝ), 0 < c → ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → DifferentiableAt ℝ a t → H (fun s => c * a s) t = H a t) → (∀ (τ : ℝ) (a : ℝ → ℝ) (t : ℝ), 0 < a (t + τ) → DifferentiableAt ℝ a (t + τ) → H (fun s => a (s + τ)) t = H a (t + τ)) → (∀ (a : ℝ → ℝ) (t : ℝ), 0 < a (-t) → DifferentiableAt ℝ a (-t) → H (fun s => a (-s)) t = -H a (-t)) → HubbleSpec H`
- `hubble a t` — **PINNED** (pin theorem `hubbleSpec_pins`): phrase (hand-written, linted): the Hubble rate with the scale factor `a` and the cosmic time of evaluation `t` (logarithmic derivative of the scale factor with respect to cosmic time; positive for expansion and negative for contraction); by definition, `hubble a t` is `deriv a t / a t ^ 2`. Phrase lines proved in Lean (statements in PHRASE_LINES.md): «logarithmic derivative of the scale factor with respect to cosmic time» only assuming `0 < a t`; `DifferentiableAt ℝ a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `0 < deriv a t`, «positive for expansion and negative for contraction» only assuming `0 < a t`; `deriv a t < 0`

## Author's paraphrase (hand-written; checked only by prose rules)

`HubbleSpec` pins `hubble` for every positive scale factor differentiable at `t`
(its `logDeriv` law `H = d ln a/dt` and uniqueness of derivatives).

## Formal statement (Lean 4)

```lean
theorem hubbleSpec_pins (H : (ℝ → ℝ) → ℝ → ℝ) (h : HubbleSpec H) (a : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) : H a t = hubble a t := …
```

Definitions specific to this item:

```lean
/-- The Hubble rate `H = ȧ/a`. (Used by this item in place of the glossary entry.) -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t ^ 2
```

## Definitions it uses

See GLOSSARY.md: `Cosmography.hubble`, `Fidelity.HubbleSpec`

## What the system checked mechanically

- Proof checked by the Lean kernel in CI (Lean 4 + Mathlib), standard axioms only.
- Definitions pinned by a machine-checked specification: hubble.
- Printed formulas used (transcriptions; ² = machine-checked agreement with a blind second reading): —.
- Non-vacuity (all hypotheses satisfiable at once, machine-checked witness): `hubbleSpec_pins`.
- Parameters the statement fixes to numbers (generated from the statement; the claim is proved for these values only): —.
- Source file: `Checked/Fidelity/Pins.lean` (do not open it before submitting your answers).

## Your answers: use ANSWER_FORM.md, item 17
