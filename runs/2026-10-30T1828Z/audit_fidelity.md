# Fidelity audit (annex XL) for the promotion of `Checked/Fidelity/` (run 1828Z)

Promoted: `Checked.Fidelity.LumDistSpec`, `HubbleSpec`, `DecelSpec`, `AngDistSpec`, `FlatLCDMSpec` (+ `*_meets_spec`), and `Pins.lean` (`decelSpec_pins`, `angDistSpec_pins`, `hubbleSpec_pins`, `LumDistSpec2`, `lumDist_meets_spec2`, `lumDistSpec2_pins`). The headline content is the spec structures (the claim "these are the textbook laws") and the pinning theorems.

- **Frozen statement:** LumDistSpec fields at 2c97869; Hubble/Decel/AngDist/FlatLCDM specs at b68bff5 (before any refutation); LumDistSpec2 at afc0d78. Unchanged since, except the `lcdm` docstring (Λ/3 nit, referee).
- **Blind authorship:** MoreSpecs written by a subagent that saw only the definitions, not the mutants. LumDistSpec written by the run before any mutant existed.
- **Referee** (`referee_specs.md`, subagent seeing only the structures): every field physically correct; all closed forms re-derived and checked with sympy (`referee_check.py`). One convention (UNCLEAR, accepted): `FlatLCDMSpec.notPastOnly` requires the Friedmann law on both sides of t₀, as the docstring says and as `IsFlatLCDM` (∀ᶠ in 𝓝 t₀) intends. Etherington field relies on `1 + redshift = a(t₀)/a(t)`, which is the definition (`Checked.Cosmography.redshift`).
- **Not vacuous:** each spec is satisfied by the program's definition (`*_meets_spec`, `lumDist_meets_spec2`).
- **Not trivial / bites:** 30/30 blind mutants and 10/10 author mutants refuted in Lean (Work/Fidelity/*Check.lean); 4 adversarial gaps of the anchors-only `LumDistSpec` refuted by `LumDistSpec2`.
- **Junk values:** no field requires junk behaviour (referee); `DecelSpec` leaves ȧ = 0 free; pins are stated only on the physical domain (a > 0, continuity/differentiability, t ≤ t₀).
- **Quantifiers/types:** pins quantify over every K, every admissible a, t ≤ t₀; signatures match the definitions.
- **Classification of residual risk:** Underspecified — `FlatLCDMSpec` does not pin `IsFlatLCDM`. Translation — the laws were written by the same model family as the definitions; anchors and the sympy referee are the independent checks.

Verdict: AUDITED. Status after green CI on the promotion commit: PROVED (Checked, standard axioms).
