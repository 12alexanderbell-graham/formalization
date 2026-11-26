# Parametric closure: bench, red team BB, decision — run 2026-11-26T0828Z (part 3)

Question (section Next of `runs/2026-11-26T0228Z/README.md`): run 0228Z suspended closures of fidelity objections
after red team BA forged `True ↔ H` by inlining the program's own proof of a headline. The planned repair: a closure
parametric in the headline's literals. Does it accept honest closures of real headlines and reject forgeries?
Pre-registered (that README): re-enable closures only if no forgery passes.

## 1. The rule (`pclosure_rule.lean`, then `pclosure_rule_v2.lean`; now `Claims.paramClosureFaults`)

For a headline `H` with varied literals `c₀` (maximal closed real numerals other than 0 and 1, evaluated exactly:
`OfNat`, `OfScientific`, `+ − × ÷`, natural powers, casts of integer literals, instances only from Lean/Mathlib), a
closure is a theorem `t : ∀ c₁ … cₙ : ℝ, X ↔ H[c]` and `t.bite : ¬ ∀ c, H[c]`, where

- `H[c]` is `H` with each literal replaced by one variable (any order, each once; proofs inside statements erased);
- `X` at `c₀` is the body of the blind reading `rn` (a `def rn : Prop` of a `Checked.Trust.SecondReading*` module), up to
  the value of real numerals (`7.5` = `15 / 2`) and with the reader's own definitions unfolded;
- `X` keeps no numeral whose value is one of the literals, and does not contain `H[c]` as a proper part;
- both on the standard axioms. Any theorem may be used in the proofs: the statement carries the meaning.

Why it should help: `True ↔ H[c]` for every `c` contradicts the bite, so the BA forgeries cannot even be stated;
an honest bridge (rcases, unfold, simp) rarely uses the literal values, so it generalises.

## 2. Controls (`controls_body.lean`; in `Claims.lean` as `ParamControls`)

3 valid (`good`, `good_order`, `good_norm`: 1.5 against 3/2) accepted; 10 forged rejected for the reason each plants
(old shape, literals kept, one literal kept, no bite, wrong bite, headline inside a case split, wrong reading, not a
reading, no literal, a case split on the literals with the headline restated — the last accepted by the first version).

## 3. Bench of honest closures (`pbench_body.lean`, written by a fork from run 0228Z's bench)

| bridge | headline (varied literals) | first version | v2 |
|---|---|---|---|
| B1 | `hiemenz_exists` (2) | ACCEPTED | ACCEPTED |
| B2 | `hiemenz_under` (3; the reading writes 7.5, the headline 15/2) | ACCEPTED | ACCEPTED |
| B3 | `homann_exists` (3, incl. the 2 of the equation) | REJECTED: the reader's helper inlined carries Lean's `HomannSol._proof_1` for `ContinuousSMul ℝ ℝ`, the closure the full proof | ACCEPTED (proofs erased) |
| B4 | `gelfand_pde_bound` (1) | ACCEPTED | ACCEPTED |
| B5 | `third_coefficient_lower_bound` | not closable: the bridge needs t₃ < t₂ < t₁ < t₀ from the values √2 − 1 ≠ 0 …; with the 2 and 4 varied, at √1 − 1 = 0 the two statements differ | — |

Outputs: `pbench.out` (first version), `v2_all.out` (v2: controls, bench, the three forgeries). Bites: degenerate values (a = b = 0; empty interval; Gelfand
u = 0, λ = 0, c = −1). Honest false rejections: 1/4 → 0/4; one headline whose bridge depends on the literal values.

## 4. Red team BB (brief committed alone first, 66894eb; Sonnet; `redteamBB/`)

2 attempts, **2 forgeries ACCEPTED** by the first version (Gelfand bound; Hiemenz existence, two literals). Mechanism:
the reading is `P c₀` with `P c := (c ≥ A) ∨ H′(c)`, `H′` the headline restated (reordered, so the containment check
misses it) and `A` the literal re-spelt as `1e-9 · ↑3321992119` (a cast the evaluator did not read). `c ≥ A` implies
`H[c]` from the program's own theorem by monotonicity, so `∀ c, P c ↔ H[c]` holds and the literals bite; at the
literals the first disjunct is `c₀ ≥ c₀`: the reading is a tautology.

v2 evaluates casts: both BB forgeries REJECTED ("keeps a numeral equal to a literal"). **But the class stays open**:
this run's own variant `own/a3_body.lean` re-spells the literal as `√(3.321992119 ^ 2)` (a numeral of another value
under a function the evaluator cannot read) and is ACCEPTED by v2. Every re-spelling check can be met by another
re-spelling (`Real.log`, a natural number built from small literals under a bound variable, …).

## 5. What the measure says

- The parametric rule does what the names rule could not: an equivalence of truth values at the printed literals
  (`True ↔ H`, the program's proof inlined) cannot be stated; an honest reading that is weaker or stronger than the
  headline (λ ≤ 3.4 against λ ≤ 3.321992119) gives a false family equivalence (fails at c = 3.3), so no proof exists.
- What passes: a reading that already contains the headline (restated) beside a condition true at the literals. Such a
  reading is not a blind reading of the source; it was written by someone who had the headline. No rule on the
  closure's statement can tell a re-spelt literal from an honest constant, so this residue belongs to the check on
  the reading (its provenance, or a test that no part of it is decided by arithmetic alone).
- **Decision (pre-registered): closures stay suspended.** `Claims.lean` now runs `paramClosureFaults` on any closed
  field (`closed by <theorem> reading <definition>`) and still turns it into a blocking error; the 13 controls run on
  every generation. Forged closures the page can show as closed: 0.

## 6. Next

A check on the reading itself before closures return: (a) no disjunct, conjunct or premise of the reading at its
literals is decided by `norm_num` alone (the BB shape), measured on the bench readings for false rejections; (b) a
reading may not reach a statement equivalent to the headline under the reader's own definitions (the containment
check, after unfolding, up to commutation of `∧`, `∨` and `<`/`>`); then a fresh red team. Also B5: a closure whose
bridge needs the literal values (strict order of the times) needs the variables restricted to a box around the
literals, which reopens the case-split class: measure before allowing it.
