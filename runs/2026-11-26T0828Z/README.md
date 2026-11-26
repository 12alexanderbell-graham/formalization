# Run 2026-11-26T0828Z

**THE RESULT:** part 3 by rotation (STATE 3n; next step STATE 3q). The parametric closure, its bench, red team BB and the decision are in section What we did; details `t5/RESULTS_PARAM.md`.

**What can a scientist now trust without checking it themselves, that they could not before?** That a fidelity objection can no longer be marked closed by an equivalence that holds only because both statements are true: the rule the claims page now runs asks for the equivalence at every value of the headline's literals and for a proof that the literals bite, so the red-team forgeries of run 0228Z cannot even be stated; closures stay suspended because a reading written with the headline in hand still passes (section What we did).

**Weakest unchecked step:** the reading. A closure is only as good as the blind reading on its left side, and no check yet tells a reading that restates the headline beside a condition true at its literals from an honest one (section Next).

## Start
- 08:28Z. Session clone on the stale local `main` (860fd46, its commits are ancestors of origin/main); worked from origin/main a96a329, then `scripts/start_run.sh`; no LOCK (taken 3f646b8, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of 7800b90 (artifact of 45776804653) restored by streaming; `lake build Checked` (3828 jobs, replayed). Subagents: one Sonnet red teamer, one fork (bench).
- CI read first: 45776804653 (7800b90, run 0628Z's final push) green on every job. Nothing to promote (necessity theorems only).

## Bottleneck (and what a yes/no changes)
- Section Next of run 0228Z: closures of fidelity objections are suspended because the rule decided by constant names. Does a closure parametric in the headline's literals accept honest closures of real headlines and reject forgeries? Yes → objections can be answered by evidence again. No → the remaining class is named and the route stays suspended (pre-registered: re-enable only if no forgery passes).

## What we did
1. **Rule** (`t5/pclosure_rule.lean`, then `pclosure_rule_v2.lean`, now `Claims.paramClosureFaults`): the closure states `∀ c, X ↔ H[c]` with every real literal of the headline other than 0 and 1 a variable (exact evaluation of numerals; instances only from Lean/Mathlib), `X` at the literals is the blind reading up to the value of its numerals, `X` keeps no numeral of a literal's value and does not contain `H[c]`, and `t.bite : ¬ ∀ c, H[c]`; any theorem may be used in the proof. 13 controls (3 valid, 10 forged, each as planted), run on every generation of the claims page.
2. **Bench** (fork, from run 0228Z's six bridges): 3/4 accepted by the first version, **4/4 by v2** (proofs inside statements erased: the Homann reading's `ContinuousSMul` proof was an abstracted `_proof_1`). The B1 third-coefficient bridge cannot be parametric: it needs the strict order of the times from the literal values.
3. **Red team BB** (Sonnet, brief committed alone 66894eb): **2/2 forgeries accepted** by the first version, Gelfand bound and Hiemenz existence: the reading is `(c ≥ A) ∨ H′(c)` at the literals, `H′` the headline restated, `A` the literal re-spelt through a cast of a natural number. v2 evaluates casts and rejects both; this run's variant with `√(3.321992119 ^ 2)` passes v2. A re-spelling check is always one re-spelling behind.
4. **Decision (pre-registered): closures stay suspended.** `Claims.lean` checks any closed field with the parametric rule (`closed by <theorem> reading <definition>`) and still makes it a blocking error; both pages' header describes the rule and says no closure is accepted (red teams of runs 0228Z and 0828Z). `objections.txt` has no entry; no page entry changes.

## Measure
- Honest closures of real headlines falsely rejected: 6/6 (rule of run 2028Z) → 0/6 (run 0228Z, names rule) → 0/4 parametric v2 (one bridge not expressible parametrically).
- Forged closures accepted: BA forgeries (`True ↔ H`, inlined proof) cannot be stated under the parametric rule (`∀ c, True ↔ H[c]` contradicts the bite); BB 2/2 accepted by v1, 0/2 by v2; own re-spelt variant 1/1 accepted by v2. Forged closures the page can show as closed: 0 (suspension).
- Controls of closure rules on the page: 16 → 29 (13 parametric).
- Trust map unchanged (no Lean module added; 315 claims).

## Next
- CI read first: the run of this run's final push (Claims.lean with the parametric rule and its controls, the two pages). Green on every job → nothing to promote. Red → its first failing command with the newest ancestor green on every job (7800b90) as base.
- Part 3 next: a check on the reading before closures return (`t5/RESULTS_PARAM.md` section 6): (a) no disjunct, conjunct or premise of the reading at its literals is decided by `norm_num` alone; (b) the reading, after the reader's definitions are unfolded, does not contain the headline up to commutation of `∧`, `∨` and `<`/`>`; measure both on the bench readings (false rejections) and on BB's three forgeries, then a fresh red team. Then the fifth round on `headlines.txt` and the multi-token reader constants (section Next of `runs/2026-11-25T1428Z/README.md`).
- Part 1 next: as in section Next of `runs/2026-11-26T0628Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-26T0428Z/README.md`.

## End
