# Run 2026-11-26T0228Z

**THE RESULT:** part 3 by rotation (STATE 3m; next step STATE 3n). The bench, the two red-team rounds and the decision are in section What we did; details `t5/RESULTS_BENCH.md`.

**What can a scientist now trust without checking it themselves, that they could not before?** That a fidelity objection shown open on the claims page cannot be shown closed by a Lean equivalence that a red team has learned to forge: the page now accepts no closure, and says so in its header, after a red team made the closure rule accept `True ↔` a certified headline by inlining the program's own proof (section What we did).

**Weakest unchecked step:** an objection can be recorded but no longer closed: the planned repair (a closure parametric in the headline's literals) is unbuilt and unmeasured (section Next).

## Start
- 02:28Z. Local `main` was the stale clone 860fd46 (its commits are ancestors of origin/main; kept as local branch `stale-local-main`); set to origin/main bea2448, then `scripts/start_run.sh`; no LOCK (taken a304792, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of 3a7afbb (artifact of 45734700171) restored by streaming; `lake build Checked` replayed it (3815 jobs). Subagent: one Sonnet red teamer (two rounds).
- CI read first: 45734700171 (3a7afbb, run 0028Z's final push) green on every job (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4). Nothing to promote (necessity theorems only).

## Bottleneck (and what a yes/no changes)
- Section Next of run 2028Z: measure the closure rule of test AZ on real bridges (false rejections) and attack it with a forged closure. Yes (honest closures pass, forgeries fail) → objections can be answered by evidence. No → the route is repaired or withdrawn before any objection relies on it.

## What we did
1. **Closure bench** (prediction committed first, 8973b62): six honest bridges `R ↔ H` of five real headlines (Hiemenz and Homann existence, the Hiemenz undershoot, the Gelfand bound, the B1 third-coefficient bound) against blind readers' statements from `Work/**/…Blind.lean`, run through the page's rule copied verbatim (`scripts/bench_closure.sh`). **6/6 rejected**, every one through proofs Lean abstracts out of a definition's body (`(9 + 1).AtLeastTwo` for a numeral 10, `ContinuousSMul ℝ ℝ`), one also through an equation lemma (`rw`), one through Mathlib-only helpers. The route could not have closed an objection on any real headline: the controls of run 2028Z had no numeral.
2. **First fix:** auxiliary proofs, equation lemmas and helpers of the closure are followed under the same rule instead of rejected (statements and proofs checked all the way down; proofs scanned by the closed-subterm rule). Bench 6/7 accepted (the seventh puts helpers outside the closure's name, by design). Controls: three valid that the old rule rejects (checked one at a time, `scripts/run_controls.sh`), four forged.
3. **Red team BA, round 1** (brief committed alone, adcd0f6): 8 attempts, **2 forgeries accepted** (`True ↔` the Gelfand bound and Hiemenz existence): a closure theorem named `Checked` made every program theorem its own helper (hole A, opened by step 2), plus a bound variable threaded through the witness (hole B, the residue of test AZ). Hole A closed (a helper is `<closure>.<one component>` in the closure's module) with a new forged control; both forgeries rejected; bench unchanged.
4. **Red team BA, round 2** (brief committed alone, 88b4a36): 4 attempts, **1 forgery accepted**: a 45-line metaprogram inlines the program's own proof of the Gelfand bound (no theorem constant left; definitions that use theorems copied as own helpers) and threads the reading's proof through it. Without the threading the rule rejects it. Test AZ had recorded hole B as costly for certified statements; it is not: the rule decides by constant names and closed subterms, and neither separates an equivalence of meaning from one of truth values for a statement the program has proved.
5. **Decision (pre-registered):** closures **suspended**. `Claims.lean` turns every `closed by` field of `objections.txt` into a blocking error (the entry stays open); the header of `CLAIMS.md` and `CLAIMS_READER.md` says no closure is accepted at present and why. The registry has no entry, so no page entry changes. `closureFaults` and its 16 controls stay as the rule under repair.

## Measure
- False rejections of honest closures of real headlines: 6/6 → 0/6 in the accepted style (one more bench case rejected by design).
- Forged closures accepted by the rule: round 1, 2/8 (both closed by the hole-A fix); round 2, 1/4 (not closable by names: route suspended). Forged closures the page can show as closed: 0 (suspension).
- Controls of the closure rule: 8 → 16 (each new valid one rejected by the old rule, the new name control accepted by the first fix).
- Trust map unchanged (no Lean module added; necessity 786 / 261 / 27 open; 314 headlines).

## Next
- CI read first: the run of this run's final push (Claims.lean, objections header, the two pages). Green on every job → nothing to promote. Red → its first failing command with the newest ancestor green on every job (3a7afbb) as base.
- Part 3 next: the parametric closure (`t5/RESULTS_BENCH.md` section 3): the closure states `∀ c, R c ↔ H[c]` with every certified literal of the headline a variable and `H[c₀]` the headline at its printed values (checked by the generator), so proving both sides would need the headline at every value. Restate the six bench bridges parametrically (false rejections), rerun both red-team forgeries and a fresh red team against it; re-enable closures only if no forgery passes. Then the fifth round on `headlines.txt` and the multi-token reader constants (section Next of `runs/2026-11-25T1428Z/README.md`).
- Part 1 next: as in section Next of `runs/2026-11-26T0028Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-25T2228Z/README.md`.

## End
- Local: `scripts/start_run.sh`, judge's build of 3a7afbb restored by streaming, `lake build Checked` (3815 jobs), the bench and the controls against three versions of the rule, `Claims.lean` three times (314 claims; header changed twice), the round-1 and round-2 forgeries rerun by this run against the final rule, `check_claims_fresh.py`, `check_headline_mentions.py --base 3a7afbb`, goal guard, `validation/make_packet.py`, `records_check.py 3a7afbb`.
- Message to Alexander (L.2): the closure route was forgeable and is suspended (seriously wrong: a page-level trust lever).
