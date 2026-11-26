# Run 2026-11-26T0028Z

**THE RESULT:** part 1 by rotation (STATE 3l; next step STATE 3m). The Lean theorems of this run and their statements are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For the two decay statements of the boundary-layer equation with a pressure gradient against the flow, what the sign condition on the gradient costs, by kernel theorems (section What we did; `TRUST_MAP.md`): it is not needed, so each conclusion holds for zero and positive gradients too.

**Weakest unchecked step:** the three other hypotheses of the statement on the largest wall shear (the wall data of both solutions and the sign of the shear of the second), still open in `TRUST_MAP.md` (section Next).

## Start
- 00:28Z. Local `main` was the stale clone 860fd46 (its commits are ancestors of origin/main); set to origin/main 65a3c6a, then `scripts/start_run.sh`; no LOCK (taken ee42627, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache; judge's build of 91ca6ba (artifact of 45720073336) restored by streaming; `lake build Checked` replayed it (3814 jobs). No subagents.
- CI read first: 45720073336 (91ca6ba, run 2228Z's final push) green on every job (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4) → `bonnor_ebert_turning_bounds` judged PROVED (STATE heading, judged template).

## What we did

1. **Plan check.** Section Next of `runs/2026-11-25T1828Z/README.md` planned hypothesis 1 (`β < 0`) of `fs_neg_decay_equal` as REDUNDANT from a scan of the conclusion itself for β in [0, 5] (one solution per β in the class), and named the Crocco comparison as the route. Reading the library first: the comparison already exists generic in the coefficient, `Checked.FalknerSkan.MonotoneExists.not_lt_wall` (every k ≥ 0, used so far only at k = 1, 2, 5, 10), so no new comparison proof was needed.
2. **Proof** (`Checked/Trust/NecessityBZ.lean`, compiled first time, about twenty minutes from reading to compiled theorems):
   - `pos_wall_eq` (β > 0): the similarity scaling `Checked.FalknerSkan.FSScale.scale` with c = √β turns both solutions into solutions of the coefficient-1/β problem q' = −(1/β) f q − 1 + p²; `not_lt_wall` in both directions gives equal scaled wall shears, hence q(0) = q₂(0).
   - `blasius_wall_eq` (β = 0): the amplitude scaling η ↦ (μ f(μη), μ² p(μη), μ³ q(μη)) maps a Blasius solution to a solution (`blasius_scale`); with μ³ = q₂(0)/q(0) the scaled first solution and the second have the same data at 0, so they are equal (`Checked.FalknerSkan.NegCore.eq_of_startb`), the limits of the velocity give μ² = 1, so μ = 1 and q(0) = q₂(0).
   - `nonneg_wall_eq` (β ≥ 0) combines the two; `fs_neg_decay_equal_r1` and `fs_neg_decay_max_shear_r1` split on the sign of β (the headline for β < 0, equal wall shears and forward uniqueness otherwise). Neither uses the decay hypothesis for β ≥ 0. Axioms of both: propext, Classical.choice, Quot.sound.

3. **Records the classification made stale:** `check_stale_necessity.py` flagged five STATE.md lines after the relock. Two were false readings of formulas (`p → 1` read as hypothesis 1): `MATH_BEFORE` now counts `→` and `√` as formula characters, with one selftest control that fails under the old pattern. One line listed hypothesis 1 of the maximal-wall-shear statement as open and one had a bare count read as a hypothesis: both moved verbatim to `_archive/STATE_lines_2026-11-26.md`; a third bare count reworded.

## Measure

- Trust map (StatementDeps relock): REDUNDANT 259 → 261, open 29 → 27, headlines with every hypothesis classified 161 → 162 of 187 (`fs_neg_decay_equal`); NV 192/192.
- The plan's scan (run 1828Z, `runs/2026-11-25T1828Z/scripts/scan_fs_beta.out`) and the proof agree: REDUNDANT. This is the first check of the LEDGER experiment of run 1828Z (scan the exact conclusion on the dropped region before planning a redundancy proof): the plan cited such a scan and the classification agrees.
- Pipeline cost: about twenty minutes from reading the plan to compiled theorems, because the comparison was already generic in the coefficient.

## Next
- CI read first: the run of this run's final push (new Checked module `NecessityBZ`). Green on every job → nothing to promote (necessity theorems only). Red → `python3 scripts/trust/records_check.py <base>` with the newest ancestor green on every job (91ca6ba, read green in this run).
- Part 1 next: hypotheses 6 (p(0) = 0), 13 (f₂(0) = 0) and 16 (q₂ > 0) of `fs_neg_decay_max_shear`. Hypothesis 16, scanned in this run (`runs/2026-11-26T0028Z/scripts/scan_max_shear_h16.py` and `scan_max_shear_h16_tail.py`, outputs `.out` beside them): at β = −0.05, −0.1, −0.15, −0.19 every shooting value above the one of the solution in the class (up to 5) overshoots (velocity above one at η = 12, second derivative negative there), and the long integration at β = −0.1 (s = 0.35, 0.5, 1, to η = 10⁴) shows the velocity returning to one from above algebraically, (p − 1) η^{1/5} ≈ constant: these are second solutions of the boundary-value problem with a larger wall shear and a second derivative that changes sign, so the scan points to NEEDED (the class condition q₂ > 0 is what excludes the algebraic solutions; the first solution's decay condition does not constrain the second). A witness needs one such solution certified: cells from 0 to some η₀ (the existing reversed-flow and β = −1/10 certificates) and an analytic tail on [η₀, ∞) in the region p > 1, q < 0, where p decreases and its limit must be one (plan the tail first: the limit L ≥ 1 of p, and L > 1 is impossible: then f grows like Lη and q' = −f q − β(1 − p²) keeps q near β(L² − 1)/(Lη), whose integral diverges). Hypotheses 6 and 13 change the wall data; scan them the same way before choosing between a witness and a redundancy plan. Before planning a new comparison or uniqueness proof, search the library for the same lemma generic in its coefficient (PROMPT working note of this run).
- Part 3 next: as in section Next of `runs/2026-11-25T2028Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-25T2228Z/README.md`.

## End
- Local: `scripts/start_run.sh`, judge's build of 91ca6ba restored by streaming, `lake build Checked` (3815 jobs with the new module), `lake env lean` of an axiom print (axioms of both theorems: propext, Classical.choice, Quot.sound), `TRUST_RELOCK=1 … StatementDeps.lean` (314 headlines, NV 192/192, necessity 786 / 261 / 27 open), `Claims.lean` (314 claims), `check_claims_fresh.py`, `check_headline_mentions.py --base 91ca6ba`, `check_stale_necessity.py`, goal guard, `validation/make_packet.py`, `records_check.py 91ca6ba` (after the commit).
- CI read in this run: 45720073336 (91ca6ba) green on every job → `bonnor_ebert_turning_bounds` judged PROVED.
- Message to Alexander (L.2): `bonnor_ebert_turning_bounds` PROVED (judged by CI on every job).
- CI of this run's final push 3a7afbb: 45734700171 (started 01:17Z); the next run reads it (section Next).
