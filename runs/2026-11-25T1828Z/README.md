# Run 2026-11-25T1828Z

**THE RESULT:** part 1 by rotation (STATE 3i; next step STATE 3j). The Lean theorems of this run and their statements are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For the two curved statements of the quartic fits of the B1 family, what the lower density bound costs, by kernel theorems (section What we did; `TRUST_MAP.md`): without it each conclusion is false, for a closed model in the allowed curvature range, so every hypothesis of both statements is now classified.

**Weakest unchecked step:** the B1 statements are about two redshifts and central fits, not about a fit to data with errors; and the plan a part-1 run writes for the next run is checked by nothing until that run (section Measure).

## Start
- 18:28Z. `scripts/start_run.sh`: local main = origin/main dfa4666; no LOCK (taken 178eabc, 48.4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean v4.35.0 (elan), Mathlib cache present. Judge's build of 1c11b90 (artifact of 45668257029) restored by streaming; `lake build Checked` up to date before the new modules. No subagents.

## CI read
- 45668257029 (1c11b90, run 1628Z's final push): green on every job (goal guard, packet, changes, work, checked incl. the trust and frozen steps, leanchecker 4/4, nanoda 4/4) → the promotion of run 1628Z judged PROVED: the judged template in its STATE.md heading.

## Bottleneck (and what a yes/no changes)
- The curved pair `l19_sq_curved`, `l19_sqg_curved` had one open hypothesis each, 1 (matter density at least one tenth). Run 1228Z planned a three-region redundancy proof. Yes (REDUNDANT) → each statement covers every density the closed or flat law admits. No → a witness model below one tenth with the conclusion false.

## What we did
- **First, the conclusion itself on the dropped region** (`runs/2026-11-25T1828Z/scripts/scan_sine.py`, output `scan_sine.out` beside it, about a minute): run 1228Z's scan compared the two distance integrals and left out the closed transverse factor, a sine of the comoving distance over √10 (curvature term −1/10). Just above the density at which the radicand y(v) = m + k v² + (1 − m − k) v⁶ first vanishes at the farther source, that distance grows to about ten, past a right angle times √10, so the sine falls back towards zero and the residual difference goes below −1 (curvature terms −3/40 and below). The planned redundancy proof could not have closed.
- **Hypothesis 1 NEEDED in both statements** (`Checked/Trust/NecessityBX.lean`, `l19_sq_curved_h1`, `l19_sqg_curved_h1`): the closed model of matter density 121/10000 and total density 11/10 (curvature constant 1/10 with H₀ = a₀ = 1), with the scale factor of `Checked.Trust.NCAS.ma`, satisfies every other hypothesis; its residual at 1 + z = 4√2 does not exceed the one at 2√2, against 1/4 and 3/20 in the conclusions.
  - **Integrals** (`Checked/Trust/NecessityBXTools.lean`, generated `Checked/Trust/NecessityBXCerts.lean`, `runs/2026-11-25T1828Z/scripts/gen_bx.py`): the radicand increases on [21/50, 1] (`bx_mono`: one factorisation), so the integrand decreases and step sums bound each integral from either side: 8.067 ≤ J₅ ≤ 9.641 (63 and 56 cells, geometric near the farther source, where y is 4.3e-4) and 2.001 ≤ J₃ ≤ 2.683 (32 and 4 cells). Compiled first time with `maxHeartbeats` raised for the long lists (about a minute).
  - **Sines:** J₅/√10 lies in (2.55, 3.05), so 0 < sin(J₅/√10) ≤ π − J₅/√10 < 0.591; J₃/√10 lies in (0.63, 0.85), so sin(J₃/√10) > 0.556 (cubic bound). With Q₃ ≤ 0.42 Q₅ (`NCAS.q_sq`, `q_sqg`) that gives the luminosity distance ratio at most the quartic ratio (`bx_final`).
- **The promotion of run 1628Z judged PROVED** (CI read above; STATE heading).
- **Annex LIV:** PROMPT working note and LEDGER experiment: a planned redundancy proof must first compute the exact conclusion on the dropped region, near each boundary (this plan and run 2026-11-21T0628Z's both rested on proxies the conclusion contradicts).
- Axioms of the two theorems: propext, Classical.choice, Quot.sound.

## Measure
- `l19_sq_curved`, `l19_sqg_curved`: open 1 → 0 each (needed 8 → 9 each); every hypothesis of both classified.
- Trust map (`TRUST_MAP.md`): NEEDED 781 → 783, REDUNDANT 258, open 31 → 29; headlines with every hypothesis classified 158 → 160 of 186; non-vacuity 191/191; headlines 313.
- Cost: scan to compiled witness about twenty minutes (the witness module and the generated step sums each compiled on the first or second try); the planned three-region redundancy proof it replaces had no route.
- Plans: of the last two part-1 plans for a REDUNDANT classification that rested on a proxy scan, two were contradicted by the exact conclusion (0628Z of 11-21, 1228Z of 11-25); the experiment in LEDGER measures the next one.

## Next
- CI read first: the run of this run's final push (new Checked modules `NecessityBXTools`, `NecessityBXCerts`, `NecessityBX`). Green on every job → nothing to promote (necessity theorems only). Red → `python3 scripts/trust/records_check.py <base>` with the newest ancestor green on every job (1c11b90, read green in this run).
- Part 1 next: hypothesis 1 (β < 0) of `fs_neg_decay_equal`, its only open one. First the conclusion itself for β ≥ 0: with q > 0, p(0) = 0 and p → 1 the profile has 0 ≤ p < 1, the class of the bounded-class uniqueness theorems of runs 2026-11-08/09 for β ≥ 0 (`Checked/FalknerSkan/`); if those cover every β ≥ 0 under these hypotheses the hypothesis is REDUNDANT by a case split, else name the β where they stop and scan there.
- Part 3 next: as in section Next of `runs/2026-11-25T1428Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-25T1628Z/README.md`.

## End
- Local: `scripts/start_run.sh`, judge's build of 1c11b90 restored by streaming, `lake env lean` of each new module during the work (the generated step sums about fifty seconds), `lake build Checked` (3809 jobs), axioms of the two theorems (propext, Classical.choice, Quot.sound), `precheck_names.py`, `TRUST_RELOCK=1 … StatementDeps.lean` (313 headlines, NV 191/191, necessity 783 / 258 / 29 open), `check_prose.py`, `precheck_citations.py`, `check_status_lines.py`, `check_stale_necessity.py`, `check_literals.py`, `check_literal_targets.py`, `check_formulas.py --base`, `check_necessity.py --base 1c11b90`, `check_headline_mentions.py --base 1c11b90` (one finding on a BLUEPRINT heading, reworded), `Claims.lean` (313 claims), `check_claims_fresh.py`, `check_claim_vocab.py`, `validation/make_packet.py` (unchanged), `records_check.py 1c11b90` (after the commit).
- CI read in this run: 45668257029 (1c11b90) green on every job → `bonnor_ebert_turning_ratio` judged PROVED.
- Message to Alexander (L.2): one line, the promotion of run 1628Z judged PROVED, with this run's classification.
- CI of this run's final push d198472: 45683665296 (queued 19:17Z); the next run reads it (section Next).
