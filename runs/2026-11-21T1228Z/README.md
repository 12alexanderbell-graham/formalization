# Run 2026-11-21T1228Z

**THE RESULT:** part 1 by rotation (STATE 2w; next step STATE 2x). The Lean theorems of this run and their statements are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For the three-source fit statement of the B1 family (the third-order polynomial of Risaliti & Lusso 2019 against exact flat ΛCDM) and for its box corollary, what five more of their hypotheses cost, each by a kernel theorem (section What we did; `TRUST_MAP.md`): every hypothesis of the fit statement is now classified.

**Weakest unchecked step:** the hypotheses `TRUST_MAP.md` still lists as open, per headline (four of them in the box corollary, section Next).

## Start
- 12:29Z. Session clone shallow on the stale divergent main (fa47717); `git checkout -B main origin/main` (05678fd), then `scripts/start_run.sh`. No LOCK → taken (090f2f4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean (elan, v4.35.0, Mathlib cache); judge build of 44897939675 (308b378) restored by streaming; `lake build Checked` 3774 jobs. No subagents.
- CI at start: 44900695787 (12580d3, run 1028Z's final push) in progress, then green on every job (13/13: checked, leanchecker 4/4, nanoda 4/4) → `gelfand_turning_values_seven` and `gelfand_pde_radial_count_turning_values_five` PROVED; their STATE headings carry the judged template.

## Bottleneck (and what a yes/no changes)
- Part 1 (section Next of run 0828Z): hypothesis 1 (0 ≤ Ω) of `fit_direction`, the last open one. Yes → every hypothesis of the fit statement classified, and the same theorem should carry over to its corollary `rl19_box_unmatched`. No → a negative-density counterexample (a matching cubic on the wrong side of the line).

## What we did
- **`fit_direction` hypothesis 1 (0 ≤ Ω) REDUNDANT** (`Checked/Trust/NecessityBN.lean`, `fit_direction_r1`; axioms propext, Classical.choice, Quot.sound), no certified integral:
  - Ω ≤ −1/180: the radicand Ω(1+z)³ + 1 − Ω is negative at 1 + z = 4√2 ((4√2)³ = 128√2 > 181), so no model reaches the farthest source (`NCBI.bi_unreach`).
  - −1/180 < Ω < 0, nearest source (`bn_near`): bridge `NCBI.bi_bridge`, comparison above the source `NCBI.bi_upper` with factor w³/√(Ω + (1 − Ω)w⁶) ≤ 1.01 (w⁶ = 1/(2√2)), so d₁ ≤ √2 · 0.42 / H₀ (empty model: √2(√2 − 1)/H₀).
  - Farthest source (`bn_far`): a time with a = (2/11) a₀ lies between the middle and farthest sources (IVT); there the radicand is positive (8/1331 + Ω·1323/1331 > 0 for Ω > −1/180), the comparison with the empty model below the present (`NCBI.bi_lower` with comparison point v = 1) gives ∫ ≥ 11/2 − 1, and comoving distance grows with source time, so d₅ ≥ 4√2 · (9/2) / H₀.
  - Conclusion: the residuals at the nearest and farthest sources give 18κP₁ ≤ 0.42P₅ (κ = 0.95499); with P₃ > 0 and the existing `Qb1/Qb3/Qb5` bounds, `linarith` gives 20/3 e₃ − e₂ ≥ 0.1044 (float LP minimum ≈ 3.83: `scripts/lp_fit_direction_neg.py`; the dual uses only r₁₅ and P₃ > 0), then `B1Fit.conclude`.
- **`rl19_box_unmatched` hypothesis 1 REDUNDANT** (`rl19_box_unmatched_r1`): its proof is `fit_direction` plus `box_neg`; `bn_box_neg` is `box_neg` without the density lower bound (the quadratic in Ω is concave with maximum near 49/60; the proof never used 0 ≤ Ω), so `fit_direction_r1` carries over.
- **`rl19_box_unmatched` hypotheses 14 (a₂ ≤ 349/100) and 15 (157/100 ≤ a₃) REDUNDANT** (`rl19_box_unmatched_r14`, `_r15`): the direction functional decreases in a₂ and increases in a₃; `bn_box_neg` needs only a₂ ≥ 343/100 and a₃ ≤ 169/100 (for a₃ < 0, L a₃ ≤ 0).
- **`rl19_box_unmatched` hypothesis 16 (a₃ ≤ 169/100) NEEDED** (`rl19_box_unmatched_h16`): at Ω = 1/5 (`B1FitWitness.exists_model`, enclosures `WL1`…`WU5`), the cubic a₂ = 343/100, a₃ = 117/20, H = 1 matches all three distance moduli within 0.05 mag with offset c = (residual at the middle source) + 5 log₁₀(102/100): the ratios (X₁/X₃)/1.02 and (X₅/X₃)/1.02 lie in [0.978, 1.0225] by the enclosures (exact-rational check `scripts/witness_rl19_h16.py`: worst-case ratio spread 1.0400 against a window of 1.0455), and |5 ln Y/ln 10| ≤ 1/20 there (`bn_log_small`). The proof copies `B1FitWitness.hyps_satisfiable` with the new cubic and offset (`maxHeartbeats` 10⁶ for this one declaration).
- Float scan (unchecked, `scripts/scan_rl19_min_a3.py`): over Ω ∈ [0, 1] (step 0.01) every cubic matching within 0.05 mag has a₃ ≥ 2.64 (minimum at Ω = 1), so hypothesis 13 (a₂ ≥ 343/100) of `rl19_box_unmatched` is predicted REDUNDANT, but a proof needs an Ω-uniform lower bound on a₃ (new certificates in the style of `B1FitCerts`, objective e₃ instead of 20/3 e₃ − e₂).

## Measure
- Necessity (TRUST_MAP after this run's relock): REDUNDANT 238 → 242, NEEDED 759 → 760, open 42 → 37; `fit_direction` open 1 → none (19/19 classified); `rl19_box_unmatched` open 1, 2, 9, 10, 13, 14, 15, 16 → 2, 9, 10, 13.
- Judge: two promotions of run 1028Z PROVED (CI 44900695787).

## Next
- CI read first: the run of this run's final push (new Trust module `NecessityBN`, ≈ 1 min locally; nanoda and leanchecker replay it). Green on every job → nothing to promote. Red in the trust step → `python3 scripts/trust/check_necessity.py` and `check_stale_necessity.py`.
- Part 1 next: `rl19_box_unmatched` 13 (predicted REDUNDANT, min a₃ ≥ 2.64 over the matching set): rerun `runs/2026-11-04T0228Z/scripts/emit_fit.py` with objective e₃ ≥ (169/100/ln²10 − A₃(Ω)) ln³2 per Ω-cell (the cells' integral bounds `L5_k`, `U1_k`, `U3_k` are public lemmas of `B1FitCerts` and may serve unchanged); then 2, 9, 10 (corollary of `fit_direction` 2, 9, 10, which are NEEDED by Einstein–de Sitter witnesses: check whether a witness with a box cubic exists, `NCAR.rl19_box_unmatched_h11` is the template); then the curved pair 1, 8.
- Part 3 next: as in section Next of `runs/2026-11-21T0828Z/README.md`.
- Parts 2/5 next: as in section Next of `runs/2026-11-21T1028Z/README.md`.

## End
- Local: `lake build Checked` (3774 jobs; restored build of 308b378), `#print axioms` of the five theorems (propext, Classical.choice, Quot.sound), `precheck_names.py`, `TRUST_RELOCK=1 … StatementDeps.lean` (309 headlines, NV 187/187; necessity 760 / 242 / 37 open), open baseline shrunk, `check_necessity.py --base 05678fd`, `check_prose.py`, `check_stale_necessity.py` (one stale STATE line archived verbatim to `_archive/STATE_lines_2026-11-21.md`), `check_headline_mentions.py --base 05678fd`, `check_stale_status.py --base 12580d3`, `Claims.lean` (309), `validation/make_packet.py` (item 18 regenerated), `records_check.py 05678fd` (43 commands, 0 failed).
- Message to Alexander (L.2): the two promotions of run 1028Z judged PROVED.
