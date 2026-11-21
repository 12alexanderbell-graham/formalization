# Run 2026-11-21T0828Z

**THE RESULT:** part 3 by rotation (STATE 2u; next step STATE 2v), then part 1 (the step run 0628Z prepared). The Lean theorems of this run and their statements are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** For one statement of the B1 family (the three-source fit of the third-order polynomial of Risaliti & Lusso 2019 against exact flat ΛCDM), what four of its hypotheses cost: for each a kernel theorem shows the statement with that hypothesis removed (section What we did; `TRUST_MAP.md`). And a hand-written line that calls a hypothesis open by describing it in words, without its number, now fails CI, so such a line can no longer contradict the generated trust map unnoticed.

**Weakest unchecked step:** the remaining open hypotheses of the B1 family (`TRUST_MAP.md`, per headline); for the records, a classification stated by content ('the decay hypotheses of `x` NEEDED') is still read by no rule.

## Start
- 08:28Z. Session clone on the stale divergent main (fa47717), shallow; reset to origin/main db96093 (`git checkout -B main origin/main`), then `scripts/start_run.sh` (elan, toolchain v4.35.0, Mathlib cache). No LOCK → taken (325dfd4).
- Env: repo ok (add_repo not exposed; the session clone was present). Local Lean; judge build of 44879898559 (4fed7f6) restored by streaming; `lake build Checked` 3765 jobs replayed. Subagents: two held-out Sonnet writers (SN6, SN7).
- CI at start: 44879898559 (4fed7f6, run 0628Z's final push) green on every job (13/13: checked, leanchecker 4/4, nanoda 4/4). Nothing to promote.

## Bottleneck (and what a yes/no changes)
- Part 3 (section Next of run 0228Z): the stale-hypothesis check reads numbers only; how often do real records describe a hypothesis by content, and can a rule catch the stale ones? Yes → the last known way for a hand-written line to call a classified hypothesis open is closed. No → the limit is measured and stated.
- Part 1 (section Next of run 0628Z): hypotheses 13–16 of `fit_direction`, predicted redundant by that run's degenerate-data scan. Yes → four fewer open hypotheses with no certified integral.

## What we did
- **Measured** (`scripts/measure_content_mentions.py`): 74 candidate mentions in STATE.md, README.md, BLUEPRINT.md and the last twelve run records; 13 lines describe a hypothesis of a headline with open hypotheses by content; 4 of them called classified hypotheses open (STATE: 'Still open in B1: … time orderings, positivity of the scale factor, and the coefficient/residual conditions of `fit_direction`', of which 3–6 and 17–19 were classified; 'Open there: … the decay class' of the separation pair; two old next-step items).
- **Rule S-N6** of `scripts/trust/check_stale_necessity.py`: in an open scope (open or plan word, or a scope label), a clause that describes a hypothesis of a headline with a necessity entry and attaches no number to it is flagged; the generic 'the open hypotheses of `x`' is exempt. The default is inverted as in S-N4: no attempt to match a description against TRUST_MAP; the line must carry numbers.
  - Frozen 699ff0a before held-out writer SN6 (brief ae220fc, alone; Sonnet; told the hypothesis texts): blind recall 6/16, honest lines flagged 0/8 (main before: 2/16). The writer described hypotheses by formulas in code spans and by necessity words alone.
  - S-N6b (written after SN6, NOT blind): any necessity cue or formula span counts as a description; frozen a6f3a45 before writer SN7 (brief e52fc90, alone; four other headlines): **blind recall 16/16**, honest lines flagged 2/8 (one true open item without its number, which the rule asks to number by design; one generic 'the open hypotheses of `x` still need triage').
  - After SN7 (not blind): a generic list is exempt; 'needs' is no longer a plan word (it states NEEDED). Controls 47 → 66. Cost: STATE lines 39, 60, 62 (trust-track entries of runs 2026-11-18T0628Z, 2026-11-12T1628Z, 2026-11-12T0227Z) moved verbatim to `_archive/STATE_lines_2026-11-21.md` with one pointer line left; next-step items 2f–1h moved verbatim to `_archive/STATE_steps_2026-11-18_to_2026-11-20.md`. On the last twelve run records (dated, not read by CI) S-N6 flags 6 lines.
- **`fit_direction` hypotheses 13, 14, 15, 16 REDUNDANT** (`Checked/Trust/NecessityBL.lean`; axioms propext, Classical.choice, Quot.sound), with no certified integral:
  - `bl_rel`: the cubic's values P₁, P₃, P₅ at u = ℓ/2, 3ℓ/2, 5ℓ/2 (ℓ = ln 2) satisfy 30P₁ − (20/3)P₃ + (6/5)P₅ = 8ℓ (third divided difference of the quadratic factor).
  - Ratios of the distance integrals for 0 ≤ Ω ≤ 1: the integrand over the empty model's 2/v³ increases in v (`bl_cmp`, `bl_cmp'`, `bl_upper`, `bl_lower`), so J₅/J₃ ≤ (4√2 − 1)/(2√2 − 1) (`bl_ratio53`); the integrand decreases (`gL_anti`), so J₁/J₃ ≤ (1 − w₁)/(1 − w₃) and J₁/J₅ ≤ (1 − w₁)/(1 − w₅) (`bl_ratio13`, `bl_ratio15`); κ(15J₁ + (12/5)J₅) ≥ (20/3)J₃ (`bl_comb`: both bounds of the middle piece, split on the integrand at w₃ against 5.6 times the empty-model ratio at w₁).
  - 14 (nearest value): P₁ ≤ 0 makes P₅ > (50/9)P₃ by the relation; the residuals at the middle and farthest sources allow at most 2·2.547/κ ≈ 5.33.
  - 16 (farthest value): P₅ ≤ 0 makes P₁ > (2/9)P₃; the residuals allow at most σ/(2κ) ≈ 0.206 (σ ≈ 0.393).
  - 13 (0 < H): H = 0 makes the polynomial distance zero; H < 0 makes all three values negative, and the relation then contradicts `bl_comb` and the two residual ratios to the middle source.
  - 15 (middle value): P₃ ≤ 0 with P₁, P₅ > 0 makes the quadratic factor convex; the residuals at the outer sources give P₅ ≥ 13.9 P₁, hence curvature y ≥ 0.16, and the rescaled conclusion 20/3 e₃ − e₂ ≥ 2.2 where 0.1044 is needed (the ΛCDM constant of the line is at most its value at Ω = 0, 1.8696).
- Local: `lake build Checked` (3766 jobs), `#print axioms` of the four theorems.

## Measure
- Records: blind recall of content descriptions by the frozen rule 6/16 (SN6) → 16/16 (SN7, S-N6b); main before S-N6: 2/16.
- Necessity (TRUST_MAP after this run's relock): REDUNDANT 233 → 237, open 46 → 42; `fit_direction` open 1, 13, 14, 15, 16 → 1.
- Experiments evaluated: run 0628Z 'degenerate data first' — met (the degenerate-data scan of run 0628Z predicted each of the four, and the Lean followed it: no needed one among them, the middle-source case with a large margin); run 0228Z 'a fourth held-out writer told the hypothesis texts' — met in part: by number no false positive (two honest numbered lines in SN6, none flagged); the content arm measured the limit (2/16 on main), which S-N6 closes.

## Next
- CI read first: the run of this run's final push (new Trust module `NecessityBL`, ≈ 20 s locally; nanoda and leanchecker replay it; the check change is in `check_stale_necessity.py`, run by the trust step). Green on every job → nothing to promote. Red in the trust step → `python3 scripts/trust/check_stale_necessity.py`.
- Part 1 next: hypothesis 1 (0 ≤ Ω) of `fit_direction`: below about −1/180 no model reaches the farthest source (`bi_unreach`); on [−1/180, 0) the conclusion has margin about 24 at Ω = 0 (scan of run 0628Z), so the empty-model comparisons `bi_lower`, `bi_upper` should bound J₁, J₃, J₅ within a few percent of their Ω = 0 values (z₁, z₃, z₅) and a perturbed `core` close it; then the curved pair `l19_sq_curved`, `l19_sqg_curved` (1, 8) and `rl19_box_unmatched` (`TRUST_MAP.md`). The relation `bl_rel` and the ratio lemmas of `NecessityBL` apply to `rl19_box_unmatched` too.
- Part 3 next: a classification stated by content ('the decay hypotheses of `x` NEEDED') is read by no rule; measure first how many such lines the records hold and how many disagree with TRUST_MAP (this run's count: 5 lines, all agreeing).
- Parts 2/5 next: as in section Next of `runs/2026-11-21T0428Z/README.md`.

## End
- Local: `lake build Checked` (3766 jobs; restored build of 4fed7f6), `#print axioms` of the four theorems, `precheck_names.py`, `TRUST_RELOCK=1 … StatementDeps.lean` (307 headlines, NV 186/186; necessity 756 / 237 / 42 open), open baseline shrunk (`fit_direction` 1), `Claims.lean` (307), `check_prose.py`, `check_claim_vocab.py`, `check_headline_mentions.py --base db96093` (front-page lines name no headline; three STATE trust-track lines archived, see What we did), `check_stale_necessity.py` (0 findings), `validation/make_packet.py` (item 18 regenerated), `records_check.py db96093` (43 commands, 0 failed). Records: STATE 2v + daily review + Trust track line, LEDGER, CHANGELOG, BLUEPRINT, PROMPT working note; LOCK removed.
