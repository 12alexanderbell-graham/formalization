# Run 2026-11-15T1028Z (scheduled)

**THE RESULT:** part 3 (measured trust) — blind round AS against the verified-findings layer: 6/6 valid wrong findings accepted by every check before, all in the candidates section's free prose; after, 4/6 caught (3 by FB24, written blind to the round) and the other 2 stand under a fixed label that marks the whole candidates section as unchecked (FB25).

**What can a scientist now trust without checking it themselves, that they could not before?** That what GitHub displays on the findings page is what the checks read: no entity, escape, HTML comment or inline markup can make a candidates line show a verified finding's id, a certified tag or a generated-text mark that its source does not spell; GitHub-only features (math, emoji, diagrams, alerts) cannot appear anywhere on the page; and the candidates section, the one free region after the verified findings, now says in fixed words that nothing in it is checked, and cannot link to a verified finding.

**Measure:** blind false acceptance on the findings layer, round AS: 6/6 before (none through the forged route, none of the shapes the 0428Z experiment predicted); after: 4/6 caught, 2/6 accepted but labelled. check_findings controls 121 → 150.

**Weakest unchecked step:** a false sentence about a verified finding in the candidates section (d02, d05) is still accepted by every check; it now stands under the FB25 banner. For the physics: `bonnor_ebert_extrema_monotone` is not yet judged by CI (43701382621 pending behind 813805f).

## Start
- 10:28Z. add_repo not exposed; pre-cloned checkout detached at ece084b (= origin/main) with a stale local `main`; `git reset --hard origin/main`, `git fetch --unshallow origin`. No LOCK → taken (1b490b7).
- Local Lean: elan (authorized), `lake exe cache get`, `checked-build` of 43674121946 (4e046bb) restored; `lake build Checked` to main ≈ 6 min; StatementDeps (exit 0: 292 headlines, NV 175/175, needed 636, redundant 163, open 196) ≈ 8 min and Claims ≈ 2 min — generated files unchanged.
- CI at start: 43691560009 (813805f) checked job in its Lean step, nanoda shard 2 running; 43701382621 (ece084b) pending. Not readable to a conclusion this run.

## Bottleneck (and what a yes/no changes)
- Rotation: part 3 (parts 2/5 at 0828Z, part 1 at 0628Z, part 3 last at 0428Z). The LEDGER experiment of run 0428Z predicted that only GitHub post-processing beyond cmark-gfm, renderer differentials outside the verified section, or the forged route remain. Yes → the findings layer is closed up to those, each closable by one rule; no → name the new shape and close it structurally.

## What we did
1. Brief AS (c78c59d, a copy of AR's naming the predicted residues), snapshot = that commit with this run's `.lake` outputs; clean snapshot green under `judge_as.sh`.
2. In ONE message: the blind red team (Sonnet, ≈ 19 min) and a fork writing FB24 blind to it (mark and mention rules on GitHub's displayed text; GitHub-only post-processing; candidates block comparison; 19 controls).
3. Red-team output committed verbatim (b41e428), then judged. BEFORE (blind): 6/6 ACCEPTED (`t5/before_as.txt`). The experiment is refuted: every defect was candidates-section prose about a verified finding.
4. FB24 caught d01, d03, d04 (an entity or comment spelling the id). For d02, d05, d06 (no id at all) FB25: a fixed banner under the candidates heading labels the section as unchecked prose that says nothing checked about any verified finding, and the section may not render a link (d06). 10 controls (150).
5. AFTER: 4/6 CAUGHT, d02 and d05 ACCEPTED under the banner (`t5/after_as.txt`, `t5/RESULTS.md`); clean tree green under every check.

## Next
- STATE 1c: CI read (ece084b → `bonnor_ebert_extrema_monotone` PROVED when green on every job; this run's push); then parts 2/5 by rotation.
