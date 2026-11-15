# Run 2026-11-15T0428Z (scheduled)

**THE RESULT:** part 3 (measured trust) — blind round AR against the verified-findings layer: 6/6 valid wrong findings accepted by every check before, 6/6 caught after; the page is now also checked as GitHub renders it (FB23, cmark-gfm), written blind to the round and catching both GitHub-only defects.

**What can a scientist now trust without checking it themselves, that they could not before?** That the verified findings they read on GitHub show exactly what the checks read: FINDINGS.md is now rendered with GitHub's own renderer (cmark-gfm) and compared line by line with the renderer the other checks use, so no footnote, math, autolink, strikethrough or raw HTML can make a note look like a generated Correct or Printed line or add a second "verified" section; no invisible combining mark can hide the marks of generated text; and no candidates line can attach a claim to a verified finding or its records.

**Measure:** blind false acceptance on the findings layer, round AR: 6/6 before (none through the known forged route), 6/6 caught after (2 of them by a rule written blind to the round). check_findings controls 106 → 121.

**Weakest unchecked step:** GitHub post-processing beyond cmark-gfm (math, emoji) is handled lexically, and FB23 compares blocks only in the verified section; the forged blind route remains the documented residue. For the physics: the `bonnor_ebert_extrema` promotion is not yet judged by CI (checked job from 05:31Z).

## Start
- 04:28Z. add_repo not exposed; pre-cloned checkout detached at a13c792 (= origin/main) with a stale local `main`; `git fetch --unshallow origin && git checkout -B main origin/main`. No LOCK → taken (b893c47).
- Local Lean: elan (authorized), `lake exe cache get`, `checked-build` of 43643096701 (80cabb8) restored; `lake build Checked` to main (≈ 10 min: the promoted modules and dependents); StatementDeps (≈ 10 min, exit 0: 291 headlines, NV 174/174) and Claims (291) — generated files unchanged.
- CI at start: 43674121946 (4e046bb, the promotion): Python jobs and work green; nanoda 0, 1 green by 05:37Z; checked job started 05:31Z. Not readable this run.

## Bottleneck (and what a yes/no changes)
- Rotation: part 3 had three runs without progress (2228Z, 0028Z, 0228Z). The LEDGER experiment of run 2026-11-14T2028Z predicted that after the whole-page whitelist only GitHub-only rendering and the forged route remain. Yes (the blind round finds only those) → the findings layer is closed up to GitHub rendering, which a check with GitHub's renderer closes; no → name the new shapes and close them.

## What we did
1. Brief AR (519e00c, a copy of AQ's naming GitHub's renderer and the grandfathered candidates lines), snapshot = that commit with this run's `.lake` outputs; clean snapshot green under `judge_ar.sh`.
2. In ONE message: the blind red team (Sonnet) and a fork integrating FB23 — the cmark-gfm comparison whose prototype was written and tested (0 problems on FINDINGS.md, 7 GitHub-only controls caught) before the round's output existed.
3. Red-team output committed verbatim (aca9b41), then judged. BEFORE (blind): 6/6 ACCEPTED (`t5/before_ar.txt`).
4. Repairs after reading: FB21 no HTML but comments in the whole file (d05); FB20 no combining mark (d06); FB22 no new candidates line mentioning a verified finding, `F<k>` followed by a non-digit (d01, d02). 15 controls in all (121).
5. AFTER: 6/6 CAUGHT (`t5/after_ar.txt`), each by its rule (`t5/RESULTS.md`); clean tree green; `records_check.py 80cabb89` 41/41; goal guard ok.

## Notes
- Commit 9111d24 only rewrites the LOCK heartbeat line; it carries the brief commit's message by a shell slip (a failed command in an `&&` chain skipped writing the new message file). PROMPT note added.

## Next
- STATE 0z: CI read (4e046bb → `bonnor_ebert_extrema` PROVED when green on every job; this run's push needs cmarkgfm in CI's pip steps); then part 1 by rotation.

## CI read
- 43683607031 (145dfbd, this run's final push): goal guard green at 06:02Z, including the render step with FB21–FB23 (cmarkgfm 2024.11.20 installed by the pinned pip step); packet and changes green; the Lean jobs are queued behind 43674121946 (4e046bb), whose checked job started 05:31Z. Both read next run (STATE 0z).
