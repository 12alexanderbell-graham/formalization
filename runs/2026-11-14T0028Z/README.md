# Run 2026-11-14T0028Z (scheduled)

**THE RESULT:** part 3 by rotation (part 3 last moved at 1828Z, part 1 at 2028Z, parts 2/5 at 2228Z) — the last author line at the top of a verified finding, its heading, is now generated (records and the binding of each printed value; FB13), and a blind red team aimed at the new layout found five ways around it, all through the frame around the generated text rather than the text itself; the frame is now fixed and fails closed (FB14, FB15).

**What can a scientist now trust without checking it themselves, that they could not before?** Everything a verified finding shows above its unchecked notes — heading included — is generated from Lean records and blind readings, and the file around it can no longer hide, duplicate or imitate that part: a reader no longer needs to check which records a finding rests on, or whether a printed value was read blind, against the Lean files.

**Weakest unchecked step:** the repairs were measured against the defects that motivated them (not blind); three printed formulas (F3's `printedD4`, F9's P₀/Q₀ family, F10's `printedDen`, `qL`) still have blind readings older than the blind route, so the generated heading says no reader described their source; F4–F7 have no record.

## Start
- 00:29Z. add_repo not exposed; pre-cloned checkout detached at 8e3a22d with a stale local main; `git reset --hard origin/main` = 8e3a22d. No LOCK → taken (9241ebc).
- CI at start: 43511962008 (3cd85d2) checked job building since 21:59Z (all other jobs green); 43528111166 (8e3a22d) pending behind it.
- Local Lean: elan + Mathlib cache ≈ 3 min; `checked-build` artifact of 43462297471 (c5c2a35) restored (unzipped in place, zip deleted, decompressed by Python zstandard in 19 s); incremental `lake build Checked` green (≈ 35 min with a red team and judges sharing two cores); StatementDeps exit 0, tree clean (TRUST_MAP unchanged).

## CI read
- **43511962008 (3cd85d2): green on every job** (checked job finished 01:15Z; nanoda 4/4). So rows β = −0.13 … −0.16 of Ganapol 2010 Table 6 (`fs_neg_wall_shear_13_window` … `_16_window` and `_exists_decay` companions) are PROVED; FB10–FB12 live; NecessityY's 18 classifications in CI's TRUST_MAP.
- 43528111166 (8e3a22d, `bonnor_ebert_max`): checked job started 01:15Z, still building at the end of this run.

## Bottleneck (and what a yes/no changes)
- STATE 0i(a): after round AM the two accepted defects sat in the heading, the only author line at top level. Yes (heading generated, a blind round finds nothing): the findings layer's trusted part is closed against the shapes tried so far. No: record what gets through and repair it.

## What we did
1. `check_findings.py` FB13: heading `### F<k> — generated heading (do not edit): records …; printed values … (read blind; its source as the reader described it / no reader file describes its source / unread)`, or a fixed no-record heading; author titles moved unchanged (with their "was" label) to the first note `*(author)* **Title** (was …): …`; `validation/make_packet.py` reads the source from there (packet byte-identical). Selftest 45 → 50.
2. Blind red team AN (Sonnet; brief `t5/briefAN.md` committed in the snapshot 9d8d3c9 before the round; snapshot as a standalone clone, read-only; output `t5/redteamAN/` committed verbatim (04043b4) before judging; ≈ 37 min).
3. Judge `t5/judge_an.sh` BEFORE (snapshot 9d8d3c9, author-files jsonl of c5c2a35) and AFTER (136a38f, this run's fresh StatementDeps jsonl).
4. Repairs (not blind): FB14 — fixed frame of FINDINGS.md (`# FINDINGS`, exactly the three level-2 headings in order, level-3 only generated finding headings and `### C-…`), scopes located by whole-line match; generators read records only inside generated blocks; an unchecked note cannot be a heading, setext underline, HTML, quote or generated-block line, and no line outside the generated part carries the marks of generated text. FB15 — a class phrase added to the registry since BASE has no quantifier word and no symbol its atom lacks. Selftest 62 controls.

## Round AN
See `t5/RESULTS.md`.
