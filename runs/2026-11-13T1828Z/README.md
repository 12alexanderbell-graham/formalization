# Run 2026-11-13T1828Z (scheduled)

**THE RESULT:** part 3 by rotation (last moved at run 1028Z; parts 1 and 2/5 moved at 1522Z/1640Z) — the part of a verified finding a reader is told to trust is now generated, not written: every one of F1–F14 shows a generated Printed line (its records' PRINTED Lean definitions, the blind reading each agrees with, and the reader's own description of the source), the generated Correct line and its certified blocks; every author sentence stands, unchanged in wording, under a fixed **Unchecked notes** marker, and the heading is labelled as the author's title. CI fails if any of this layout is broken (`check_findings.py` FB10–FB12).

**What can a scientist now trust without checking it themselves, that they could not before?** Which lines of a verified finding are machine-generated and which are author prose — the boundary is now drawn line by line in the file and enforced by CI, instead of a file-level disclaimer — and, for F1, F2, F10 and F12–F14, the source location of each printed value as the blind reader (not the author) described it.

**Weakest unchecked step:** the heading (author's title, now labelled unchecked) still carries the finding's source list and summary, and blind round AM shows a false heading passes (d04, d05); F3's and F9's printed formulas have blind readings older than the blind route, so no reader describes their source; F4–F7 have no record and nothing in them is generated.

## Start
- 18:28Z. add_repo not exposed; pre-cloned checkout detached at cc5a1da with a stale local main (diverged 54/50; kept locally as `old-local-main`, not pushed); `git checkout -B main origin/main` = cc5a1da. No LOCK → taken (a08a839).
- CI at start: 43462297471 (c5c2a35, run 1522Z) checked job building since 16:26Z (nanoda 3/4 green, work green); 43482419250 (7911453, run 1640Z's final push) work and nanoda running, checked job pending behind it.
- Local Lean: not installed this run (no Lean change planned); the `author-files` artifact of 43422957898 (028d5c4) supplied `.lake/*.jsonl`/`*.tsv` for every Python check (`records_check.py`: clean tree fails only goal_guard (stub README) and check_literals (stale meaning.jsonl), as expected).

## Bottleneck (and what a yes/no changes)
- STATE 0f: the lines of a verified finding no rule can generate (Scope, printed attributions, Plain words, Lean-evidence prose) were free; four word-rule rounds (AI, AJ, AK, AL) were each beaten on the day they were run (24 of 24 accepted). Yes (a layout that generates the trusted part and labels the rest, enforced by CI): the false-acceptance question moves from prose to the generated part, where it can converge. No: record what still gets through.

## What we did
1. `scripts/trust/check_findings.py` FB10 (layout), FB11 (generated Printed line), `--write-layout F<k>`; `check_numbers.py` reads a Printed line only if it equals the generator's output character for character. FB11 takes the reader's words from the earliest runs/ reader file that is an ancestor of the Checked reading's first commit, as first committed (a reader file planted later never counts). `FINDINGS.md` F1–F14 rewritten into the layout: no author sentence reworded; hand-written Printed/Correct lines moved into the notes with the prefix *(author)* (LEDGER line naming F1–F14).
2. Blind red team AM (Sonnet; brief `t5/briefAM.md` committed in the snapshot commit ffdcac7 before the round started; snapshot ffdcac7 as a standalone clone; output `t5/redteamAM/` committed verbatim (9dde6b1) before judging; ≈ 11 min).
3. Judge `t5/judge_am.sh` (BEFORE, snapshot) and `t5/judge_am_after.sh` (AFTER, d012f51; ports each defect by stripping and restoring the heading label only). Clean trees fail only goal_guard and check_literals (see Start); a defect is caught only by another check.
4. Repairs after AM (not blind): FB10 fails closed on text before the first finding (d02), a finding key used twice (d03), any HTML comment that is not an exact block opener (d06; the prose regexes need the exact opener too), and requires the label *Author's title, unchecked:* in every heading (d04, d05); FB12: a registry class phrase applies only through an atom among a universal record's assumptions or inside an existence record's condition, and the generated Correct line quotes the Lean atom beside each phrase (d01). 45 selftest controls (29 before).

## Round AM

| d | defect | BEFORE (ffdcac7, blind) | AFTER (d012f51, not blind) |
|---|---|---|---|
| d01 | grow-only class-phrase registry line → generated Correct line of F1 claims "any spatial curvature" | **ACCEPTED** | CAUGHT (FB12; check_numbers) |
| d02 | "Index (generated …)" text between `## Verified findings` and F1, three false claims | **ACCEPTED** | CAUGHT (FB10) |
| d03 | a second `### F2` section with a hand-edited, generated-looking Printed line | **ACCEPTED** | CAUGHT (FB10) |
| d04 | F13 heading adds Guo et al. 2020 (the correct value) to the wrong values | **ACCEPTED** | ACCEPTED, heading now labelled unchecked |
| d05 | F3 heading moves the misprint to v1 (no reader describes F3's source) | **ACCEPTED** | ACCEPTED, heading now labelled unchecked |
| d06 | look-alike block opener hides a "Uniqueness (generated)" line in F14 | **ACCEPTED** | CAUGHT (FB10) |

**False acceptance (blind) against FB10/FB11: 6/6.** After the repairs: 2/6, both in the heading (not blind).

## Local checks and push
- `records_check.py 028d5c4` after the last edit: 38/40; the two failures are check_literals (plain and --base), whose `.lake/meaning.jsonl` (028d5c4) predates run 1640Z's eight headlines — as on the clean tree; no `.lean` file changed this run, so CI's own StatementDeps run decides them as for 7911453.
- Intermediate pushes carried `[skip ci]`; the final push (LOCK removed) starts the main run; its checked job replaces 7911453's pending one (it contains 7911453).

## Next start
- CI read first: the run of this run's final push (it contains c5c2a35 and 7911453; its checked job replaced 7911453's pending one). Green on every job → rows −0.13 … −0.16 PROVED and FB10–FB12 live: one L.2 line to Alexander.
- Part 3 next (STATE 0i): generate the heading (finding number + the reader-described sources of its printed values + the records' names) and move the author title into the notes; records for F4–F7; reader files for the pre-route readings of F3/F9/F10 (a fresh blind reading of the typeset source, then the generator describes it).
