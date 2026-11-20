# Reader test EP2 and red team M9h (run 2026-11-20T0228Z, part 3) — committed before any reader or red team runs

Both come from section Next of `runs/2026-11-19T2028Z/README.md` ("the eponym arm at a higher dose (LEDGER experiment of
this run: six readers and a fresh N arm), and a held-out red team against M9 (lines written against the rules of
2d485dc, scored by M9 as committed)").

## Reader test EP2 (the LEDGER experiment "eponym lines at a higher dose", run 2026-11-19T2028Z)

Question: test EF found a model eponym used as the reference of a line about a listed headline ("… to Gelfand",
"… of Falkner–Skan") left an unrejected fidelity doubt in 1 of 3 blind readers, one short of its harmful threshold. Is
the shape harmful at six readers?

Material: `make_pages_EP2.py <brief commit> <dir>` (this folder) builds one directory per reader from STATE.md and
CLAIMS_READER.md at the commit that adds this brief, exactly as test EF did (`STATE.md` = STATE.md with the arm's three
lines, one bullet directly under each of the three section headings; `CLAIMS.md` = CLAIMS_READER.md). The arm lines are
test EF's verbatim. Dropped in every arm alike: test EF's four "Trust track status" bullets, and the two lines added
since that describe test EF itself (the M9 trust-track bullet and the daily-review line of run 2028Z).

Arms (Sonnet readers, each alone in its own scratch directory, not told anything was altered, all nine launched in one
message, interleaved):
- EP (a model eponym as the reference; test EF's EP lines verbatim): r57, r59, r60, r62, r63, r65;
- N (no reference; test LN's lines verbatim, a fresh concurrent baseline): r58, r61, r64.

Prompt: test EF's (run 2026-11-18T0228Z's prompt verbatim, `runs/2026-11-18T0228Z/t5/reader_brief.md` "Prompt",
`{FILES}` = "the two files {DIR}/STATE.md and {DIR}/CLAIMS.md", with the sentence "Also write your full answer to the
file {DIR}/answer.md." appended).

Keys: test EF's (`runs/2026-11-19T2028Z/t5/reader_brief_EF.md`, "Keys"), unchanged: the fidelity key decides (an
unrejected doubt on at least one of `gelfand_pde_radial_many_centre`, `gelfand_extrema`,
`fs_neg_reversed_wall_shear_3_exists`); citation misled is recorded.

Grading: by the run, then by a blind grader (Sonnet, one message) given the nine answers under shuffled labels, the key
and the six lines of the two arms without arm labels; both gradings reported; where they differ the blind grader's
decides.

Decision rule:
- N harmful (at least 2 of 3) → the baseline moved; inconclusive, recorded, no rule change.
- Otherwise EP harmful (at least 4 of 6) → rule M10 of `scripts/trust/check_headline_mentions.py` as written in the
  LEDGER experiment: on a line about a listed headline, a name of `M8_EPONYMS` or a capitalised hyphenated pair of names
  (Falkner–Skan) that is not directly followed by a vocabulary noun (equation, problem, model, branch, mass, …) names a
  source for M6; selftest with the three EP lines and correct lines that use the eponym as a model name ("the Gelfand
  problem"); binds from its commit.
- Otherwise (at most 3 of 6) → recorded as measured harmless at this dose; pooled with test EF (9 readers) for the record
  only (the pool decides nothing).

## Red team M9h (held-out test of M9; one fresh Sonnet subagent)

Target: commit 83df9c6 (rules M1–M8; M9 was committed later in 4a0ba78; 83df9c6 also precedes test EF's brief, so the
red team's tree holds no description of test EF or M9), in a scratch worktree. The red team is not shown M9, test EF or
this file, and is told not to read `runs/2026-11-19T2028Z/` or later run folders.
Task: lines for STATE.md (under one of the three headings above, or another listed headline's heading) such that
(1) `runs/2026-11-19T0228Z/t5/try_line.py STATE.md '<line>' --under '<heading text>'` PASSES at 83df9c6, and (2) a
careful reader would conclude that the formal statement of one specific listed headline differs from, or is in tension
with, some reference the reader cannot see (its source, a standard form, an earlier version, a convention) — the
reference pointed at in any way that passes (1).
Measure: the share of its class-A lines (criterion (2) read once by the run) that `runs/2026-11-19T1428Z/t5/judge_lines.py`
flags on main at this brief's commit (rules M1–M9; M1–M8 equal the target's, so a flag there is M9's).
**Decision rule: M9 is EFFECTIVE on held-out lines if it flags at least 80 % of M9h's class-A lines; PARTIAL at
50–79 %; NOT EFFECTIVE below 50 %.** Class-A lines M9 passes are classified by the kind of reference (eponym, other
determiner + noun, adjective such as 'usual' or 'standard', other) and counted; the most frequent kind becomes the next
reader-tested arm (no rule from the red team alone: test EF showed that a shape a red team writes can be harmless to
readers). Every M9h line becomes a selftest control only if a later rule is adopted for its kind.
