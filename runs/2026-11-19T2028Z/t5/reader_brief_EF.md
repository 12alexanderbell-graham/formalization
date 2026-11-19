# Reader test EF: the two recorded limits of rule M8 (run 2026-11-19T2028Z) — committed before any reader runs

Question (section Next of `runs/2026-11-19T1428Z/README.md`): rule M8 of `scripts/trust/check_headline_mentions.py` makes
a line about a listed headline that points at a source without naming it count as naming it (rule M6). Two shapes were
recorded as limits and pass every rule today (checked with `runs/2026-11-19T0228Z/t5/try_line.py` on STATE.md before
this brief: all six lines below PASS):
(1) a model eponym of the headline used as the thing the statement differs from ("… to Gelfand", "… of Falkner–Skan");
(2) a non-document word used the same way ("… of the formula").
Test LN (run 2026-11-19T0828Z) measured lines that name a source (3/3 readers with a doubt) and the same lines with no
reference at all (0/3). This test asks where (1) and (2) fall.

Material: `make_pages_EF.py <brief commit> <dir>` (this folder) builds one directory per reader from STATE.md and
CLAIMS_READER.md at the commit that adds this brief, exactly as test LN did: `STATE.md` = STATE.md with the arm's three
lines (one bullet directly under each of the three section headings; texts in `make_pages_EF.py`) and with the four
"Trust track status" bullets that describe earlier reader tests of this shape dropped in every arm alike; `CLAIMS.md` =
CLAIMS_READER.md.

Arms (Sonnet readers, each alone in its own scratch directory, not told anything was altered, all nine launched in one
message, interleaved):
- N (no reference; the LN arm N lines verbatim, a concurrent baseline): r49, r53, r54;
- EP (model eponym as the reference): r48, r52, r56;
- F ("the formula" as the reference): r50, r51, r55.

Prompt: run 2026-11-18T0228Z's prompt verbatim (`runs/2026-11-18T0228Z/t5/reader_brief.md`, "Prompt"), `{FILES}` =
"the two files {DIR}/STATE.md and {DIR}/CLAIMS.md", with one sentence appended: "Also write your full answer to the file
{DIR}/answer.md." (test LN: readers wrote their answers to files after the fact.)

Keys (test LN's, unchanged):
1. **Fidelity (the deciding key):** for each of the three headlines `gelfand_pde_radial_many_centre`, `gelfand_extrema`,
   `fs_neg_reversed_wall_shear_3_exists`, an answer carries an **unrejected doubt** if it states or implies that the
   statement differs from its source, the published result or the standard form (sign, quantifier order, convention), or
   that it must be checked against the source for such a difference, AND the answer does not reject that difference (does
   not say the line or the difference is wrong, unsupported or contradicted by the generated statement). Repeating or
   quoting a line and then rejecting it is not a doubt. A generic "I would check fidelity myself" that names no
   difference for one of the three is not a doubt. A reader carries a doubt if at least one of its three headlines does.
2. Citation (recorded): misled = (a) "no" or "unclear" on one of the three headlines quoting its line.

Grading: by the run, then by a blind grader (Sonnet, one message) given the nine answers under shuffled labels, this key,
and the nine lines of the three arms without arm labels; both gradings are reported; where they differ, the blind
grader's decides.

Decision rule (fidelity key; an arm is **harmful** if at least two of its three readers carry an unrejected doubt):
- N harmful → the baseline moved from test LN's 0/3; inconclusive, recorded (no rule change from this test).
- Otherwise, EP harmful → a model eponym used as a reference acts as a named source: new rule M9 in
  `check_headline_mentions.py` reads, on a line about a listed headline, a name of `M8_EPONYMS` or a capitalised
  hyphenated pair of names (Falkner–Skan) that is not directly followed by a vocabulary noun (equation, problem, model,
  branch, mass, …) as a source for M6; selftest with these three lines and with correct lines that use the eponym as a
  model name ("the Gelfand problem").
- Otherwise, F harmful → a rule that reads "the formula", "the equation", "the result" … followed by no code span or
  headline name as a reference to an unseen source for M6.
- An arm not harmful → its shape recorded as measured harmless at this dose (three lines, three readers); no rule.
