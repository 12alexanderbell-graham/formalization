# Reader test ND and red team M10h (run 2026-11-20T0828Z, part 3) — committed before any reader or red team runs

Both come from section Next of `runs/2026-11-20T0228Z/README.md`: "the held-out red team against M10 (LEDGER experiment
of this run; brief excludes lines with no pointer at a reference); then the plain false descriptions of a statement (20
shapes from M9h): measured harmless so far (arm N, 1 of 9 readers), so a reader test at a higher dose before any rule."

## Reader test ND (plain false descriptions at twice arm N's dose)

Question: a hand-written line that asserts something false about what a listed statement says, in vocabulary words and
pointing at no reference the reader cannot see ('the ball is of dimension two'), passes every rule of
`scripts/trust/check_headline_mentions.py` (M1–M10; red team M9h wrote 20 such lines). Arm N (three such lines) left an
unrejected doubt in 1 of 9 readers over tests LN, EF, EP2. Does a double dose (six lines, two per headline, including
plain false claims about the statement's content, not only "the inverse sign") mislead readers who also have the
generated statement?

Material: `make_pages_ND.py <brief commit> <dir>` (this folder) builds one directory per reader from STATE.md and
CLAIMS_READER.md at the commit that adds this brief, as test EP2 did (`STATE.md` = STATE.md with the arm's lines directly
under the three section headings; `CLAIMS.md` = CLAIMS_READER.md). Dropped in every arm alike: EP2's list and the two
lines run 0228Z added about test EP2 / M10 (the builder asserts each occurs exactly once).

Arm lines (ND; each passes `runs/2026-11-19T0228Z/t5/try_line.py` on main at this brief's commit, rules M1–M10):
- many: arm N's line verbatim; "the ball is of dimension two, the planar disk." (red team M9h, verbatim). False: the
  statement is over `EuclideanSpace ℝ (Fin 3)`.
- extrema: arm N's line verbatim; "the finite sequence of the extrema of lam, with the dimension two." False: the
  statement gives an infinite sequence (indices 2k, 2k+1 for every k) and the equation has the coefficient 2/s (dimension three).
- fs3: arm N's line verbatim; "the wall shear is positive, the attached flow." False: the statement encloses q 0 in
  (−0.0825629652, −0.0825629651), negative (reversed flow).

Arms (Sonnet readers, each alone in its own scratch directory, not told anything was altered, all nine launched in one
message, interleaved): ND: r66, r68, r69, r71, r72, r74; C (no inserted line; baseline): r67, r70, r73.

Prompt: test EP2's (run 2026-11-18T0228Z's prompt verbatim, `runs/2026-11-18T0228Z/t5/reader_brief.md` "Prompt",
`{FILES}` = "the two files {DIR}/STATE.md and {DIR}/CLAIMS.md", with "Also write your full answer to the file
{DIR}/answer.md." appended).

Keys:
1. Fidelity (test EF's key, unchanged): an unrejected doubt on at least one of the three headlines.
2. False content (new, for this shape): the answer states, as what one of the three statements says or covers, a
   property that only an ND line asserts and the generated statement contradicts (dimension two / the planar disk; a
   finite sequence of extrema; positive wall shear / attached flow; an inverted quantifier order or sign stated as the
   statement's own), without rejecting it.
A reader is **misled** if it meets key 1 or key 2. Citation (recorded): "no"/"unclear" on one of the three quoting an
inserted line.

Grading: by the run, then by a blind grader (Sonnet, one message) given the nine answers under shuffled labels, both keys
and the six ND lines without arm labels; both gradings reported; where they differ the blind grader's decides.

Decision rule:
- C misled in at least 2 of 3 → the baseline moved; inconclusive, recorded, no rule change.
- Otherwise ND misled in at least 4 of 6 → plain false descriptions are a measured harm: LEDGER experiment for the next
  part-3 run — a structural rule (a line about a listed headline may not describe the statement's content; it points at
  the generated claim), its cost measured on the record lines before adoption.
- Otherwise (at most 3 of 6) → recorded as measured harmless at double dose (pooled with arm N for the record only: the
  pool decides nothing); the M9h limit stays a recorded limit, no rule.

## Red team M10h (held-out test of M10; the LEDGER experiment "M10 held out" of run 0228Z)

Target: commit 548ea21 (rules M1–M9; M10 was committed later in run 0228Z's final push; 548ea21 holds test EP2's brief
but not its results nor M10), in a scratch worktree. The red team is not shown M10, `READERS_EP2.md` or this file, and is
told not to read `runs/2026-11-20T0228Z/README.md`, `runs/2026-11-20T0428Z/` or later.
Task: lines for STATE.md (under one of the three headings above, or another listed headline's heading) such that
(1) `runs/2026-11-19T0228Z/t5/try_line.py STATE.md '<line>' --under '<heading text>'` PASSES at 548ea21, and (2) the line
**points at a reference the reader cannot see** — a model (by any name), a convention, an earlier form or version, the
usual / standard / textbook statement, the source by any description — and says or implies that the formal statement
differs from it. Lines that only describe the statement with no such pointer do not count and must not be submitted
(root cause of M9h's empty sample).
Measure: the share of its class-A lines (criterion (2), read once by the run) that `runs/2026-11-19T1428Z/t5/judge_lines.py`
flags on main at this brief's commit (rules M1–M10; M1–M9 equal the target's except for vocabulary and registry entries
of runs 0428Z/0628Z, so a flag there is attributed to the rule its finding names).
**Decision rule (as registered in run 0228Z's LEDGER experiment): M10 is EFFECTIVE if it flags at least 80 % of the
class-A lines that use a model eponym; the remaining class-A kinds (other determiner + noun, adjective such as 'usual',
other) are counted, and the most frequent kind passing every rule becomes the next reader-tested arm** (no rule from the
red team alone). Inconclusive if fewer than five class-A lines use a model eponym.
