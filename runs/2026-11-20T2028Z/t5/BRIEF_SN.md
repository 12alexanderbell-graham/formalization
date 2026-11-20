# Brief SN (run 2026-11-20T2028Z): held-out writer test of `check_stale_necessity.py`

Registered before the writer is launched (this commit). The writer is a Sonnet subagent that is NOT shown the check,
its rules, its docstring or this run's README; it sees only this brief's section "Writer prompt" and the excerpt
`trust_excerpt.txt` (seven necessity lines of TRUST_MAP.md, witness names removed).

## Question
Stale 'open' lines arise innocently: a run writes an accurate line ("hypothesis 8 open") and a later run classifies
the hypothesis. Does the check flag such lines when they are written the way an author writes, not the way the
check's author expected?

## Arms (written by the writer, labelled by the writer in a JSON file)
- **STALE** (20 lines): each says or implies that at least one hypothesis that the excerpt lists as needed or
  redundant is open / unclassified / still to do. Varied: STATE.md bullet styles, plan items ("next: …"), section
  bullets under a heading naming the headline, lists over several headlines, the hypothesis named by number.
- **TRUE** (10 lines): each mentions only hypotheses the excerpt lists as open, as open; or states a classification
  correctly.
Each line is scored as written (one line, no line breaks). A STALE line that names a hypothesis by description only
(no number) is kept and counted separately (the check does not read descriptions: documented limit).

## Measure and decision rule (pre-registered)
- Recall = STALE lines with a number flagged / STALE lines with a number. False positives = TRUE lines flagged.
- Recall ≥ 0.8 and no false positive → the check binds as built. Recall < 0.8 → the missed shapes are recorded in
  the LEDGER; shapes that a regular expression can read without new false positives on the TRUE lines and on the
  current STATE.md / README.md / BLUEPRINT.md are added in this run, and the after-figure is reported as NOT blind.
  Any false positive → fixed in this run, reported.
- Section-scoped lines (no headline name on the line) are scored inside a scratch section whose heading line names
  the headline in backticks, as STATE.md sections do.

## Writer prompt
You write status lines for a research log in Markdown. The log has hand-written lines about Lean theorems
("headlines") and their numbered hypotheses; a generated table (excerpt below) says, for each headline, which
numbered hypotheses are shown needed, shown redundant, or still open. Old lines in the log were accurate when they
were written, but later work classified more hypotheses, so some old lines now call a classified hypothesis open.

Task: write 30 one-line log entries into a JSON file (path given below) as a list of objects
{"id": "s01".."s20" or "t01".."t10", "kind": "STALE" or "TRUE", "section_headline": null or a headline name,
"by_number": true/false, "line": "..."}.
- s01–s20 (STALE): each line, read today against the excerpt, wrongly says or implies that at least one hypothesis
  the excerpt lists as needed or redundant is open, unclassified, unresolved, undone or still to be shown. Write them
  as a busy researcher would, in varied styles: bullets ("- **Necessity:** …"), "Not yet: …", plan items
  ("Next: …", "Part 1: …"), lists over several headlines, short and long. Usually name the hypothesis by its number;
  in at most four lines describe it in words instead (set by_number false). For up to six lines, leave the headline
  name off the line and give it in "section_headline" (the line sits under a heading naming it). Use backticks for
  headline names (e.g. `fs_neg_tenth_monotone_lt` or `FREta.eta_ratios`), as the log does.
- t01–t10 (TRUE): lines that are correct against the excerpt: they call open only hypotheses the excerpt lists as
  open, or state a classification correctly, in the same styles.
Do not try to trick any program; write natural log lines. Write only the JSON file.
