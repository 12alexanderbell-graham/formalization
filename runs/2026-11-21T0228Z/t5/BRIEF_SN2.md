# Brief SN2 (run 2026-11-21T0228Z): second held-out writer test of `check_stale_necessity.py`

Registered before the writer is launched (this commit, alone). Planned by run 2026-11-20T2028Z (section Next): the
rules of that run were widened after reading writer SN's lines, so their after-figure (16/16) is NOT blind. This test
gives the blind figure for the widened check (main at 985f72e, unchanged since 2026-11-20T2028Z apart from records).

Same design as `runs/2026-11-20T2028Z/t5/BRIEF_SN.md` (question, arms, scoring), with:
- a fresh Sonnet writer, not shown the check, its rules, its docstring, any run README or the first writer's lines;
- an excerpt of eight OTHER headlines (`trust_excerpt.txt` in this folder, witness names removed; none of the seven
  of test SN), one of which (`B1L19.l19_sq_central`) has no open hypothesis left;
- the writer prompt below: the prompt of test SN verbatim, plus one sentence on headlines with no open hypothesis.

## Measure and decision rule (pre-registered)
- Recall = STALE lines with a number flagged / STALE lines with a number. False positives = TRUE lines flagged.
  Description-only STALE lines are scored separately (documented limit of the check).
- Recall >= 0.8 and no false positive -> the widened check stands as built (blind figure recorded).
- Recall < 0.8 -> the missed shapes are recorded in the LEDGER; shapes a regular expression can read without new
  false positives on the TRUE lines of SN and SN2 and on the current STATE.md / README.md / BLUEPRINT.md are added in
  this run, after-figure reported as NOT blind.
- Any false positive -> fixed in this run, reported.
- Description-only lines about a headline that TRUST_MAP lists with NO open hypothesis are decidable without reading
  the description (anything called open there is stale). If any such line is missed, a rule for it (S-N3) is written
  after scoring (NOT blind) and its cost on the records measured.
- Scoring: `score_SN2.py` (the scorer of test SN, pointed at this folder).

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
  headline names (e.g. `fs_monotone_of_limit` or `B1Fit.fit_direction`), as the log does. A headline whose excerpt line lists no
  open hypothesis has none left.
- t01–t10 (TRUE): lines that are correct against the excerpt: they call open only hypotheses the excerpt lists as
  open, or state a classification correctly, in the same styles.
Do not try to trick any program; write natural log lines. Write only the JSON file.
