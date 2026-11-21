# Brief SN3 (run 2026-11-21T0228Z): third held-out writer test, of rule S-N4 (default-deny) as frozen

Registered before the writer is launched (this commit, alone). Test SN2 (this folder) gave the blind figure of the
widened word-rule check: recall 8/17, description 0/3, false positives 0/10 (below 0.8 for the second time: 6/16 in
SN). This run then wrote a prototype rule S-N4 that inverts the default (`sn4_proto.py`, committed before this
brief): every hypothesis number the line attaches to a headline whose TRUST_MAP entry classifies it is flagged
unless the clause or its sentence states that same classification with no plan or open word. Its figures on SN
and SN2 (16/16, 17/17, false positives 0/20, 0 lines on STATE.md / README.md / BLUEPRINT.md) are NOT blind: it was
written after reading SN2's lines.

This test gives S-N4's blind figure: a fresh Sonnet writer, not shown any check or earlier writer, the prompt of
SN2 verbatim (headline examples changed to this excerpt's), and an excerpt of eight further headlines
(`trust_excerpt_SN3.txt`, witness names removed; none of SN's or SN2's; three have no open hypothesis left).

## Measure and decision rule (pre-registered)
- Recall = STALE lines with a number flagged by `sn4_proto.py` as committed before this brief / STALE lines with a
  number; false positives = TRUE lines flagged. The check on main (word rules) is scored beside it.
- Recall >= 0.8 and no false positive -> S-N4 is added to `scripts/trust/check_stale_necessity.py` as built
  (blocking with the existing rules), with planted controls; the blind figure recorded.
- Otherwise: S-N4 is still added if it beats the word rules without a false positive on the bound files; the
  misses are recorded in the LEDGER and any change after this test is reported NOT blind.
- Scoring: `score_SN3.py`.

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
  headline names (e.g. `cubic_shape_miss` or `FalknerSkan.NegDecay.fs_neg_decay_equal`), as the log does. A headline whose excerpt line lists no
  open hypothesis has none left.
- t01–t10 (TRUE): lines that are correct against the excerpt: they call open only hypotheses the excerpt lists as
  open, or state a classification correctly, in the same styles.
Do not try to trick any program; write natural log lines. Write only the JSON file.
