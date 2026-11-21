# Brief SN6: write lines of a research log (held-out writer test, run 2026-11-21T0828Z)

You are helping test a checker of a research log. Do not look for, open or read any file under `scripts/`, `runs/` other
than this brief and `runs/2026-11-21T0828Z/t5/headlines_SN6.md`, or any `.py` file. Read only those two files.

Background. A repository proves physics statements in Lean ("headlines"). Each headline has numbered hypotheses.
A generated page classifies each hypothesis as NEEDED (dropping it makes the statement false), REDUNDANT (the statement
holds without it) or open (not yet decided). `runs/2026-11-21T0828Z/t5/headlines_SN6.md` lists four headlines with
their hypotheses and the current classification.

Hand-written log lines (bullets in a STATE.md-like file) often talk about hypotheses **by their content, without their
numbers**: "the wall condition of `x` is still open", "Next: the time orderings of `x`", "Not yet: whether the density
bound of `x` can be dropped". When the page has since classified such a hypothesis, the line is stale.

Write exactly 24 lines, each a markdown bullet, in the style of a terse research log, each naming at least one of the
four headlines in backticks by its short name (e.g. `fit_direction`):

- 16 STALE lines: each says, by content only (no hypothesis numbers, no ordinals like "the third hypothesis"), that a
  hypothesis the page classifies as NEEDED or REDUNDANT is open, unclassified, to be decided, planned, or still lacks a
  witness. Vary the wording as much as a real log would: different verbs, scope labels ("Not yet:", "Open:", "Part 1
  later:", "To do:"), plans ("check whether", "try to drop"), questions, parentheses, several headlines per line,
  descriptions in words or in formulas ("q > 0", "Ω ≤ 1", "the source redshifts", "the matching at the far source").
  Spread them over all four headlines.
- 8 HONEST lines that are not stale: e.g. a line stating a classification that agrees with the page in words ("the
  source redshifts of `fit_direction` are NEEDED"), a line about the headline that is not about its hypotheses ("Next:
  promote `x` to the reader page"), a line that refers to "the open hypotheses of `x`" in general, a line that gives
  the numbers of truly open hypotheses ("`x` 4 and 7 are open").

Write the result to `runs/2026-11-21T0828Z/t5/LINES_SN6.md`, one bullet per line, in random order, and the key to
`runs/2026-11-21T0828Z/t5/KEY_SN6.md`: for each line its number in LINES_SN6.md (1-based), STALE or HONEST, the
headline(s) and the hypothesis numbers meant. Do not run any program. Reply with one sentence when done.
