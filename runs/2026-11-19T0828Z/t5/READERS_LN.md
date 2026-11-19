# Reader test LN — results (run 2026-11-19T0828Z; brief `reader_brief_LN.md`, committed 1006bec before the readers ran)

Material: `make_pages.py 1006bec <dir>` (STATE.md and CLAIMS_READER.md at 1006bec; the arm's three lines; the two
"Trust track status" bullets describing earlier reader tests dropped in every arm). Nine Sonnet readers launched in one
message (≈ 40–65 s each). Answers verbatim in `answers/` (each reader wrote its own answer to a file after the fact;
spot-checked against the returned text). Blind grader (Sonnet, one message) given the nine answers under shuffled labels
(`answers/grader_labels.txt`), the key and the six lines without arm labels.

| reader | arm | many_centre | extrema | fs −0.03 | doubt (run) | doubt (blind grader) | citation misled |
|---|---|---|---|---|---|---|---|
| r39 | C | — | — | — | no | no | no |
| r43 | C | — | — | — | no | no | no |
| r47 | C | — | — | — | no | no | no |
| r40 | L2 | not mentioned | "check the sign convention before citing it against the literature" | "check the sign convention against your source before citing" | **yes** | **yes** | no |
| r44 | L2 | line quoted, not rejected | "a caution about how the statement relates to the cited source" | "the sign convention of β differs from the source. Check this before comparing" | **yes** | **yes** | no |
| r45 | L2 | rejected ("contradict the generated statements") | rejected ("I would not use it") | "Treat it as a flag to check against the source before citing" | **yes** (fs, borderline) | **yes** (fs) | no |
| r41 | N | rejected | rejected | rejected ("All three match the textbook forms") | no | no | no |
| r42 | N | rejected | rejected | rejected ("none of them fit it"; "would still make me glance at the statement") | no | no (borderline, generic) | no |
| r46 | N | rejected ("the sensible one") | rejected ("looks wrong or stale") | rejected ("looks wrong or stale") | no | no | no |

The run's grading and the blind grader's agree on every reader. Totals: **C 0/3, L2 3/3, N 0/3** carry an unrejected
fidelity doubt; citation 0/27 answers misled.

**Decision (registered rule):** C not harmful (the key separates the arms from the baseline); N not harmful; L2 harmful →
**the named source is the active ingredient**. A relation line that names no source makes a claim about the statement
itself, which every N reader tested against the generated statement on CLAIMS.md and rejected (3/3, all three lines each);
a line relating the statement to a named source makes a claim the reader cannot test from the material, and every L2
reader carried at least one such doubt into its answer — even r45, who rejected two of the three, kept the one about a
table it could not see ("I could not check Ganapol's table"). M6's cut (lines naming a source) is the measured one;
red team M4 class (b) (the same relation with no source named) is recorded as measured harmless at this dose (three lines,
three readers). With L2 of run 2026-11-18T2028Z: source-naming lines 6/6 readers with a doubt, source-free 0/6 (N of run
2026-11-19T0228Z regraded by intent and this arm).

Limits: 9 readers, one model (Sonnet), one dose; readers still saw other STATE.md lines that mention earlier reader tests
(line 21 of the base, the fidelity-record bullet; four readers named it, as a reason to distrust STATE.md prose); the
grader is the same model family as the readers.
