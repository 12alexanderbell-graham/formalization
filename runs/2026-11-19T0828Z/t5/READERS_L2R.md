# Reader test L2R — results (run 2026-11-19T0828Z; brief `reader_brief_L2R.md`, committed e5372b5 before the readers ran)

Material: `make_pages_r.py e5372b5 <dir>`: STATE.md with the three L2 lines (as in test LN), CLAIMS_READER.md at e5372b5,
whose Status lines now print every registered blind literal reading of the source (`<reader def> := <body>`; for
`gelfand_extrema` e.g. `gelfandRhs := fun s w φ => -(2 / s * φ s) - Real.exp (w s)`; for the β = −0.03 row
`fsRevRowWantedRhs := fun f p q η => -(f η * q η) - -3 / 100 * (1 - p η ^ 2)`). Three Sonnet readers in one message
(≈ 40–60 s). Answers verbatim in `answers/r48.md`–`r50.md`. Blind grader (Sonnet) given these three answers mixed with
LN's L2 answers r40, r44, r45 under shuffled labels (`answers/grader2_labels.txt`).

| reader | many_centre | extrema | fs −0.03 | doubt (run) | doubt (blind grader) | citation misled |
|---|---|---|---|---|---|---|
| r48 | — | "The equation has the opposite sign of the exponent from Joseph–Lundgren 1973" | "Check the sign before matching it to a table." | **yes** | **yes** | no |
| r49 | "its relation to literature, such as 'dual of Joseph–Lundgren'" (borderline) | "a hand-written note on the source relation, not an objection" | "If you cite it as Ganapol's row, check the sign convention." | **yes** | **yes** | no |
| r50 | — | "STATE.md says the equation has the 'inverse sign of the exponent' relative to Joseph–Lundgren 1973" | "warns that the sign convention … is the inverse of Ganapol 2010 Table 7" | **yes** | **yes** | no |

**Decision (registered rule): NOT EFFECTIVE** — 3/3 carry an unrejected doubt (LN's L2: 3/3). No reader mentioned the
printed readings; each read the statement itself and the STATE.md line, and the readings sat at the end of a long
generated Status line. Printing the source's form on the page does not by itself neutralise a source-naming relation
line; M6 stays the only guard and its recorded limits (generic descriptions, names outside the list) stay open.
The printed readings are kept (a reader who looks for the source's form now finds it on the page; nothing is weakened),
recorded as not measured effective.

Second blind grading of LN's L2 answers (same key, mixed with L2R): r40 yes, r44 yes, **r45 no** ("contradicts the
generated statement" read as a rejection of the β line; LN's grader read the following "check against the source" as
keeping the doubt). LN's L2 arm stays harmful under either grading (3/3 or 2/3).

Next (part 3): the readings may help only where a reader is pointed at them. Two candidate tests: (i) a generated
sentence directly under each headline heading ("the source's own form, read blind: …", its own line, not inside the
Status line); (ii) a reader prompt that asks to check fidelity explicitly. Or accept M6 as the measured guard and close
its two open limits structurally: a `source=` registry entry per headline (literal_readings already carries some) so
every source a record may name is in the list by construction.
