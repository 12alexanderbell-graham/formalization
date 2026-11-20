# Test ND and red team M10h: results (run 2026-11-20T0828Z; brief BRIEF_ND_M10h.md, committed cdf0842 before any reader or red team ran)

## Reader test ND (plain false descriptions at twice arm N's dose)
Nine Sonnet readers launched in one message on pages built by `make_pages_ND.py cdf0842` (answers in `answers/`).
Blind grader (Sonnet, one message, shuffled labels `grade_labels.json`, both keys and the six ND lines without arm labels):

| reader | arm | label | key 1 (fidelity doubt) | key 2 (false content) | misled | citation misled |
|---|---|---|---|---|---|---|
| r66 | ND | X9 | no (quotes L3, L2, L6: "They contradict the generated statements: CLAIMS.md shows Fin 3, the sign '- Real.exp', and q 0 < 0") | no | no | no |
| r67 | C | X1 | no (generic) | no | no | no |
| r68 | ND | X4 | no | no | no | no |
| r69 | ND | X5 | no (quotes "the ball is of dimension two" as a misreading the statements contradict) | no | no | no |
| r70 | C | X2 | no (refers to the refuted earlier Work file) | no | no | no |
| r71 | ND | X6 | no; borderline on L5 (rejects L1, L2, L6 explicitly; "contradictory bullets about two of these theorems") | no | no | no |
| r72 | ND | X3 | no | no | no | no |
| r73 | C | X7 | no (generic) | no | no | no |
| r74 | ND | X8 | no (rejects L1, L2, L5, L6: "contradict the generated statement, so I ignored them") | no | no | no |

The run's grading agrees on every reader. **ND 0/6 misled, C 0/3**; citation 0/27 misled. Four of the six ND readers
quoted the inserted lines and rejected them from the generated statement (Fin 3, the sign, q 0 < 0).
**Decision (registered rule): ND at most 3 of 6 → plain false descriptions recorded as measured harmless at double dose;
no rule.** Pooled with arm N of tests LN, EF, EP2 for the record only: 1 of 15 readers.

## Red team M10h (held out at 548ea21, rules M1–M9)
One Sonnet subagent, ≈ 2 min, 29 lines (`m10h_lines.txt`), 29/29 pass at 548ea21 (checked by `judge_lines.py` in the
worktree). All 29 point at a reference the reader cannot see (class A, read once by the run). On main at cdf0842
(rules M1–M10), per kind (findings by rule; every flag is M6 via M10's eponym-as-source):

| kind | lines | flagged on main | pass |
|---|---|---|---|
| model eponym | 20 | 14 | 6 |
| determiner + noun ('the model', 'the theory', 'the method', 'the physical problem', 'the data') | 9 | 0 | 9 |

M10 on class-A eponym lines: **14/20 = 70 % → below the registered 80 %: M10 not EFFECTIVE (partial).** The six eponym
lines that pass all put the eponym before a noun of `M10_NOUNS` (the exemption for a model's name: 'a Gelfand problem in
a ball of radius two', 'the Hartree problem', 'a Crocco problem, rescaled', 'the Falkner Skan problem with rescaled
scaling', 'a Gelfand problem, rescaled' under the Falkner–Skan heading). Most frequent kind passing every rule:
determiner + noun (9) → the next reader-tested arm (test DN, `BRIEF_DN.md`).
