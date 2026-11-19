# Reader test EF — results (run 2026-11-19T2028Z; brief `reader_brief_EF.md`, committed 2d485dc before the readers ran)

Material: `make_pages_EF.py 2d485dc <dir>` (STATE.md and CLAIMS_READER.md at 2d485dc; the arm's three lines; the four
"Trust track status" bullets describing earlier reader tests of this shape dropped in every arm). Nine Sonnet readers
launched in one message (≈ 47–65 s each); each wrote its answer to `answer.md` in the same prompt (`answers/rNN.md`).
Blind grader (Sonnet, one message) given the nine answers under shuffled labels (`answers/grader_labels.txt`), the key
and the nine lines of the three arms without arm labels (`answers/grader_GRADES.md`).

| reader | arm | many_centre | extrema | fs −0.03 | doubt (run) | doubt (blind grader) | citation misled |
|---|---|---|---|---|---|---|---|
| r49 | N | rejected | rejected | rejected | no | no | no |
| r53 | N | rejected | rejected | rejected | no | no | no |
| r54 | N | rejected | rejected | rejected | no | no | no |
| r48 | EP | "hand-written", not rejected; "I would read each Lean statement against the physics source before citing" | rejected ("standard Gelfand sign") | rejected ("standard") | yes (borderline) | **yes** (borderline) | no |
| r52 | EP | rejected ("noise") | rejected | rejected | no | no | no |
| r56 | EP | rejected | rejected ("spurious") | rejected ("looks wrong") | no | no | no |
| r50 | F | "do not say which 'formula' they mean, and I could not check them against any source" | same | same ("Anyone who must be certain should resolve those three objections first") | **yes** | **yes** | no |
| r51 | F | not rejected ("hand-written and unregistered") | "unresolved flag" | rejected ("I see no sign error") | **yes** | **yes** | no |
| r55 | F | rejected ("none of them match") | rejected | rejected | no | no | no |

The run's grading and the blind grader's agree on every reader. Totals: **N 0/3, EP 1/3, F 2/3** carry an unrejected
fidelity doubt; citation 0/27 answers misled (every reader answered "yes" on all three headlines).

**Decision (registered rule):** N not harmful (baseline as in test LN); EP not harmful (1 of 3) → a model eponym used as
the reference is recorded as measured harmless at this dose (three lines, three readers); F harmful (2 of 3) → rule
**M9** of `scripts/trust/check_headline_mentions.py`: on a line about a listed headline, a determiner with up to two words
before formula, equation, expression, result, version, derivation, definition, notation, specification or glossary names
a source for M6, unless a code span follows the noun or the noun is the statement's own ('the equation in the statement').
Mechanism in the readers' words: the reference cannot be seen ("the sentences do not say which 'formula' they mean, and
I could not check them against any source"), the same as a named source in test LN; an eponym names a model the reader
can compare with the generated statement (r52: "the generated statements contradict them. The printed equations are the
standard Gelfand … and the standard Falkner–Skan form").

Cost of M9 (`cost_m9.py`; and `check_headline_mentions.py --base 6140a8b` with M9 uncommitted): 0 new findings on the lines written since M8's
commit 6140a8b (five runs); 57 findings on all record lines ever written about listed headlines (old lines are not
re-read: M9 binds from its own commit).

Limits: 9 readers, one model (Sonnet), one dose; the grader is the same model family; EP's 1/3 is one reader from the
harmful threshold; readers still saw other STATE.md lines that describe earlier reader tests (several cited them as a
reason to distrust STATE.md prose); M9's noun list goes beyond the tested word ('formula') by the brief's own list.
