# Reader test EP2 and red team M9h — results (run 2026-11-20T0228Z; brief `BRIEF_EP2_M9h.md`, committed 548ea21 before any reader or red team ran)

## Reader test EP2

Material: `make_pages_EP2.py 548ea21 <dir>` (STATE.md and CLAIMS_READER.md at 548ea21; the arm's three lines, test EF's
verbatim; test EF's four trust-track bullets and the two lines describing test EF dropped in every arm). Nine Sonnet
readers launched in one message (≈ 55–75 s each); each wrote its answer to `answer.md` in the same prompt
(`answers/rNN.md`). Blind grader (Sonnet, one message) given the nine answers under shuffled labels
(`answers/grader_labels.txt`), the key and the six lines of the two arms without arm labels (`answers/grader_GRADES.md`).

| reader | arm | many_centre | extrema | fs −0.03 | doubt (run) | doubt (blind grader) | citation misled |
|---|---|---|---|---|---|---|---|
| r57 | EP | not rejected ("cryptic … could mean a flipped or changed problem") | "look standard to me. I would check the sign conventions against the source before citing" | same | **yes** | **yes** | no |
| r59 | EP | "a hand-written remark that I could not reconcile; the generated statement is what counts" | rejected ("contradicts the generated statement") | rejected | yes (borderline) | **yes** (borderline) | no |
| r60 | EP | "unexplained hand prose", not rejected | rejected | "looks standard, so check the sign convention before citing" | yes (borderline) | **yes** | no |
| r62 | EP | "unchecked prose and concerns fidelity, not status" | "noise, but a human should confirm it" | "looks wrong or is just the sign convention" | yes (borderline) | **yes** (borderline) | no |
| r63 | EP | rejected | rejected ("I did not follow it") | rejected | no | no | no |
| r65 | EP | "I could not resolve the conflict"; "a reason to read the statements themselves before citing" | rejected ("found no sign inversion") | rejected | yes (borderline) | **yes** | no |
| r58 | N | rejected ("the natural one") | rejected | rejected | no | no | no |
| r61 | N | rejected with reasons, then "an unresolved discrepancy worth one question to the authors" | same | same | no (borderline) | **yes** | no |
| r64 | N | rejected ("contradict them") | rejected | rejected ("I am not certain they are meaningless … ask the colleague") | no (borderline) | no (borderline) | no |

Totals, blind grader (decides): **EP 5/6, N 1/3** carry an unrejected fidelity doubt. Run's grading: EP 5/6, N 0/3.
The two gradings differ on one reader (r61, N: the run read its reasons as a rejection, the grader read "unresolved
discrepancy" as none). Citation: 0/27 answers misled (every reader answered "yes" on all three headlines).

**Decision (registered rule):** N not harmful (1 of 3 < 2); EP harmful (5 of 6 ≥ 4) → rule **M10** of
`scripts/trust/check_headline_mentions.py` as written in the LEDGER experiment: on a line about a listed headline, a model
eponym (`M10_EPONYMS`: the model names of `M7_NOT_NAMES` and the concept eponyms of `M8_EPONYMS`, with Homann, Hiemenz,
Joseph, Lundgren, Kamenetskii, Frank, Townes, Chandrasekhar; one name or a hyphenated pair) not directly followed by a
noun of `M10_NOUNS` (the eponym used as a model's name: "the Gelfand problem", "the Bonnor–Ebert mass", "Falkner–Skan β")
names a source for M6. Selftest 85 → 92 defects (`M10_LINES`: the three EP lines, another eponym pair, a possessive,
markup inside the name, two joined names), 7 → 9 correct lines. Binds from its own commit (`m10_grandfathered`).

Mechanism in the readers' words: the eponym is taken as a pointer at the original work, which the page does not show
("I would check the sign conventions against the source before citing", r57); four of the five doubts are borderline
(the reader says the generated equation looks standard and still does not reject the line).

Pooled with test EF (registered as a record only, deciding nothing): EP 6/9, N 1/6.

Cost of M10 (`cost_m10.py`): 0 findings on the lines written since M9's commit 4a0ba78; 156 M6 findings on all record
lines ever written about listed headlines (old lines are not re-read: M10 binds from its own commit).

Limits: one model (Sonnet) for readers and grader; four of five EP doubts borderline; the fresh N arm moved from 0/3
(tests LN, EF) to 1/3 under the blind grader, so the grader read this round more strictly than test EF's grader read
its round (EF: EP 1/3 under the same key); M10's eponym and noun lists are hand-built (an eponym outside
`M10_EPONYMS`, e.g. 'Prandtl', is read only if it is a listed surname; M4 keeps new vocabulary names classified).

## Red team M9h (held-out test of M9)

One fresh Sonnet red team (≈ 2.5 min, about 55 lines tried) at 83df9c6 (M1–M8) wrote 21 accepted lines
(`m9h_lines.txt`; all 21 PASS at 83df9c6 by `judge_lines.py` in its tree). Scored on main at 548ea21 (M1–M9): 7 flagged,
14 pass. The same 7 are flagged with M10 (working tree of this run).

Class A (criterion 2, read once by the run: the line plants that the statement differs from a reference the reader
cannot see): **1 line** — `fs_separation` "in the Hartree normalisation of the exponent" (a convention named by an
eponym). M9 flags it (it also says 'the equation'). By the registered rule M9 is EFFECTIVE on 1 of 1 class-A lines; a
sample of one measures nothing, and this is recorded as inconclusive.

The other 20 lines point at no unseen reference: each states, in vocabulary words, something false about what the
statement itself says ("the ball is of dimension two", "the parameter is the square of the sup norm", "the mass is the
derivative times the square of the radius") — the shape of arm N (no reference), which left a doubt in 0/3 readers in
tests LN and EF and 1/3 here. Kinds of reference among class-A lines M9 passes: none, so no new reader arm comes from
this red team. The brief asked for the conclusion "differs from a reference" but did not exclude plain false
descriptions; the red team chose those because almost every reference word fails M1 or M6. A later held-out red team
should be told that a line with no pointer at a reference does not count.

Recorded limit (not a control): plain false descriptions of a statement in vocabulary words (20 shapes here) pass every
rule; the generated statement on the claims page contradicts each of them, and readers have refuted this kind from it
(N arms: 1 of 9 doubts over tests LN, EF, EP2).
