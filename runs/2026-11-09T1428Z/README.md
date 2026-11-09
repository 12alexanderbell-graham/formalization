# Run 2026-11-09T1428Z (scheduled)

**THE RESULT:** part 3 — the plain-words phrase of every pinned definition in a generated claim is now **produced by CI from blind readings alone** rather than checked for coverage: the last author choices (for a property, which arguments are the subject, the verb, the article; every connective, the order of blind texts and how a split quotient is joined) are gone. A blind shape reader fixed subject, verb and article for the nine properties; `check_claims.py` regenerates every phrase from the registry with one fixed template and fails unless the phrase file is exactly that output (P10, P11, stated before blind red team AC ran), and the registry keeps each reader file's order, cites it once, admits no invisible characters, and never lets an excluded reader line back in (P11a–c, P12).

**What can a scientist now trust without checking it themselves, that they could not before?** That the sentence explaining a defined quantity or property inside a generated claim (e.g. "the position as function of time x is a Duffing oscillator initial value problem solution with …", "the cosmographic coefficient … (n-th time derivative of the scale factor over the scale factor divided by the n-th power of the Hubble rate; …)") is a mechanical function of blind readers' texts: no author can make it say "the solution" instead of "a solution", drop an argument, swap a Greek letter's case, hide a sentence behind an invisible line break, reorder clauses so a divisor attaches to the wrong clause, or show a reader line the program had judged false.

**Measure (phrase layer):** blind red team AC (Sonnet, brief 3dcc21f committed alone; P10/P11 stated in d48a572 before it ran): as submitted against the snapshot's rules **6/6 pass**; against this run's rules **0/6 pass** — d04 (an argument's role omitted), d05 ("the" solution: uniqueness overstated), d06 (Ω0 → ω0) caught by P10/P11 as stated before AC (**blind 3/6**); d01 (U+000B hid text from the checker that Claims.lean printed), d02 (an excluded overclaim un-excluded), d03 (registry order glued a divisor to the wrong clause) by P11a, P12, P11b (not blind). Adversary AD (Sonnet, on P10–P12 as first implemented): **4/4 pass**; after the repair (P11c) **2/4** (d02, d04 open: see weakest step). Judge's variants d02b, d03b (AC) and d03b (AD) rejected.

**Weakest unchecked step:** the content of a blind reading. AD d02/d04: an author may commission a new, honest-looking reading whose lines restate an excluded overclaim in other words ("an inflection point of the isotherm with horizontal tangent") or a hypothesis as a property; P9 then requires the line to be shown. Only the main session's clause-by-clause check against the Lean body stands between such a line and CLAIMS.md, and no script checks it. Also open: the SIGN line "positive curvature constant gives above one" of `omega0` is false at the junk value hubble = 0 (AD side note; the shrink-only baseline cannot take a registered SIGN line out).

## Start
- 14:28Z. add_repo not exposed (session repo pre-cloned, detached at 9e1586d with a stale local main); `git checkout -B main origin/main` = 9e1586d. No LOCK; taken bcdb283 (14:31Z).
- Environment: repo reachable (push); local Lean: elan + toolchain v4.35.0 + Mathlib cache, full `lake build Checked` from 14:30Z in the background (see below). Python rules run locally throughout.
- CI read at start: 83ebad4 (42626827566, run 1028Z's β < 0 promotion): goal guard, packet, changes, work, nanoda 4/4 green; **checked job cancelled by coalescing**. 10576fa (42628579635) and 9e1586d (42630582568) cancelled likewise. The first run of the current tree with a checked job: 3dcc21f (42635575605), see CI below.

## Bottleneck
STATE exact next step 2 (part 3 by rotation; five runs without part-3 progress): a blind round on P7–P9 and the predicate shapes. Yes: the phrase layer has no author choice left that a red team can use; no: the "the/a" article, subject and joins remain hand-chosen words in every generated claim that uses a property.

## Work
1. Shape reader brief d48a572 (P10, P11 stated), red team AC brief 3dcc21f, each committed alone; both Sonnet agents launched in one message on read-only snapshots (`git archive`), outputs committed before any rule: shape reading 4a0fa02, AC output d8450d9.
2. The first shape reader had not been given the blind NAME lines and chose verbs that do not fit them ("the scale factor is a … expansion law", "p is a critical point condition"): lesson below. Second brief 9f4f014 (with the NAMEs, from `runs/2026-11-08T2228Z/names/NAMES.txt`), reading 0533e79: for all nine properties exactly the subject, verb and article of the former `PRED` (each checked against the Lean body in the main session) → no phrase changed.
3. P10/P11 in `check_claims.py` (`registry_shapes`, `generate`, `generated`, `--generate`; template moved from `runs/2026-11-09T0228Z/scripts/gen_phrases.py` into CI code), P11a/P11b/P12 after AC (e1f0f34). Judge `t5/judge_AC.py` → `t5/judge_AC.out`.
4. Adversary AD (brief 9189018 alone, output 66a278f before the repair) → P11c (074906b): one source block per reader file, no registry line twice, reader files free of invisible characters, joins anchored on the previous reader line's text, an unjoinable "divided by" text fails. Judge `t5/judge_AD.py` → `t5/judge_AD.out`.
5. Planted controls for the P3 route and P12 (`scripts/trust/route_control.py`, CI step in the goal-guard job, 31f9758). The control's first version re-added an existing line and so "passed" every bad sequence: the bug was in the control, the route check was right once a new line was used.
6. `check_literals.py` rule-1 message now explains author constants inside conclusions (STATE next step 2's lesson of run 1028Z).

## Judge
| defect | move | snapshot rules | this run's rules |
|---|---|---|---|
| AC d01 | U+000B in phrases.txt: text hidden from check_claims (splitlines), printed by Claims.lean | passes | rejected, P11a + P11 (not blind) |
| AC d02 | excluded "equivalent to equal chemical potential" un-excluded and shown | passes | rejected, P12, P11b (not blind) |
| AC d03 | two registry lines swapped: "divided by …" glued to "orders 0 and 1 coefficients are one" | passes | rejected, P11b (not blind) |
| AC d04 | roles of w₀, wₐ omitted from IsFlatCPL | passes | rejected, P11 (blind) |
| AC d05 | "is the … solution" (uniqueness) for three IVPs | passes | rejected, P10/P11 (blind) |
| AC d06 | Ω0 → ω0 | passes | rejected, P11 (blind) |
| AD d01 | clause reading cited twice around a symbol line: divisor glued to order 2 | passes | rejected, P11c |
| AD d02 | new reading restating three excluded overclaims in other words | passes | **passes (open)** |
| AD d03 | honest two-line reading: dedupe + join on the last text | passes | rejected, P11c |
| AD d04 | new reading of siblings restating excluded hypotheses | passes | **passes (open)** |

## Lessons
- A blind reader choosing a grammatical slot must see the blind texts that fill the neighbouring slots: the shape reader without the NAMEs wrote readings that were each defensible and together false sentences. Give a reader every blind text its output will be joined to (PROMPT working note).
- A control that "passes" a bad case is first a suspect control: the route check was right; the control re-added an existing line.

## CI
- 3dcc21f (42635575605; Lean tree = run 1228Z's head, incl. run 1028Z's promotion 83ebad4 and 1228Z's Work proofs 9f7db47): goal guard, packet, changes, work, nanoda 4/4 (memoised) and **checked green** (build 14:42–15:18Z, trust step, frozen registry, author files; read 15:37Z) → **the four β < 0 headlines of 83ebad4 (`fs_neg_decay_max_shear`, `fs_neg_decay_equal`, `fs_neg_tenth_exists_decay`, `fs_neg_tenth_outside_decay`) are PROVED**, and so is every other STATE item still marked "PROVED once green" (14 lines updated).
- This run's later pushes (rules e1f0f34, 074906b, 31f9758; records): earlier ones cancelled by coalescing; the latest main run is read at the end of the run (below) or by the next run.
- Local, end of run: full `lake build Checked` green (14:30–15:50Z, 79 min); `lake env lean scripts/trust/Claims.lean` (228 claims, CLAIMS.md byte-identical); `check_claims.py` lint with P10–P12 on the real `.lake/phrases.jsonl`: 23 phrases, 0 problems; `--base 9e1586d` and `--base 3dcc21f` green. CI: 31f9758 (42644286245) goal-guard job incl. the new route-control step **green**; its checked job cancelled by coalescing; fcdef1e (42644624186) checked job and cbb38ab (42646789985): read next run.
- LOCK removed in the final records commit.
