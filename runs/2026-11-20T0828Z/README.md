# Run 2026-11-20T0828Z

**THE RESULT:** part 3 by rotation (STATE 2i → part 3 as in section Next of `runs/2026-11-20T0228Z/README.md`, trust track T5). Five pre-registered measurements: reader test ND (plain false descriptions at double dose), held-out red team M10h, reader test DN, which decided rule M11, reader test EN (the shape M10 exempts) and held-out red team M11h.

**What can a scientist now trust without checking it themselves, that they could not before?** A hand-written line that compares a listed statement with an unnamed reference ('to the model', 'as in the theory', 'of the method', 'the data') can no longer sit next to it in the records; such lines left a false fidelity doubt in 4 of 6 blind readers. And, measured: false descriptions of what a statement says, with no reference, misled 0 of 6 readers at double dose (four of them refuted the lines from the generated statement).

**Weakest unchecked step:** the rules read word shapes; a held-out red team still gets 4 of 20 unnamed references past M11 by a new qualifier ('the real problem', closed after the fact), so each rule is as good as its closed lists. The judge's slowest job is still nanoda shard 1 (82 min of 116 for the last promotion).

## Start
- 08:28Z. Local main was a stale divergent clone (fa47717); `git checkout -B main origin/main` at e2eaeee. No LOCK → taken (0c0c737).
- CI at start: 44698202534 (e2eaeee, run 0628Z's final push) in progress; read in section CI read.
- Local Lean: not needed for the measurements (no `.lean` change); elan and the restored build of 6b8fc4c set up for the end checks (section End).

## Bottleneck (and what a yes/no changes)
- Part 3 (rotation): (1) are plain false descriptions of a statement (20 lines of red team M9h pass every rule) harmful at double dose? Yes → a structural rule next; no → recorded harmless. (2) Does M10 catch held-out eponym references (LEDGER experiment of run 0228Z)? And which reference kind still passes every rule most often → its reader test, and a rule if harmful.

## What we did
- **Brief first** (`t5/BRIEF_ND_M10h.md`, committed cdf0842 with the page builder `t5/make_pages_ND.py` before any reader or red team ran).
- **Reader test ND** (nine blind Sonnet readers in one message on STATE.md + CLAIMS_READER.md of cdf0842; arm ND: arm N's three lines plus three plain false descriptions — 'the ball is of dimension two, the planar disk', 'the finite sequence of the extrema of lam, with the dimension two', 'the wall shear is positive, the attached flow' — six lines; control C: no line). Blind grader under shuffled labels (`t5/READERS_ND_M10h.md`): **ND 0/6 misled, C 0/3**; four ND readers quoted the lines and refuted them from the generated statement (Fin 3, the sign, q 0 < 0). By the registered rule: harmless at double dose, no rule.
- **Red team M10h** (held out at 548ea21, rules M1–M9; brief excluded lines with no pointer at a reference, the fix of run 0228Z): 29 class-A lines in ≈ 2 min (`t5/m10h_lines.txt`), 29/29 pass at the target. On main: model eponyms 14/20 flagged (70 %, below the registered 80 %: M10 not effective); the six that pass put the eponym before a model noun ('a Crocco problem, rescaled'). Determiner + noun ('the model', 'the theory', 'the method', 'the physical problem', 'the data') 0/9 flagged: the most frequent passing kind → test DN.
- **Reader test DN** (brief `t5/BRIEF_DN.md` committed 15b2aa9 first; test EP2's three lines with 'to the model' in place of the eponym; nine readers, control C of three; `t5/READERS_DN.md`): **DN 4/6 unrejected fidelity doubt, C 0/3** (blind grader; the run's own grading 3/6) — "I see no defect, but I would check the sign/quantifier conventions against the source". By the registered rule → **rule M11** of `scripts/trust/check_headline_mentions.py`: on a line about a listed headline, a determiner, an optional qualifier (physical, original, standard, usual, …) and a reference noun (model, theory, method, data, literature, textbook, reference, convention, physics; problem / form / case after a qualifier) names a source for M6, unless a code span follows or it is the statement's own; named models ('the Gelfand model') are M10's case. Binds from its commit (`m11_grandfathered`). Selftest 92 → 103 defects, 9 → 11 correct lines. Cost (`t5/cost_m11.py`): 0 findings on lines since M10's commit, 8 on all record lines ever written (not re-read).

- **Reader test EN** (brief `t5/BRIEF_EN.md` committed 75c8b2a first; the six M10h eponym lines passed M10 by its exemption for a model's name, so test EP2's lines with 'to the Gelfand problem' / 'to the Falkner Skan problem'; `t5/READERS_EN.md`): **EN 0/6, C 0/3** (blind grader). Recorded harmless; M10's exemption stays. Every EN reader that named the lines checked them against the standard form of the named problem and rejected them.

- **Red team M11h** (brief `t5/BRIEF_M11h.md` committed ccdb477 first; held out at 15b2aa9, rules M1–M10): 27 class-A lines, 27/27 pass at the target; on main unnamed references 16/20 flagged (80 %: **M11 EFFECTIVE** by the registered rule), the four passing all 'the real problem' → `M11_QUAL` + real, actual, true (hardened after the fact, not blind; selftest 107 defects); eponym + model noun 0/7 (harmless by test EN).

## Measure
- T5: reference shapes measured harmful and now closed: eponym (M10, 5/6), unnamed reference by determiner + noun (M11, 4/6). Plain false descriptions: 0/6 at double dose (pooled with arm N, record only: 1 of 15 readers). Held-out red-team class-A lines passing every rule: 29/29 at 548ea21 → 6/29 on main with M11 (the eponym + model-noun shape).
- Same three sentences, only the reference changes: bare eponym 5/6, 'the model' 4/6, named problem ('to the Gelfand problem') 0/6, none 1/3 and 0/6 — the harm follows a reference the reader cannot identify, not the false content and not a named model the reader can check.

## CI read
- 44698202534 (e2eaeee, run 0628Z's final push: `Checked/Trust/NecessityBC.lean`, no headline changed) concluded green on every job at 09:38Z (checked job, work job, leanchecker 4/4, nanoda 4/4) → nothing to promote; hypothesis 3 of `fs_monotone_of_limit` NEEDED is judged.

## End
- Local before the final push: elan + Mathlib cache, `checked-build` of 44682554465 (6b8fc4c) restored (the zip deleted first: the disk allowance filled once during the restore), `lake build Checked` (3735 jobs, two rebuilt), StatementDeps without relock (303 headlines, NV 183/183; NEEDED 744, REDUNDANT 219, open 60; TRUST_MAP unchanged), Claims (303 generated claims; CLAIMS.md unchanged), check_headline_mentions selftest (107 defects, 11 correct lines) and `--base` 6b8fc4c and e2eaeee, goal guard, records_check.py 6b8fc4c and e2eaeee (43 commands, 0 failed).

## Next
- CI read first: the run of this run's final push (M11 in the checked job's records step; no Lean change, so the kernel jobs should report memoised passes).
- **The judge first, for the first hour (PROMPT note of this run; deferred by runs 0028Z, 0228Z, 0628Z and this one):** nanoda shard 1 (82 min) bounds every promotion; find its heavy declarations (export module groups with `exportshard`, time nanoda on each) before giving nanoda its own assignment; refresh `scripts/nanoda/shard_times.txt` from the newest four leanchecker logs.
- Then by rotation (part 3 at 0828Z, part 1 at 0628Z, parts 2/5 at 0428Z): parts 2/5 as in section Next of `runs/2026-11-20T0428Z/README.md`; part 1 as in section Next of `runs/2026-11-20T0628Z/README.md`. Part 3 later: the shape now most often passing every rule is the named model as the reference (7 of 27 M11h lines), measured harmless (EN 0/6); so part 3's next measure is the whole-page one — a fresh blind reader test on the records as they stand (no inserted lines) against a page with only generated text, to see whether any hand-written line still moves a reader.
