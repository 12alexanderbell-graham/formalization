# Run 2026-11-21T0228Z

**THE RESULT:** part 3 by rotation (STATE 2r). The check of this run and its three blind measures are in section What we did.

**What can a scientist now trust without checking it themselves, that they could not before?** That a hand-written line of STATE.md, README.md or BLUEPRINT.md which treats a classified hypothesis as still to be decided fails CI however it is worded: a third writer, blind to the new rule, got 1 of 16 such lines past it (the rule it replaces let 6 of 16 through on the same lines).

**Weakest unchecked step:** a hypothesis described by its content alone (a "density bound", a "regularity condition") of a headline that still has open hypotheses: no rule can tell which hypothesis is meant.

## Start
- 02:28Z. Local main was the stale divergent clone again (fa47717); `scripts/start_run.sh` reset it to origin/main (3dd65c8), installed elan and the Mathlib cache. No LOCK → taken (985f72e).
- Env: repo ok (add_repo not exposed; the session clone was present); local Lean installed (not needed: no `.lean` file changed); the `.lake` outputs of StatementDeps from the author-files artifact of 44849818184 (generated pages identical to main); two Sonnet subagents (held-out writers SN2, SN3).
- CI at start: 44849818184 (3dd65c8, run 0028Z's final push) completed.

## CI read
- 44849818184 (3dd65c8): **green on every job** (01:22Z → 02:06Z, 44 min). nanoda check 20.2 / 22.5 / 27.6 / 26.0 min (shards 0-3; ratio 1.37, below the 1.5 refit threshold of run 1428Z's Next), leanchecker replay 19.1 / 24.2 / 27.3 / 20.0 min. One new Trust module (`NecessityBI`), no headline changed: nothing to promote.

## Bottleneck (and what a yes/no changes)
- Part 3 by rotation, item of run 2028Z's section Next: the rule of `check_stale_necessity.py` had been widened after reading writer SN's lines (6/16 blind → 16/16 not blind). Does the widened rule hold on a writer it has not seen? Yes (≥ 0.8) → the word rules stand. No → a second miss in a row says that adding words after each writer does not converge, and the rule has to change shape.

## What we did
- **Test SN2** (brief `t5/BRIEF_SN2.md` registered alone 6933eaf; writer output `t5/writer_SN2.json` committed alone efa9274; scorer `t5/score_SN2.py`): a fresh Sonnet writer, the prompt of test SN, eight other headlines (`t5/trust_excerpt.txt`). **Blind: recall 8/17 by number, 0/3 by description, false positives 0/10**, below 0.8 for the second time. Misses: other plan verbs (need to show, check whether, work out whether, still to be tested, decide necessity of), a number before the name ('4, 5, 6 in `x`', '16 is redundant in `x`'), a hyphen range ('17-20'), a section line with no open word.
- **Root cause (annex LIV):** the rule looked for open words and then for numbers inside them; every writer uses open words the last one did not. **Rule S-N4 inverts the default:** every hypothesis number a line attaches to a headline (after the name, before 'of/in/for `x`', or in a clause about hypotheses under a single headline; numbers of formulas, durations, counts, tables, runs and code excluded) is flagged when TRUST_MAP classifies it, unless the line states that same classification: the list followed by its own word ('`x` 2, 3 NEEDED'), 'witnesses for …', or a clause or sentence stating needed / refutes / cannot be dropped (or redundant) with no plan or open word and not the other classification.
- **Test SN3** (prototype `t5/sn4_proto.py` frozen in 629109d before brief `t5/BRIEF_SN3.md`, registered alone 09764cd; writer output `t5/writer_SN3.json` committed alone a084aad): a third Sonnet writer, eight further headlines (`t5/trust_excerpt_SN3.txt`). **Blind: S-N4 recall 15/16, false positives 0/10; the word rules on main 10/16, 0/10.** Pre-registered rule met → S-N4 added to `scripts/trust/check_stale_necessity.py` as built.
- **Added after SN3 (NOT blind):** the one miss ('prove 16, 17, 18 necessary'; a list ending the line with a full stop was read as a decimal) and two rules for descriptions: **S-N5** reads an ordinal description as numbers ('the last hypothesis of `x`', 'the first two hypotheses', 'the second-to-last'; all 11 description lines of the three writers were ordinal), **S-N3** flags a clause that calls a hypothesis or condition of a headline open when TRUST_MAP lists none open for it, whatever the words. Planted controls 26 → 47 (S-N3 5, S-N4/S-N5 16). Scored together (`t5/score_all.py`): SN 16/16 + 4/4, SN2 17/17 + 3/3, SN3 16/16 + 4/4, false positives 0/30.
- **Cost on the records:** 0 lines of STATE.md, README.md, BLUEPRINT.md as they stand. On the records before run 2028Z's rewrite (c4715c6): the word rules flag 10 lines, the new check 12 (the two more are dated plans naming hypotheses classified since). Dated run READMEs (not read by the check): 22 lines by S-N4 and the word rules, 6 by S-N3, mostly stale plans; a few are lines that report a test of such lines.

## Measure
- Blind recall on held-out writers, by number: 6/16 (SN, word rules) → 8/17 (SN2, widened word rules) → **15/16 (SN3, S-N4)**; false positives 0/10 in each test. Description lines: 0 of 11 read before, 11 of 11 after (NOT blind).

## Local checks
- `check_stale_necessity.py --selftest` (47 controls), the check on the three files, planted lines on a copy of STATE.md (S-N1b and S-N3 fire), `check_necessity_prose.py`, the remaining commands in section End.

## Next
- CI read first: the run of this run's final push (scripts and records only; the kernel shards are memoised on unchanged input). Green on every job → nothing to promote. Red in the trust step → `check_necessity_prose.py` output.
- The remaining limit: a hypothesis described by its content of a headline that still has open ones. The hypothesis texts are known to StatementDeps; a generated per-hypothesis gloss in TRUST_MAP (the hypothesis's Lean text, shortened) would let a rule match a description against it. Measure first how often real records describe a hypothesis by content (the three writers never did: they saw numbers only).
- Then by rotation (part 3 at 0228Z, part 1 at 0028Z, parts 2/5 at 2228Z): parts 2/5 as in section Next of `runs/2026-11-20T2228Z/README.md`; part 1 as in section Next of `runs/2026-11-21T0028Z/README.md`; part 3 next as in this section.

## End
- Local: `check_stale_necessity.py` (47 controls; 0 findings on the three files), `check_necessity_prose.py`, `goal_guard.py`, `check_headline_mentions.py --base 3dd65c8` (one STATE line reworded twice for M1), `records_check.py 3dd65c8` (43 commands, 0 failed; `.lake` outputs of 44849818184's author-files, generated pages identical). Records: STATE 2s + daily review + Trust track line, LEDGER, CHANGELOG, BLUEPRINT, PROMPT working note; LOCK removed.
