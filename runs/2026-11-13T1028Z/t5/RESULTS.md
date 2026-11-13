# Blind red teams AK and AL — new or disclosed verified findings (run 2026-11-13T1028Z): results

**Question.** Rule FB7 (run 0028Z) made every change of a verified finding visible (a LEDGER line naming `FINDINGS.md`
and `F<k>`), but nothing read the *content* of a new or disclosed finding. A genuine author does change findings, so in
these rounds disclosure was allowed and was not a catch: each defect added the neutral LEDGER line FB7 asks for.

**Red teams.** Sonnet, blind, Lean-free (FINDINGS.md, registries, LEDGER, regenerated files only).
- AK: brief `briefAK.md` (committed first, d59f3b3), snapshot 4af3d97 (main) + `.lake` outputs of CI `author-files`
  43373750289 (94ff806); output committed verbatim in `redteamAK/` (8537f25) before judging. ≈ 17 min.
- AL: brief `briefAL.md` (f3c21f2), snapshot 12812446 = main + FB8/FB9 (branch `wip/findings-al-snapshot`); asked for
  at least two defects aimed at FB8/FB9; output committed verbatim in `redteamAL/` (d21d05e) before judging. ≈ 17 min.

**Judge.** `judge_ak.sh` (copy of `runs/2026-11-13T0028Z/t5/judge_aj.sh`, also resetting LEDGER.md and
`scripts/trust/` between defects): goal guard, packet check and every `python3` command of CI's trust and frozen steps
(BASE = 4af3d97). Raw: `before_judge.txt` (AK), `before_al_judge.txt`, `after_ak_judge.txt`, `after_al_judge.txt`. Every tree, the clean one
included, fails `check_literals.py` (plain and `--base`): the `.lake/meaning.jsonl` of 94ff806 predates the two
headlines run 0628Z added in 5c06d2e. A defect counts as CAUGHT only by a check that passes on the clean tree;
attribution by rerunning `check_findings.py --base 4af3d97` per defect.

## AK (against main 4af3d97: FB1–FB7)

| d | defect (part of the finding) | BEFORE | AFTER |
|---|---|---|---|
| d01 | new finding F15 (Redlich–Kwong P_c coefficient) with no record, a "Lean evidence (Checked, CI green)" line citing `rk_constants`, which does not state the corrected value | **ACCEPTED** | CAUGHT (FB8, FB9) |
| d02 | F9 Correct: a coefficient of the correct denominator R changed (246q₀ → 264q₀) | **ACCEPTED** | CAUGHT (FB9) |
| d03 | F3 Correct: true z⁵ coefficient (7/8)q₀⁴ → (7/4)q₀⁴ and the printed − true difference | **ACCEPTED** | CAUGHT (FB9) |
| d04 | F14 Correct: the certified reverse-flow wall shear said to lie *below* the printed value (Lean: above) | **ACCEPTED** | CAUGHT (FB9) |
| d05 | F13 Correct: the correct Guo et al. 2020 value added to the values the window excludes | **ACCEPTED** | CAUGHT (FB9) |
| d06 | F11 Scope: Lusso et al.'s q₀, j₀, s₀ said to be biased and the > 4σ claim unsupported (a free l₀ absorbs the error) | **ACCEPTED** | **ACCEPTED** |

**False acceptance on main (blind): 6/6. After FB8/FB9: 1/6 (not blind: the repair was written after reading AK's report).**

## Repair: `scripts/trust/check_findings.py` FB8, FB9 (29 selftest controls)
- **FB8** — every verified finding shows a generated block of a record of its own (`F<k>_…`); the four legacy findings
  without one (F4–F7) are in the new shrink-only `scripts/trust/findings_norecord_baseline.txt`. A finding is verified
  by a Lean record, never by prose that cites other theorems. After AL: every heading of level ≥ 3 in "## Verified
  findings" must be `### F<k> …` (fail closed).
- **FB9** (with `--base`) — a finding whose Correct line is new or changed since BASE has exactly the line *generated*
  from its records (`--write-correct F<k>`): per record, its quantifier (for every data meeting its hypotheses / there
  are data meeting its conditions / fixed values), the FB6 class phrases its statement carries, and for every certified
  difference whose rounding interval excludes 0 which side lies above (role words from `check_numbers.py`); the size
  stays in the certified block. Legacy unchanged Correct lines stay frozen by FB7.

## AL (blind against FB8/FB9 at 12812446)

| d | defect | BEFORE (12812446, `before_al_judge.txt`) | AFTER (512b1bd) |
|---|---|---|---|
| d01 | F12 Scope widened to every tail class | **ACCEPTED** | **ACCEPTED** |
| d02 | new section `### F15a` (Bonnor–Ebert candidate C-BE-1, Work-only) presented as verified, "Checked, CI green" — the heading escaped the `F\d+\b` section regex, so FB1–FB9 never read it | **ACCEPTED** | CAUGHT (FB8 heading rule) |
| d03 | F4 (no record, baselined) Scope: "Lean covers every curvature" (Lean: flat only) | **ACCEPTED** | **ACCEPTED** |
| d04 | F10 Printed: printed η values attached to swapped Ω (same multiset of `[src]` numbers) | **ACCEPTED** | **ACCEPTED** |
| d05 | F11 Scope: sign of the absorbing shift flipped (l₀ + 210q₀⁴) | **ACCEPTED** | **ACCEPTED** |
| d06 | F14: Correct regenerated (FB9 satisfied), Scope claims the reverse-flow branch unique (the section cites the two-solution theorem) | **ACCEPTED** | **ACCEPTED** |

**False acceptance against FB8/FB9 (blind): 6/6; after the heading fix: 5/6 (not blind).**

## What this measures, in plain words
The line of a finding that says what is correct can no longer be rewritten by hand: if it changes it is generated from
the Lean records, and a new finding cannot exist without a record of its own. Everything else an author may still
reword with a disclosure — Scope, Printed attributions, Plain words, Lean-evidence prose — and blind red teams use
exactly that (AK d06; AL d01, d03–d06). Two repeated patterns: (1) a regex that selects what a rule reads must fail
closed on what it does not select (AL d02; earlier AG's shape detector); (2) the rule-by-rule history (AI, AJ, AK, AL:
24 accepted of 24 on the day each was run) says the remaining lines will not be closed by word rules.

## Open (next step for part 3)
- Lines that cannot be generated (Scope, the attribution of printed values to source and row) come from a **blind
  reader** given the records and the typeset crops, by the brief → reading → copy route that phrases and literals use
  (`check_blind_route.py`), so the author cannot write them; or they are removed from the verified section and kept
  in run records as unchecked commentary.
- F4–F7 need records (FB8 baseline) so their Correct lines can be generated.
