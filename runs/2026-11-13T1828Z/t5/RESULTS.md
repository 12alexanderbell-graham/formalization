# Blind red team AM — the generated layout of verified findings (run 2026-11-13T1828Z): results

**Question.** Can a dishonest author make the part of a verified finding a reader is told to trust (heading, generated
Printed and Correct lines, certified blocks) say something false while every CI check stays green, after FB10/FB11?

**Red team.** Sonnet, blind, Lean-free; brief `briefAM.md` (committed in ffdcac7, the snapshot); snapshot ffdcac7 as a
standalone clone with the `.lake` outputs of the author-files artifact of 43422957898; output `redteamAM/` committed
verbatim (9dde6b1) before judging; ≈ 11 min.

**Judges.** `judge_am.sh` (BEFORE, tree ffdcac7) and `judge_am_after.sh` (AFTER, tree d012f51; each defect ported only
by stripping the heading label before `apply.py` and restoring it after). Every command of CI's trust and frozen steps
plus goal_guard and make_packet --check. Clean trees fail goal_guard (stub run README) and check_literals (stale
meaning.jsonl) only; a defect counts as CAUGHT only by another check. Raw: `before_am_judge.txt`, `after_am_judge.txt`.

| d | defect | valid? | BEFORE | AFTER |
|---|---|---|---|---|
| d01 | a grow-only registry line (atom: a certified number of F1_l0's conclusion) makes the generated Correct line say "any spatial curvature and any dark-energy equation of state" (F1_l0 assumes flat ΛCDM) | yes | **ACCEPTED** | CAUGHT (FB12; check_numbers reads the quoted atom's decimal) |
| d02 | an "Index (generated …)" paragraph between `## Verified findings` and F1, in no section, with three false claims | yes | **ACCEPTED** | CAUGHT (FB10) |
| d03 | a second `### F2` section (dict keys: the later one shadowed it) with a generated-looking Printed line citing Eq. (21) | yes | **ACCEPTED** | CAUGHT (FB10) |
| d04 | F13's heading adds Guo et al. 2020 Table 8 (the correct rounding) to the wrong values | yes | **ACCEPTED** | ACCEPTED (heading now labelled *Author's title, unchecked*) |
| d05 | F3's heading moves the misprint to arXiv v1 (F3's reading has no reader file, so no generated source description) | yes | **ACCEPTED** | ACCEPTED (same label) |
| d06 | a look-alike opener `<!-- certified: F14_reversed_wall_shear. -->` hides a "Uniqueness (generated …)" line from FB10 and FB7 | yes | **ACCEPTED** | CAUGHT (FB10) |

**Blind false acceptance against FB10/FB11: 6/6. After the repairs: 2/6 (not blind), both in headings.**

**The planted-reader attack failed blind:** the red team found no way to make FB11 quote a description that is not the
original reader's (ancestor rule).

**In plain words.** Four of six attacks were on the machinery that separates generated from author text (a registry
the generator trusts, text outside any section, a duplicate key, a look-alike marker): each is now a fail-closed rule.
The two that remain are the heading, the one author line every reader reads. Labelling it is not the same as checking
it; the structural fix is to generate it (STATE 0i (a)).
