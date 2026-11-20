# Reader test DN (run 2026-11-20T0828Z, part 3) — committed before any reader runs

From the decision rule of red team M10h (`BRIEF_ND_M10h.md`, judged in this run before this brief): the class-A kind
that passed every rule (M1–M10) most often was a determiner + noun used as the reference ('the model', 'the theory',
'the method', 'the physical problem', 'the data': 9 lines), so it becomes the next reader-tested arm. No rule from the
red team alone.

Question: does a line that compares a listed statement with 'the model' (a reference the reader cannot see) leave a false
fidelity doubt, as the eponym did (test EP2: 5 of 6)?

Material: `make_pages_DN.py <brief commit> <dir>` (this folder): the builder of test ND unchanged except for the arm.
Arm DN: test EP2's three EP lines with 'to Gelfand' / 'of Falkner–Skan' replaced by 'the model' (the fs3 line reworded
to 'has the inverse sign to the model' because 'is the inverse of the model' is flagged by M6 under that heading):
- "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers to the model."
- "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent to the model."
- "- `fs_neg_reversed_wall_shear_3_exists`: the pressure gradient term has the inverse sign to the model."
Each passes `runs/2026-11-19T0228Z/t5/try_line.py` on main at this brief's commit.

Arms (Sonnet readers, each alone, all nine in one message, interleaved): DN: r75, r77, r78, r80, r81, r83; C (no inserted
line): r76, r79, r82. Prompt, keys (key 1 fidelity decides; key 2 recorded), grading (run, then a blind grader under
shuffled labels; the blind grader decides): as test ND.

Decision rule:
- C with an unrejected doubt in at least 2 of 3 → inconclusive, recorded, no rule change.
- Otherwise DN with an unrejected doubt in at least 4 of 6 → rule M11 of `scripts/trust/check_headline_mentions.py` in
  this run: on a line about a listed headline, a determiner + reference noun of a closed list (`M11_REF_NOUNS`: model,
  theory, method, physical problem, data, …) names a source for M6; selftest with the three DN lines and the passing
  M10h determiner lines; binds from its commit; cost measured on lines since M10's commit.
- Otherwise (at most 3 of 6) → recorded as measured harmless at this dose; no rule.
