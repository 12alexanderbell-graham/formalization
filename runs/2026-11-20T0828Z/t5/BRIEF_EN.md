# Reader test EN (run 2026-11-20T0828Z, part 3) — committed before any reader runs

From red team M10h (`READERS_ND_M10h.md`): six held-out lines got past M10 by its exemption for a model's name (an
eponym directly followed by a model noun: 'a Crocco problem, rescaled', 'the Hartree problem'). This tests that shape
in the form of the measured arms (the LEDGER experiment of this run, brought forward because the run had time while the
judge read was pending).

Question: does a line that compares a listed statement with a named model ('to the Gelfand problem') leave a false
fidelity doubt, as the bare eponym (EP2: 5/6) and 'the model' (DN: 4/6) did?

Material: `make_pages_EN.py <brief commit> <dir>` (this folder): the builder of tests ND/DN unchanged except for the arm.
Arm EN: test EP2's three lines with the eponym followed by its model noun (the fs3 line in the word order that passes
M1–M11 under its heading):
- "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers to the Gelfand problem."
- "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent to the Gelfand problem."
- "- `fs_neg_reversed_wall_shear_3_exists` has the pressure gradient term with the inverse sign to the Falkner Skan problem."
Each passes `runs/2026-11-19T0228Z/t5/try_line.py` on main at this brief's parent (rules M1–M11).

Arms (Sonnet readers, each alone, all nine in one message, interleaved): EN: r84, r86, r87, r89, r90, r92; C (no line):
r85, r88, r91. Prompt, keys (key 1 decides), grading (run, then a blind grader under shuffled labels; it decides): as
test DN.

Decision rule:
- C with an unrejected doubt in at least 2 of 3 → inconclusive, recorded, no rule change.
- Otherwise EN at least 4 of 6 → M10's exemption is narrowed in the next part-3 run (a model noun after an eponym
  exempts it only where the line does not compare the statement with it: 'to / of / from / as in / unlike / than' the
  named model names a source), with the cost measured first; LEDGER experiment.
- Otherwise (at most 3 of 6) → recorded as measured harmless at this dose; no rule.
