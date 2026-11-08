# Run 2026-11-08T0628Z (scheduled)

**THE RESULT:** part 3 moved: the *role* of every certified number in FINDINGS.md — the value of a source's printed formula, of a quantity the program derived, or their difference — is now read from its Lean statement and the checked labels of the definitions it evaluates, written next to the number in its tag, and checked against the words around it; the records that certified printed formulas as anonymous arithmetic now name them as PRINTED definitions read twice by a blind reader. Also: CI confirmed run 0428Z's promotion, so the Homann trio and Lane–Emden index 2 are PROVED.

**What can a scientist now trust without checking it themselves, that they could not before?** That when FINDINGS.md says a certified number is the *printed* value (or the true one, or the printed-minus-true error), Lean's statement says the same: e.g. "the printed l₀ is 0.685 instead of 3.115" can no longer be swapped, relabelled or attached to q₀ without CI failing, and the role sits in the tag itself (0.685[✓F1_printedL0(printed)]).

**Measure:** run 0028Z's adversary's open role defects (d1, d2, d5, d6) and five variants: 9/9 rejected (not blind; replayed in `replay/`). Blind red team U: see below. Baselines shrunk: records-selector 2 → 1, literal 7 lines (2 removed), prose 4, source names 4, claim vocabulary 11. Checked headlines 192 (unchanged), PRINTED definitions with a blind second reading +2.

**Weakest unchecked step:** values with role `free` (roots, poles, sizes such as F9_pole, F10_exceptions, F8/F11 sizes) carry no machine role, and role words outside the closed lists are not read: a reader is protected by the tag's role, not by the sentence.

## What we did
- Start (06:27Z): no LOCK; LOCK + stub 14723d7. elan + Mathlib cache, full `lake build Checked` in the background.
- Design: role = outermost program definitions of the certified quantity (pretty-printed by StatementDeps) and their labels in `def_kinds.txt`; prose rules R0–R4 in `check_numbers.py`; replay script for the 0028Z adversary.
- Lean: `printedAvilesL0`, `printedCLSL0` (PRINTED) and agreements with the blind readings of run 2026-11-05T2028Z; F1_printedL0, F2_toy, F2_error, F9_values restated; relock; Claims; packet.
- FINDINGS: role in every certified tag (`scripts_add_roles.py`), F3 and F9 sentences.
- Blind red team U (Sonnet; brief committed first): see `t5/`.
- Records: STATE, LEDGER, CHANGELOG, BLUEPRINT, PROMPT working note.

## CI
- 129f217 (42453268112): green on every job (checked: build 36 min, trust step 8 min, frozen registry, author files; work; nanoda shards 0–3).
- This run's pushes: read next run.
