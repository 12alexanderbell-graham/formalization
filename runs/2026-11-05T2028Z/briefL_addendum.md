# Addendum for blind round L (prepared run 2026-11-05T2028Z; use with runs/2026-11-05T0828Z/t5/briefK.md)

New evidence route since round K: grandfathered links were closed by blind second readings/formulations
(`Checked/Trust/SecondReadingClaims*.lean`, `SecondFormulation{D,E}.lean`) and, for source CLAIMs, by a
generated module that substitutes a reader's data into the program claim's text
(`runs/2026-11-05T2028Z/scripts/gen_claim_readings.py`). The only guards on this route are mechanical
equality (Lean) and disclosure (a LEDGER line naming every new declaration and the word "brief").

Ask the red team for at least three defects aimed at it, e.g.:
- a new wrong CLAIM (invented or misprinted formula) whose "second reading" module was written by the author
  (data copied from the program), disclosed in LEDGER like a genuine one;
- a generated "second-reading claim" that also changes a quantifier, a hypothesis or the remainder order while
  substituting data, so the agreement proves equality with a claim the source never made;
- a second formulation that imports the program module and reuses a program constant under another name.
The judge then measures whether any check rejects them; a pass is a structural gap (proposal: the generated
module must be reproducible byte for byte by the committed generator from the program text and the reader
files, and reader files must be byte-identical to a file under `runs/*/` written before the agreement commit).
