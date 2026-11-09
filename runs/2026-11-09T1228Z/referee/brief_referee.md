# Brief: referee of a certified existence proof (run 2026-11-09T1228Z)

Claim (Lean, compiled, standard axioms): `fs_neg_tenth_reversed` in `runs/2026-11-09T1228Z/lean/low/NegReversed.lean` — Falkner–Skan β = −1/10 has a solution with −1 ≤ f' ≤ 1, f' → 1, faster-than-every-exponential approach (∀ M, eventually M(1 − f') ≤ f''), and −0.1405462131 < f''(0) < −0.1405462129; and `fs_neg_tenth_two_decay`. Also `runs/2026-11-09T1228Z/lean/NegWindow.lean` (attached solution: 0.3192697598 < f''(0) < 0.3192697599 for every solution with f'' > 0 and the same approach).

Read: the statements; `runs/2026-11-09T1228Z/lean/low/LAssemble.lean` (events, tube, supremum argument), `LCell.lean`, `LInv.lean`, `LUnclamp.lean`; the plan `runs/2026-11-09T0428Z/research/fs_negative_beta.md` §1–3; generators `runs/2026-11-09T1228Z/scripts/gen_low.py`, `make_lower.sh` (may be run; they print margins).

Tasks:
1. Attack the statements: wrong normalisation (scaling F(s) = √10 f(s/√10)? sign of the pressure term?), vacuity, junk values, a quantifier or hypothesis that makes them weaker than the words in the docstrings.
2. Independently compute the reversed-flow wall shear at β = −0.1 (your own shooting code, ≥ 15 digits, two methods or two tolerances), and the attached one; compare with the windows.
3. Check the mathematical route in plain words: are the events open and disjoint as claimed, does the tube cover the whole window, why the neither-point has the decay property, and whether anything assumes what it proves.
4. Prior art: is the reversed-flow value printed (e.g. −0.140546, Asaithambi; Stewartson −0.141) consistent with the window?

Rules: web only via WebSearch/WebFetch; arxiv.org/pdf only (no ar5iv, no e-print); a failed or blocked fetch is "not read", never retried by curl/wget/code. Python in a temp dir outside the repository. Do not edit any repository file except your report `runs/2026-11-09T1228Z/referee/REPORT.md`; if your Write tool refuses, return the report as text. Do not run `lake build`. Do not commit.
