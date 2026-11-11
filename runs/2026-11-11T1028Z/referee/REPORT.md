# Referee report (run 2026-11-11T1028Z; Opus subagent; saved by the main session — the subagent's Write was refused by the harness)

**Verdict: STANDS-WITH-CORRECTIONS.** Both Lean statements of `Work/FalknerSkan/Neg1988.lean` are the right formalization and true with margin; corrections concern the docstring/headline only:
- (a) a correctly rounded value is in print: Guo, Zhuang, Meng & Rabczuk, arXiv:2010.05682, Table 8, **0.005218** (WebFetch summary only, UNVERIFIED until typeset-read) — so "every printed value is wrong" is false as stated;
- (b) Zhu–Cheng–Wu (2009 preprint, math.ecnu.edu.cn) Table 5 row "-0.1988 0.005229 0.005225 0.005226 7.51 6.68" (summary, UNVERIFIED);
- (c) the printed values are 3–11 units too large in the 4th significant digit (with the carry, the 3rd printed digit also changes);
- (d) Fazio's reverse-flow −0.005158 is also off (true −0.0051574).

## 1. Attack on the statements
- Junk values, quantifiers: none found. One-sided derivatives on `Ici 0`; window literals exact. Window alone would be vacuous without existence; existence closes it; `Checked.FalknerSkan.NegDecay.fs_neg_decay_equal` (all β < 0) gives uniqueness in the class.
- The tabulated attached solution is in the class: collocation at L = 10 gives f'' > 0 at every node (min 1.3e-13 at the right end), f' < 1, f''/(1 − f') = 1.146, 1.944, 2.860, 3.816, 4.789, 5.776, 6.764 at η = 3…9, growing like x = η − δ (δ = 2.3329801727), as the parabolic-cylinder tail g = e^{−x²/4}D_ν(x), ν = −1 − 2β, predicts.
- The class excludes exactly the right solutions: reverse-flow branch (f''(0) = −0.0051574) and zero shear excluded by `hpos`; algebraic tails (1 − f' ~ Cη^{2β}) have f''/(1 − f') ~ 2|β|/η → 0 and fail the decay condition; the linearised tail with f'' > 0 is a combination of the Gaussian and algebraic modes only.
- Normalisation: every source read uses f''' + ff'' + β(1 − f'²) = 0 with β = −0.1988 (Fazio 2012 eq. (1.5) typeset; Asaithambi 2021; Zhu–Cheng–Wu; Guo et al.; Smith 1954). Converted: m = β/(2 − β) = −0.0904129525; in f''' + ((m+1)/2)ff'' + m(1 − f'²) = 0 the same flow has F''(0) = 0.003519061429; Barlow √2 normalisation 0.007379632. No printed value matches a conversion.
- Rounding of β does not explain the values (dα/dβ ≈ 68 near the fold; 0.0052182 → 0.005229 needs Δβ ≈ 1.6e-7).
- Scaled route: K = 2500/497, true A = √K f''(0) = 0.0117033858090; window in A (0.011703188702, 0.011703412983). Slow chain at 0.011703189 is 3e-10 above the floor and 2.0e-7 below the true A; overshoot chain at 0.0117034 is 1.4e-8 above the true A.

## 2. Independent computation
**f''(0) = 0.00521818788(4)**, 11 significant digits stable; 0.0052181 < f''(0) < 0.0052182 with margins 8.8e-8 and 1.2e-8.
- Method A: `scipy.integrate.solve_bvp` on [0, L] with the asymptotic tail imposed at L (f''(L) = (1 − f'(L)) D_{ν+1}(x)/D_ν(x), x = f(L)): 0.0052181878839 for L = 8…14 at tol 1e-12.
- Method B: DOP853 (rtol 1e-13) + Brent on the tail-matching residual: 0.0052181878840 at η∞ = 8, 9, 10.
- Scripts: `scripts/bvp_collocation.py`, `scripts/truncation_and_crosscheck.py` (no mpmath installed; double precision).
- **Truncation study (plain f'(L) = 1):** L = 6.5: 0.0063414; 7.0: 0.0053537; 7.5: 0.0052298; 8: 0.0052190; 9: 0.0052182. L reproducing each printed value: 0.005221 → 7.77, 0.005222 → 7.71, 0.005225 → 7.60, 0.005226 → 7.58, 0.005229 → 7.51 (with f''(L) = 0 instead: 8.54, 8.49, 8.39, 8.37, 8.31). Zhu–Cheng–Wu report their free boundary at 7.51; f'(7.51) = 1 gives 0.0052292 — their printed 0.005229 is reproduced exactly as a truncation error. Exception: their ref. [32] lists η∞ = 6.68 (naive truncation there gives 0.00577), not investigated.

## 3. Prior art
| Source | Printed at β = −0.1988 | True (rounded) | Agrees | How read |
|---|---|---|---|---|
| Fazio, arXiv:1212.5057v1 p. 16 | 0.005221; −0.005158 (reverse) | 0.005218; −0.005157 | no; no | typeset (0828Z crop, re-viewed) |
| Asaithambi, JCAM 176 (2005), via Asaithambi Fluids 6 (2021) 153 Table 2 | 0.005225 | 0.005218 | no | WebFetch summary (UNVERIFIED) |
| Zhang & Chen, AMC 210 (2009), same table | 0.005222 | 0.005218 | no | summary (UNVERIFIED) |
| Salama, Numer. Heat Transf. B 45 (2004), same table | 0.005226 | 0.005218 | no | summary (UNVERIFIED) |
| Zhu, Cheng & Wu (2009 preprint) Table 5 | 0.005229 | 0.005218 | no | summary (UNVERIFIED) |
| Guo, Zhuang, Meng & Rabczuk, arXiv:2010.05682 Table 8 | **0.005218** (η∞ = 11.999793) | 0.005218 | **yes** | two WebFetch summaries of arxiv.org/pdf (UNVERIFIED) |
| Barlow et al., arXiv:1907.09912 | no f''(0) at −0.1988; separation (−0.198837735, 0, −2.359) | — | β* to 9 digits | summary (UNVERIFIED) |
| Forbrich, AIAA J. 20 (1982), via a bibliography | β* "−0.1988377" | — | yes | secondary summary (UNVERIFIED) |

Guo et al. row (summary): "1 | -0.1988 | 0.005218 | 11.999793 | 1.77E-41 | 0.00522 | 0.00522 | 0.00559 | 0.00509 | 0.00513"; their β = −0.1 entry 0.319270 agrees with the checked window 0.3192697598–0.3192697599.
Not read: Hartree 1937, Smith 1954 (beyond a bibliography remark), Cebeci–Bradshaw, Cebeci–Keller, Rosenhead, Asaithambi 2004, the Zhang–Chen and Salama originals, White, Schlichting. From memory (UNVERIFIED): classical tables go from β ≈ −0.19 to separation without a −0.1988 row.
Rigorous enclosure in print: none found (one targeted search). "The 4th digit is wrong in print" is not published as a claim; the correct 0.005218 appears in Guo et al. next to the older values without comment.

## Process notes (main session)
- The referee tried `curl` on the Zhu preprint PDF (not arXiv) for a typeset reading of content it had read through WebFetch; the environment's classifier refused it and it was not worked around. Briefs already forbid re-fetching with curl; this case (curl for a typeset copy of a summarised non-arXiv page) is now named explicitly in the PROMPT note.
