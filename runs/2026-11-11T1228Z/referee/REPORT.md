# Referee report (run 2026-11-11T1228Z; Opus subagent; saved by the main session — the subagent's Write was refused by the harness)

**Verdict: STANDS-WITH-CORRECTIONS.** The three frozen statements of `lean/FalknerSkan/Neg1988Rev.lean` are true, not vacuous and correctly formalised. Independent f''(0) of the reversed branch = **−0.005157420177929** (two methods), inside (−0.00515743, −0.00515741) with margins 9.8e-9 (lower) and 1.02e-8 (upper). Corrections concern prose only:
- (a) **What (2) refutes.** −0.005158 *is* the wall shear of a solution of the plain boundary-value problem (f'(∞) = 1): that solution overshoots (f' − 1 peaks at 9.36e-9 near η ≈ 8.86, then returns to 1 from above, algebraic tail). The refutation must read "no solution with f' ≤ 1 (Stewartson's |f'| ≤ 1), hence not the exponentially decaying reversed solution", never "no solution". The docstring's sentence ("the wall shear of no solution with f' ≤ 1") has the right strength.
- (b) **Size.** The printed value is 5.80e-7 too negative (1.1e-4 relative): 0.58 units of the last printed digit; it misses correct rounding (−0.005157) by 0.08 of a unit.
- (c) **Wording.** "The reversed-flow solution" → "a reversed-flow solution in the decay class" (Lean proves existence in the window, not uniqueness; identifying it with Fazio's branch rests on Stewartson's "two acceptable solutions" and numerics).
- (d) **Prior art.** Ganapol (arXiv:1006.3888, typeset) has 11–12-digit reversed-flow tables to β = −0.19 (Table 7) and β = −0.198826 (Table 8); Fazio is the only source found printing a reversed value at β = −0.1988. Ganapol Table 5 prints the attached "-0.1988 5.218187884E-03" (pdftotext layout dump, not cropped) — an earlier correct attached value than Guo et al.

## 1. Attack on the statements
**(1) `fs_neg1988_reversed`.** Sign and literals right (β = −0.1988, exact rationals). |f'| ≤ 1 holds for the reversed solution (collocation L = 12, tol 1e-11; Taylor to η = 10): reversed region η ∈ (0, 0.0481), min f' = −6.653e-5 at η = 0.0240, f'' < 0 only on (0, 0.0240), f' < 1 everywhere checked (1 − f'(10) = 2.6e-14). Decay condition holds: f''/(1 − f') = 0.548, 1.898, 3.766, 5.717, 7.692 at η = 2, 4, 6, 8, 10, tracking x = η − δ (δ = 2.3851678294), the Gaussian tail D_{ν+1}(x)/D_ν(x) ~ x. The class matches Stewartson's selection criterion (abstract via WebFetch, UNVERIFIED: "when β < − 0·1988 there are no solutions satisfying |f′| ⩽ 1 for all η … 0>β> − 0·1988 there are two acceptable solutions, one with f″(0) < 0"). No junk values; nothing too strong.

**(2) `fs_neg1988_printed_reversed_overshoots`.** True: with f''(0) = −0.005158, f' first reaches 1 at η = 8.09605925 (40-digit Taylor bisection 8.09605924807; DOP853 event 8.09605928); peak f' − 1 = 9.3558e-9 at η ≈ 8.859; then f' → 1 from above as f' − 1 ≈ 1.9710e-8·(η − δ)^{2β}. Not vacuous (the trajectory exists on [0, 200]). Optional strengthening: hypotheses on [0, 9] only. Fair refutation of "the wall shear of either branch" (attached has f''(0) > 0; every solution of class (1) has p ≤ 1) without any uniqueness. It does not refute the plain problem with f'(∞) = 1 (continuum of algebraic-tail solutions: −0.005158 and −0.0051575 overshoot and come back, peaks 9.36e-9 and 1.26e-9; −0.005157 approaches 1 from below). Asymmetry: the same lemma would fail for the correctly rounded −0.005157; the refutation works because Fazio's last digit falls on the overshoot side. Proof-route note: the overshoot margin is ≈ 9.4e-9 in f' at scaled ξ ≈ 3.6–4.0; a direct certified chain needs f' enclosures better than 1e-8 there.

**(3) `fs_neg1988_two_decay`.** Not vacuous, not trivial; follows from (1) and run 1028Z's `fs_neg1988_exists_decay` (q > 0 ⇒ 0 ≤ p < 1). Shows the `hpos` hypothesis of `fs_neg_decay_equal` / `fs_neg1988_window` is necessary. Same shape as `fs_neg_tenth_two_decay`.

**Scaled route.** True A = −0.011567095601858; window in A (−0.011567117630863, −0.011567072774732). A_over = −0.011567117 ↦ f''(0) = −0.0051574297187 (2.8e-10 inside the lower edge, 2.14e-8 below the true value); A_slow = −0.011567073 ↦ −0.0051574101004 (1.0e-10 inside the upper edge, 2.26e-8 above). Classification consistent (−0.0051575 overshoots, −0.005157 approaches slowly).

## 2. Independent computation (scripts in `scripts/`)
**f''(0) = −0.005157420177929104149** (method B stable to 22 digits; method A agrees to 12–13).
- Method A (`rev_collocation.py`): scipy `solve_bvp` on [0, L] with the parabolic-cylinder Robin tail f''(L) = (1 − f'(L)) D_{ν+1}(x)/D_ν(x), x = f(L), ν = −1 − 2β; hand-made starting profiles, no shooting; all 12 converge to the reversed branch. L = 8–16, tol 1e-11: −0.00515742017805 … −0.00515742017812; 40 000-node mesh: −0.00515742017793 for every L. δ = 2.3851678294.
- Method B (`rev_taylor.py`): own mpmath Taylor integrator (order 36, h = 1/16), secant on the tail residual (no overshoot classification). L = 9–13: −0.00515742017792910414908; halving h: same 22 digits.
- Pipeline check (`cross_beta.py`): reproduces Ganapol −0.0713359060034 (β = −0.19), −0.133421237895 (−0.15), −0.0976920601346 (−0.18); Ganapol Table 8 at β = −0.198826: printed −0.00288367895808, computed −0.002883678960576; Barlow V, VI: −0.1429351943576, −0.065168585542904; −0.1405462129787 at β = −0.1 (inside the checked window of `fs_neg_tenth_reversed`).
- IVP at f''(0) = −0.005158 (`rev_taylor.py`, `rev_truncation.py`): as in (2); DOP853 rtol 1e-13: crossing 8.09605928, peak 9.3559e-9 at 8.8534.
- Truncation (`rev_truncation.py`): naive f'(η∞) = 1 reproduces −0.005158 at η∞ = 8.0960592 (rounding interval [7.987, 8.432]); f''(η∞) = 0: η∞ = 8.854 ([8.752, 9.166]). Fazio's ITM (starred variables, λ = |f''(0)|^{−1/3} ≈ 5.79): η∞ = 8.10 ↔ η*∞ ≈ 1.40; attached 0.005221 ↔ η*∞ ≈ 1.35; rounding intervals in η*∞ [1.343, 1.354] and [1.380, 1.457] are disjoint, so no single truncation reproduces both; Fazio states only IVP tolerances 1e-6 (pp. 16–17); cause not determined. `fazio_freeboundary_check.py`: f'' at the first crossing 2.6e-7 (attached 0.005221), 5.7e-8 (reversed −0.005158).

## 3. Prior art (reversed / lower branch near separation)
| Source | Printed | Agrees | How read |
|---|---|---|---|
| Fazio, arXiv:1212.5057v1 p. 16 | "when β = −0.1988 we get for the missing initial conditions the values 0.005221 and −0.005158, respectively" | no (true −0.0051574202, 0.0052181879) | typeset (0828Z crop) |
| Fazio, arXiv:1212.5057v1 Table 4 p. 30 | reverse flow β = −0.18: Stewartson −0.097, Asaithambi −0.097692, Auteri et al. −0.097692, ITM −0.097692; also β = −0.1, −0.15 (−0.140546, −0.133421); no −0.1988 row | yes | typeset (`typeset/fazio2012_p30_table4_reverse.png`) |
| Fazio, arXiv:2003.07971 | repeats "0.005221 and −0.005158" | no | pdftotext of arxiv.org/pdf (text only) |
| Ganapol, arXiv:1006.3888 Table 7 | reversed β = −0.01 … −0.19, 12 digits ("-1.90E-01 -7.13359060034E-02"); no −0.1988 | yes | typeset (`typeset/ganapol2010_p23_table7_reversed.png`) |
| Ganapol Table 8 (completing Cebeci–Keller) | "-1.98826E-01 -2.88367895808E-03", "-1.98837735E-01 -5.77014 E-06" | yes at −0.198826 (2.5e-13) | typeset (`typeset/ganapol2010_p24_table8_cebeci_keller.png`) |
| Ganapol Table 5 (forward) | "-0.1988 5.218187884E-03" | yes | pdftotext layout dump only |
| Belden … Barlow, arXiv:1907.09912 Fig. 2 caption | reversed V (−0.12, −0.1429351943576), VI (−0.02, −0.065168585542904); separation IV (−0.198837735, 0, −2.359) | yes | typeset (`typeset/barlow2019_p4_fig2_caption.png`) |
| Guo, Zhuang, Meng & Rabczuk, arXiv:2010.05682 Table 8 | attached "1 -0.1988 0.005218 11.999793 1.77E-41 0.00522 0.00522 0.00559 0.00509 0.00513"; no reversed values | attached yes | typeset (`typeset/guo2020_p33_table8.png`) — upgrades run 1028Z's UNVERIFIED row |
| Stewartson, PCPS 50 (1954) 454 | abstract: reversed solutions "tabulated"; criterion |f'| ≤ 1 | — | WebFetch abstract only (UNVERIFIED) |
| Cebeci & Keller JCP 7 (1971) | 3-digit reversed values near separation (per Ganapol) | — | not read |
| Libby & Liu 1967; Zhu–Cheng–Wu 2009; Asaithambi 1997/2004/2005; Oskam & Veldman 1982; Hastings 1972 | — | — | not read |

Rigorous enclosure of a reversed-flow Falkner–Skan wall shear in print: none found (two targeted searches). No source publishes that the printed reversed value at β = −0.1988 is wrong in its last digit.

## Process notes
- Scripts `rev_collocation.py`, `rev_taylor.py`, `rev_truncation.py`, `fazio_freeboundary_check.py`, `cross_beta.py`, all under `nice`, each < 9 min. Five crops ≤ 90 KB each in `typeset/`. PDFs and text dumps in the session scratchpad, outside the repository.
- PDFs fetched with curl from arxiv.org/pdf only (1212.5057v1, 2010.05682, 1907.09912, 2003.07971, 2011.07725, 2011.07723, 1006.3888, 2112.15267), none after a failed WebFetch. No git, lake or lean.
