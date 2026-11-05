# Run 2026-11-05T0428Z (scheduled)

**THE RESULT:** part 1 (test suites for scientific claims; idle since 1628Z, five runs) moved: a published data table and its printed model-comparison numbers tested by Lean theorems — Moresco et al. 2016 (arXiv:1601.01701v2), Table 5's AICc/BIC — plus the part-5 Lane–Emden audit (near misses and mutants of the frozen statement proved false).

**What can a scientist now trust without checking it themselves, that they could not before?** That the information criteria printed in Moresco et al. 2016 Table 5 do not follow from the paper's own definitions and data: in every row the printed AICc and BIC cannot come from one maximum likelihood (for every N ≤ 31, Eq. 5.4 as printed), and the printed oΛCDM BIC 25.71 and linear BIC 35.29 lie above the BIC at an explicit fit (χ² < 14.975 and < 27.972 on the printed Table 4, every N ≤ 35). Proved in Lean (Work), exact arithmetic, standard axioms; blind restatement closed. And: the Lane–Emden n = 3 headline (PROVED in Checked by run 0228Z, CI 41968192006 every blocking step green) is sensitive — changing θ(0) by 10⁻⁸, or the exponent 3 to 1 or 5, makes it false (proved).

**Weakest unchecked step:** the reading that Table 5's −2 ln L_max is χ² with no additive constant. Under the referee's alternative (the "AICc" column is plain AIC with N = 31), the oΛCDM and linear rows become internally consistent, and all four of their numbers equal our minima plus one common 0.446 — unexplained. Claim 1 (AICc and BIC inconsistent under Eq. 5.4) and the piecewise row do not depend on it. No stated conclusion of the paper changes (line disfavoured by > 5 either way): a misprint-class result, parked as a finding candidate, not messaged.

**Kind of answer (PROMPT note 1228Z):** not in print — no erratum, no paper recomputes Table 5 (screen + referee search; the JCAP version was not reachable).

## Start
- 04:28Z: LOCK of run 0228Z (02:28Z, < 150 min) → auditor role (48.4): Lane–Emden near-miss audit in `runs/…/audit/`. Run 0228Z pushed its promotion and removed the LOCK at 04:30Z (71a343e); this run took the LOCK at 04:37Z (7ff892c).
- Local Lean: elan installer accepted, Mathlib cache. add_repo not exposed; pre-cloned detached HEAD (reset local main to origin/main).

## Work
1. **Lane–Emden audit** (`Work/Math/LaneEmdenNearMiss.lean`, against `Checked.Math.LaneEmden.laneEmden3_constants`): `near_miss_initial` (θ(0) = 1 − 10⁻⁸: the scaled existence witness Aθ(Aξ) has its first zero at ξ₁/A, outside the interval), `mutant_n5` ((1 + ξ²/3)^(−1/2), no zero), `mutant_n1` (sinc, zeros kπ). Not refutable: dropping continuity of θ' at 0 (it follows from the rest; the blind bridge derives it).
2. **Screen** (`screen_hz.md`): Moresco 2016 recommended (Farooq 2017 not reproducible from print: unprinted covariances; Yu 2018: GP only). Transcription reproduces the printed z_t = 0.64 and the linear AICc 32.42.
3. **Freeze** 13f0ee8 `Work/Data/Moresco16.lean`; **proof** same file + `Moresco16Certs.lean` (generator `scripts/gen_m16.py`: rational √-enclosures to 10⁻⁹ and per-term bounds, generic step `term_le`); statements byte-identical to the freeze (script check). Module doc: referee corrections added after the freeze (LEDGER).
4. **Audit**: blind restatement (Sonnet, `Work/Data/Moresco16Blind.lean`: N ∈ {30, 31} natural, any tolerance ε ≤ 1/10, z_t parameter, ((H − model)/σ)² form) **closed** in `Work/Data/Moresco16BlindClosed.lean`. Referee STANDS-WITH-CORRECTIONS (`referee_m16.md`: own 50-digit recomputation, χ²_min 14.9670381749 and 27.971206035; transcription row by row; the AIC reading above).

## Next
Lower bound over the whole prior region (χ²_min > 14.96: two-parameter certificates, `B1L19Curved` pattern) would certify that the printed AICc is also off under Eq. 5.4; promotion of `Moresco16` to Checked (m16Table PRINTED with machine second reading, `chiSqOL`/`chiSqLine` FORMULA; NV witnesses are the existentials themselves).
- Tools for the oΛCDM lower bound (part 1/2 bridge, next run): `Work/Data/Moresco16Lower.lean` (discriminant bound, tangent √ bound, box convexity, χ² as a quadratic in H₀) and the float feasibility script `runs/2026-11-05T0428Z/scripts/feas_m16_lower.py` (267 boxes for c = 14.6).
