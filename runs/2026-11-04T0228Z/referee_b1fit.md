VERDICT: STANDS-WITH-CORRECTIONS

The frozen statement `Work.Cosmography.B1Fit.fit_direction` is true for every Ω ∈ [0, 1], with margin 0.80 above the frozen 1/2. It is non-vacuous and says what its theorem docstring says. The corrections concern:
- two numerical claims in the module docstring that hold only for Ω ≳ 0.06–0.1, not on all of [0, 1];
- the framing sentence, which this theorem supports only in a "which side of a line" sense, not in a distance sense;
- a proof-precision warning: the statement is tight in the magnitude tolerance.

Referee: independent, 2026-11-04. Scripts are outside the repository in /tmp/referee_b1fit/scripts/ (core.py, fits.py, t1–t11.py). Copies of the author's scripts, run for comparison only after my numbers were fixed, are in /tmp/referee_b1fit/dl/. I used mpmath at 30 digits for the distances and the LP vertices, and scipy for the fits.

Notation:
- x_k = log₁₀(1+z_k) = (L/2)·(1, 3, 5), with L = log₁₀2.
- P(x) = x + a₂x² + a₃x³.
- D_k = H₀ d_L(z_k), from the bridge integral. I cross-checked it against a z-integral to 1e-15.
- f = (20/3)L·(a₃ − lusA3 Ω) − (a₂ − lusA2 Ω). The conclusion is f > 1/2.

## 1. Truth and margin

1. **Reduction.** H, H₀, ln 10 and c all drop out. Some c satisfies all three `hm` conditions exactly when the three residuals span at most 0.1 mag. Equivalently, for each pair, P_k/P_j ∈ [R_kj·10^(−0.02), R_kj·10^(+0.02)], where R_kj = D_k/D_j. With P > 0 these are six half-planes in (a₂, a₃). The feasible set is a bounded hexagon for every Ω on my grid. Minimising f over it is a 2-variable LP. I solved it by exact vertex enumeration, and cross-checked with scipy HiGHS (same minimiser).

2. **Result.** The statement is true on all of [0, 1].
   - Worst case: **min f = 1.3028 at Ω = 0.3123**. The margin above 1/2 is **0.803**; the frozen constant is 38% of the truth.
   - Other values: f_min = 23.33 at Ω = 0, 2.05 at Ω = 0.2, 1.31 at 0.3, 1.49 at 0.4, 1.88 at 0.5, 2.55 at 0.8 and 2.05 at Ω = 1.
   - Binding constraints at the minimiser:
     - Ω < 0.025: P₃/P₁ lower and P₅/P₁ lower.
     - 0.025–0.155: P₅/P₁ lower and P₅/P₃ lower.
     - Ω ≥ 0.155: P₃/P₁ upper and P₅/P₃ lower.

   The author's e-space LP (espace.py, rescaled) gives a worst ratio of 1.3030 at grid point Ω = 0.31. This agrees with my number.

3. **The tolerance margin is thin. This matters for the proof.** Write ε for the tolerance about c (frozen value 0.05).
   - The conclusion f > 1/2 fails as soon as ε > **0.0595 mag**. f > 0 fails as soon as ε > **0.0650 mag**.
   - At ε = 0.06, min f = 0.454.
   - In ratio terms, the six bounds may be loosened by only about **0.85% (multiplicative)** before 1/2 is lost. The author's sens.py agrees: at 0.5% loosening the worst value falls to 0.856 in f units, and at 1% to 0.384.

   So the certified enclosures of D₃/D₁, D₅/D₁ and D₅/D₃ must together lose less than about 0.85% in ratio, uniformly in Ω (each D to roughly 0.4%). The B1Truncation certificates were about 5% loose in magnitude terms (0.09 proved against 0.115 true). That was enough there, but much finer Riemann/tangent grids and Ω sub-intervals will be needed here. Lowering the constant from 1/2 to 0 would only buy ε up to 0.065.

4. **Junk branches.** For H ≠ 0, Lean's `logb` gives Δμ_k = 5log₁₀(D_k|H|/(ln10·|P_k|)) when P_k ≠ 0, and Δμ_k = 0 when P_k = 0 (since x/0 = 0 and logb 0 = 0). H = 0 makes every `logPolyDL3` equal 0. Any single `hp` rules that out. I enumerated all 26 sign patterns (+, −, 0) of (P₁, P₃, P₅) on a 51-point Ω grid.
   - **All negative, (−,−,−): empty for every Ω.** So with `hp₁`, `hp₃` and `hp₅`, H < 0 is impossible, and **`hHp` is not needed for truth.**
   - With `hHp` kept, `hp₃` alone suffices, and so does `hp₅` alone. Every pattern with P₃ > 0 or P₅ > 0 is either empty or has f ≥ 16 (except the true branch, (+,+,+)).
   - `hp₁` alone does not suffice. Pattern (+,−,−) reaches f = −20.5. The apex P₃ = P₅ = 0 gives f = 0.489 < 1/2 at Ω = 0.
   - Dropping all three `hp` (keeping `hHp`) makes the statement false.

   **CI point.** These redundancies are logical, not structural. The natural proof turns each `hm_k` into linear inequalities by cross-multiplying. That needs P_k > 0 for each k, which comes from `hp_k` and `hHp` (P_k = H·logPolyDL3_k/ln10). So every hypothesis is used. Risk arises only if the prover takes a shortcut, for example deriving P₁ > 0 from P₃, P₅ > 0, or avoiding the sign of H. **Advise the prover to obtain each P_k > 0 from its own `hp_k` and `hHp`.** No relock is needed.

5. **All three matching hypotheses are needed.** If any one of `hm₁`, `hm₃`, `hm₅` is dropped, the feasible set becomes an unbounded wedge, and f is unbounded below at Ω = 0.3 (and at Ω = 1).
   - Without `hm₁` the statement is false at 86 of 101 grid points. At Ω = 0 the minimum is already 0.489.
   - Without `hm₃` it is false at 98 of 101; without `hm₅`, at 101 of 101.

   The cosmology hypotheses (`hΩ₀`, `hΩ₁`, ordering `h₅₃`/`h₃₁`/`h₁₀`, `hpos`, `hdiff`, `hH₀`, `hH`, `hz_k`) are all consumed by `lumDistFlat_flatLCDM`. If t₅ > t₀, the Icc is empty, every hypothesis on a is vacuous, and the statement fails. So the ordering is genuinely needed.

## 2. Fidelity

1. **The Lean statement matches its theorem docstring.**
   - c is bound only in hypotheses (read: "for some offset c").
   - 1/20 is 0.05 mag about c, i.e. a 0.1 mag peak-to-peak spread.
   - The `5·logb 10` convention is correct, and the inequality is strict.
   - "Margin of 1/2 in a₂" is the correct reading.
   - Redshifts: `√2 − 1`, `2√2 − 1`, `4√2 − 1` give 1+z = 2^(1/2), 2^(3/2), 2^(5/2), so x = L/2, 3L/2, 5L/2. The slope (20/3)·log₁₀2 = 2.0069 is in the same log₁₀ units.
   - Units: `lusA2`/`lusA3` carry ln10 and ln²10, matching `logPolyDL3`'s ln10·(x + a₂x² + a₃x³). I checked at Ω = 1 (Einstein–de Sitter): H₀d_L = u + (3/4)u² + (7/24)u³ with u = ln(1+z), which reproduces lusA2(1) and lusA3(1). There is no ln/log₁₀ mismatch.

2. **Non-vacuity.** The exact three-point interpolant is always feasible (zero residual spread) and has P > 0:
   - Ω = 0: (a₂, a₃) = (−4.584, 14.446), P = (0.096, 0.847, 4.313);
   - Ω = 0.3: (1.622, 5.195), P = (0.205, 1.261, 3.886);
   - Ω = 1: (0.716, 3.376), P = (0.178, 0.908, 2.597).

   Global flat-ΛCDM scale factors exist for every Ω ∈ [0, 1] (e^t, sinh^(2/3), t^(2/3)). So the hypotheses are satisfiable for every Ω.

3. **Two docstring numbers are wrong on part of [0, 1].** Both are right on the four Ω values the author tried (0.1, 0.3, 0.6, 1.0).

   a. *"Least-squares fits over z ≤ 4.66 or 5.1 leave residuals within ±0.036 mag at these three redshifts for every Ω tried."* Free offset, z ≥ 0.01. Three-point residual half-ranges:

   | Ω | uniform z, ≤ 4.66 | uniform z, ≤ 5.1 | uniform ln(1+z), ≤ 5.1 | uniform z, ≤ 7 |
   |---|---|---|---|---|
   | 0 | **0.204** | **0.193** | **0.230** | **0.263** |
   | 0.02 | **0.081** | **0.088** | **0.091** | **0.108** |
   | 0.04 | 0.0497 | **0.0537** | **0.0545** | **0.0656** |
   | 0.06 | 0.035 | 0.038 | 0.039 | 0.047 |
   | 0.1–1 | ≤ 0.0264 | ≤ 0.0240 | ≤ 0.0305 | ≤ 0.0309 |

   So these fits satisfy the hypothesis only for Ω ≳ 0.045. The fraction 0.036 is printed by `lsfit.py` as `halfrange5`, which is over the **five** points 1+z = 2^(k/2), k = 1…5, not over the theorem's three. My three-point maxima over Ω ∈ [0.1, 1] are 0.026–0.031.

   b. *"The Taylor point's residual half-range at the three points is 0.11–0.23 mag."* Over [0, 1] it is **0.110–0.807**: 0.807 at Ω = 0, 0.526 at 0.02, 0.234 at 0.1. The quoted range holds for Ω ≥ 0.1.

   c. Minimax fits: no cubic agrees within ±0.05 mag over [0.01, 5.1] for Ω ≲ 0.055. Best half-ranges are 0.254 at Ω = 0, 0.107 at 0.02, 0.067 at 0.04 and 0.049 at 0.06. The docstring's sentence about minimax fits is logically correct but empty there.

   **Correction:** restrict both numerical remarks to Ω ≥ 0.1, or quote the full-range numbers. The theorem itself is unaffected. For Ω < 0.05 it is true but does not apply to range fits.

4. Minor: "spanning the RL19 quasar range z ≤ 5.1". The three points span 0.41–4.66. Nothing below z = 0.41 or between the points is constrained. The docstring already says the hypothesis is weaker than agreement on the whole range, so this is acceptable.

## 3. Scientific relevance and framing

1. **Side of the line.** I take the RL19 centre at (3.45, 1.6), one reading.
   - f_RL(Ω) = (20/3)L·(1.6 − lusA3) − (3.45 − lusA2) is **negative for every Ω ∈ [0, 1]**. Its maximum is **−1.214** (near Ω ≈ 0.8). Sample values: −9.20 at Ω = 0, −4.41 at 0.3, −1.62 at 1.
   - The author's espace.py gives the same 1.2135.
   - So the Taylor point (f = 0) always lies strictly between the RL19 centre (f ≤ −1.21) and every matching cubic (f > 1/2).

2. **What this certifies, and what it does not.**
   - It certifies a *direction* statement. Along the normal n = (−1, 2.007)/2.243, truncation moves ΛCDM's cubic image by at least 0.22 away from the side where the RL19 centre lies.
   - It does **not** certify a Euclidean "farther from RL19" statement. The theorem's half-plane guarantees only d(RL, fit) ≥ (0.5 + 1.214)/2.243 = **0.764**.
   - For Ω ≥ ~0.6 that is less than d(RL, Taylor). At Ω = 0.8 it is 0.766 against 1.380. At Ω = 1 it is 0.943 against 1.724.
   - At the curve level (RL19 test against the whole ΛCDM line), the Taylor curve comes within **1.091** of the RL19 centre (Ω = 0.58). The certified bound 0.764 does not exceed that.

   Numerically, the full feasible hexagon is farther than the Taylor point for every Ω. Its minimum over Ω is **1.764** (Ω = 0.7), against 1.091. That fact is not in the frozen statement.

3. **The "antiparallel" picture holds only at low Ω.** Cosine between the least-squares fit displacement (uniform z ≤ 5.1) and the RL19 offset from the Taylor point:

   | Ω range | cosine |
   |---|---|
   | 0–0.45 | −0.92 to −1.00 |
   | 0.6 | −0.69 |
   | 0.7–1 | −0.29 to −0.45 |

   The earlier report's −0.97 to −1.00 was for Ω = 0.3.

   The fits are still farther from the RL19 centre than the Taylor point is, for every Ω. The fitted ΛCDM curve's closest approach is 2.697, at Ω = 0.70.

4. **Realistic weightings.** The conclusion f > 1/2 held for every fit I tried, at every Ω ∈ [0, 1]. The 0.05 hypothesis did not always hold:

   | weighting (z ≥ 0.01, free offset) | 3-pt half-range at Ω = 0.3 | max over Ω | min f over Ω |
   |---|---|---|---|
   | quasar-like density (log-normal plus z ≈ 3 bump), z ≤ 5.1 | 0.027 | 0.187 (Ω = 0) | 3.16 |
   | 740 SNe (σ = 0.15, z ≤ 1.3) + 1598 QSOs (σ = 1.4) | **0.057** | 0.40 | 1.24 |
   | same, QSO σ = 0.7 | 0.049 | 0.33 | 1.73 |
   | SN + QSO + 160 GRBs (σ = 0.8, z ≤ 6.7) | 0.047 | 0.34 | 1.82 |
   | exp(−z) weight, z ≤ 5.1 | 0.043 | 0.30 | 2.04 |
   | SNe only, z ≤ 1.3 (cubic extrapolated) | **0.073** | 0.47 | **0.66** (Ω = 0.4) |

   So the theorem covers range-type fits for Ω ≳ 0.06. The SN-dominated joint fit that RL19's Fig. 3 most resembles sits **at the edge of the hypothesis** at Ω = 0.3 (0.047–0.057). The direction conclusion holds there numerically even where the hypothesis fails.

   This is a framing caveat. Do not write "every realistic fit of RL19 type is covered". Write "least-squares fits over the quasar range (uniform or quasar-like weights, Ω ≳ 0.06) are covered; SN-dominated joint fits are borderline."

5. **Would 0.1 mag break it? Confirmed, if "0.1 mag" means ±0.1 about c.**
   - At ±0.1, min f = **−3.97** (Ω = 0.28). The conclusion fails for Ω ∈ [0.12, 1].
   - Even the sign f > 0 is lost above ±0.065.
   - (If "0.1 mag" means peak-to-peak, it is the frozen statement.)

6. **Suggested wording for the sentence.** "Exact flat ΛCDM, seen through any cubic that matches it within 0.05 mag at z ≈ 0.41, 1.83 and 4.66, lies on the far side of a line through the Taylor point from the RL19 contour centre, for every Ω_M ∈ [0, 1]: truncation does not move ΛCDM's cubic image toward the RL19 contour."
   - Do not use "moves away from" as a distance claim without the numerical caveat in 3.2.
   - Credit Banerjee et al. 2021 for the displacement itself (§4).

## 4. Prior art

1. **Yang, Banerjee & Ó Colgáin 2020** (arXiv:1911.01681) and **Banerjee et al. 2021** (arXiv:2009.04109) show numerically, with mocks, that log-polynomial fits to flat ΛCDM miss the Taylor curve. The earlier report (0828Z §4) read the 2009.04109 Fig. 3 ellipses: they are displaced to smaller a₂ and larger a₃, the same direction as here. Neither paper compares that direction with the RL19 offset, and neither states a bound.
2. **Banerjee, Ó Colgáin, Sasaki & Sheikh-Jabbari 2021**, "Lost in the log-polynomial expansion" (arXiv:2102.02098). Mock cubic fits show "a glaring mismatch between the centre of the ellipses and the red segment". The paper gives no direction analysis and no comparison with the quasar best fit.
3. **Bargiacchi et al. 2021** (arXiv:2101.08278) uses orthogonalised log-polynomials. **Bargiacchi, Dainotti & Capozziello 2023** (arXiv:2307.15359) uses 4th/5th order. It reports offsets whose direction depends on the evolution treatment, and makes no truncation-direction analysis and no bound.
4. Lusso et al. 2020 (arXiv:2008.08586): the abstract mentions only generic systematics checks. My fetch of the full text was blocked, so I did not check its body.
5. **I found no analytic or certified statement of this direction result, and no Ω-uniform half-plane bound.** The phenomenon (mock fits displaced from the Taylor point) is prior art and must be credited. The certified half-plane, and its placement relative to the RL19 centre for all Ω ∈ [0, 1], appear new.

Sources (arXiv abs/pdf only):
- https://arxiv.org/pdf/2009.04109
- https://arxiv.org/pdf/1911.01681v2
- https://arxiv.org/pdf/2102.02098v1
- https://arxiv.org/pdf/2101.08278
- https://arxiv.org/pdf/2307.15359
- https://arxiv.org/abs/2008.08586v1
- https://arxiv.org/pdf/2212.04118

## 5. Requested corrections (summary)

1. Module docstring: restrict the "±0.036 mag" and "0.11–0.23 mag" remarks to Ω ≥ 0.1, or quote the full-range values (§2.3). Also label the author's 0.036 as a five-point figure.
2. Framing: the theorem certifies the side of a line, not a Euclidean or curve-level increase in distance from RL19 (§3.2). Add the SN-dominated borderline caveat (§3.4).
3. Proof plan: the D-ratio enclosures must lose less than about 0.85% in total, uniformly in Ω (§1.3). Obtain each P_k > 0 from its own `hp_k` and `hHp`, so that no hypothesis goes unused (§1.4).
4. Optional: the constant could be raised to 6/5 (true margin 1.303). I do not recommend it, given the certificate precision in item 3.
