VERDICT: STANDS-WITH-CORRECTIONS

# Referee report: `Work/Cosmography/B1L19.lean` (l19_sq_central, l19_sqg_central, l19_sq_box, l19_sqg_box)

Referee run 2026-11-04 (independent). The scripts are in `/tmp/referee_l19/scripts/` (margins.py, omega_large.py, box.py, more.py, taylor.py, twopct.py, twopct_fine.py, profile.py, omfail.py). Renders are in `/tmp/referee_l19/` (tab-4.png, eq8-3.png, sec32-3.png, fig2-3.png, p4-4.png), and papers in `/tmp/referee_l19/papers/`. I fixed my own numbers before I read `runs/2026-11-04T1228Z/`. After that I compared them with `scripts/s.py`, `box.py` and `second_reading_l19.md`, and they agree (§7).

Notation: x₃ = log₁₀(2√2) = 1.5 log₁₀2 and x₅ = 2.5 log₁₀2. z₃ = 1.828 and z₅ = 4.657. f(x) = 1 + a₂x + a₃x² + a₄x³, so the quartic is P = x·f. R_ex(Ω) = d_L(z₅)/d_L(z₃) and R_p = P(x₅)/P(x₃). Every theorem reduces to `5 log₁₀(R_ex/R_p) > c`, with c = 7/20, 3/10 or 0. This reduction is valid when d_L, H and P are positive at both sources; §2 shows that the hypotheses supply this.

## 1. Truth and margins

1.1 **R_ex is strictly decreasing in Ω.** I computed d_L by direct z-integration (mpmath quad at 30 digits) on a 1001-point grid of [0, 1].
- R_ex(0) = 5.0938363, R_ex(0.3) = 3.0823872 and R_ex(1) = 2.8591854.
- R_ex(1) agrees with the closed form for the Einstein–de Sitter model, 2(1−2^{−5/4})/(1−2^{−3/4}) = 2.85918538802.
- dR/dΩ is negative at every sampled point, ranging from −117.9 at Ω = 0 to −0.139 at Ω = 1.
- Analytic reason, valid for every Ω where the model reaches z₅, including Ω > 1: ∂_Ω ln(1/E) = −g(z)/2, where g = ((1+z)³−1)/E² is increasing in z. The weighted mean of g over [z₃, z₅] therefore exceeds its mean over [0, z₃], so the ratio of the far integral to the near integral decreases in Ω.
- The minimum over [0, 1] of every margin is therefore at Ω = 1.

1.2 **Central fits** (Table 2 central values; I checked them against my own 250-dpi render, tab-4.png):

| | P(x₃) | P(x₅) | R_p | min over Ω∈[0,1] of 5log₁₀(R_ex/R_p) | constant | slack |
|---|---|---|---|---|---|---|
| SNe+QSO | 1.3352 | 3.2057 | 2.4009306 | 0.37931 mag at Ω = 1 | 7/20 | 0.0293 mag |
| SNe+QSO+GRB | 1.3288 | 3.2818 | 2.4697054 | 0.31799 mag at Ω = 1 | 3/10 | 0.0180 mag |

- At Ω = 0.3 the margins are 0.543 and 0.481 mag; at Ω = 0 they are 1.633 and 1.572 mag.
- Both theorems are true.
- The constants could be raised to 0.379 and 0.318 at most.
- Rounding of the printed coefficients (±0.0005 each) moves the margin by at most 0.0002 mag (from the gradient of R_p).

1.3 **Box statements.**
- R_p(a₂, a₃, a₄) is a linear-fractional function. Its denominator is positive on the region (§2.3), so the function is quasi-linear there, and its supremum over the region {a₂ ≥ A₂, a₃ ≤ A₃, a₄ ≤ A₄, P₅ > 0} is attained either at the vertex or along a recession ray.
- The recession limits are (x₅/x₃)² = 25/9 = 2.7778 (along +a₂). The directions −a₃ and −a₄ lower the ratio.
- The supremum is therefore max(vertex, 2.7778):
  - SNe+QSO corner (2.906, 5.479, −1.794): R_p = 2.8212815, margin 5log₁₀(2.8591854/2.8212815) = **0.0290 mag**.
  - SNe+QSO+GRB corner (3.043, 4.480, −0.915): R_p = 2.8291128, margin **0.0230 mag**.
- Random sampling confirms the vertex value: 133,575 and 133,250 admissible points with P₅ > 0, and the largest sampled R_p was 2.8212566 and 2.8290864, both below the corner value.
- Gradient of R_p at the corners: (−0.0060, +0.113, +0.138) for SNe+QSO and (−0.0072, +0.115, +0.140) for SNe+QSO+GRB. The one-sided directions in the theorems are therefore the right ones.
- Both box theorems are true, with thin margins.

1.4 **How far the box ends can move** (one end at a time, the others held at the corner; root of R_p = R_ex(1)):

| | a₂ end | a₃ end | a₄ end |
|---|---|---|---|
| SNe+QSO | ≥ −0.46 (see note) | ≤ 5.822 (+0.34σ) | ≤ −1.517 (+0.14σ) |
| SNe+QSO+GRB | ≥ 0.42 | ≤ 4.747 (+0.29σ) | ≤ −0.700 (+0.13σ) |

- Note on the a₂ end: the positivity argument in §2.3 needs a₂ ≥ 0, so a₂ ≥ 0 is the safe limit. The a₂ end is almost irrelevant.
- If all three ends move together by a common multiple n of the printed one-sided σ, the statement fails at **n = 1.100** (SNe+QSO) and **n = 1.092** (SNe+QSO+GRB). The author's s.py gives 1.12 and 1.10 on a 0.02 step.

## 2. Hypotheses and junk values

2.1 **hH₀ is redundant.** Suppose hubble a t₀ ≤ 0. Then hH forces H ≤ 0 on [t₅, t₀], so a is non-increasing there, and z₅ = a(t₀)/a(t₅) − 1 ≤ 0. That contradicts hz₅ = 4√2 − 1 > 0. The hypothesis is harmless.

2.2 **Normalisation H.**
- Central theorems: H only has to be nonzero. For H < 0 both quartic distances are negative, and logb of the ratio takes |·|, which gives the same value.
- H = 0 makes logPolyDL4 = log10/0·(…) = 0, so both residuals are logb 0 = 0 and the conclusion 0 > 7/20 is false. hHp (or H ≠ 0) is needed.
- Box theorems: hHp is needed. With H < 0, hp₅ forces f(x₅) < 0. If f(x₃) < 0 as well, |P₅|/|P₃| can reach 4.63 > R_ex(1) (take a₃ → −∞), and the statement fails.

2.3 **Positivity at the nearer source is implied; no extra hypothesis is needed.**
- Assume a₂ ≥ 0, a₄ < 0 and f(x₅) > 0, and suppose f(x₃) ≤ 0.
- Then the cubic f, with f(0) = 1 and f → −∞, has three positive roots, or a double root at x₃ and a third root beyond x₅. In both cases a₂ = a₄·(Σ rᵢrⱼ) < 0, a contradiction.
- So hp₅ together with the box constraints gives P₃ > 0. Sampling agrees: 0 of about 266,000 admissible points had P₃ ≤ 0.
- No branch of the box statements reaches x/0 or the |·| behaviour of logb at the nearer source.

2.4 **hp₅ is needed.** Take a₂ = 2.906, a₄ = −1.794 and a₃ = −(x₅ + a₂x₅² + a₄x₅⁴)/x₅³ ≈ −4.277.
- Then P₅ = 0, the far residual is logb(d/0) = logb 0 = 0, and P₃ = (ln10/H)·0.576 > 0.
- For H large, 5log₁₀(d₃/P₃) > 0, so the conclusion fails for every Ω.
- If P₅ < 0 instead (a₃ very negative, so P₃ < 0 too), the |·| ratio tends to (5/3)³ = 4.63 > R_ex(1), and the statement fails at Ω = 1.

2.5 **Time ordering (h₅₃, h₃₀) is needed.** Without it, t₃ can lie outside [t₅, t₀], where a is unconstrained. lumDistFlat at t₃ is then arbitrary (negative if t₃ > t₀), and the statement fails.

2.6 **Ω ≤ 1 is needed for the box theorems and for the stated constants.** It is not needed for the strict central inequality.
- Flat models with Ω > 1 (Λ < 0) keep E > 0 for z ≥ 0, and R_ex keeps decreasing towards a limit as Ω → ∞: R_∞ = 2.5694318 (omega_large.py, with integrand 1/√((1+z)³−1)).
- The strict central inequality (c = 0) holds for every Ω ≥ 0, with margins of at least 0.147 mag (SNe+QSO) and 0.086 mag (SNe+QSO+GRB).
- The stated constants fail at Ω ≥ **1.344** (7/20) and Ω ≥ **1.193** (3/10).
- The box statements fail at Ω ≥ **1.339** (SNe+QSO) and Ω ≥ **1.256** (SNe+QSO+GRB).

2.7 **Ω ≥ 0 is not needed for truth.**
- On Ω ∈ [−0.00555, 0) the hypotheses can be satisfied and R_ex increases (5.22 at Ω = −0.001).
- For Ω < −1/((1+z₅)³−1) = −0.00555, the square root reaches zero before z₅, so z₅ cannot be reached and the hypotheses are unsatisfiable (vacuous).
- The hypothesis is presumably kept for the bridge lemma. It is harmless.

2.8 **Non-vacuity.** For every Ω ∈ [0, 1] exact solutions exist: a ∝ sinh^{2/3} for 0 < Ω < 1, e^{t} for Ω = 0, and t^{2/3} for Ω = 1. I found no hidden vacuity.

## 3. Fidelity

3.1 Each Lean statement says what its docstring says.
- `logPolyDL4` is Eq. (7) of v4 with c = 1. x = log₁₀(1+z) is `Real.logb 10`, and "log" in the paper is base 10, because ln(10) and log appear separately. The prefactor ln(10).
- k/H₀ is absorbed into 1/H. This is legitimate: L19 itself says H₀ is degenerate with k. The differences are independent of H and of any offset.
- The residual sign convention 5log₁₀(d_L/D_L) is stated explicitly.

3.2 The phrase "region contains the box of all three printed ±1σ ranges" is **correct for both samples**. I checked it against my render of Table 2:
- SNe+QSO: 3.075−0.169 = 2.906, 4.466+1.013 = 5.479, −3.716+1.922 = −1.794.
- SNe+QSO+GRB: 3.205−0.162 = 3.043, 3.564+0.916 = 4.480, −2.510+1.595 = −0.915.
- The phrase "the side that brings the ratio closer" is correct at the corner (gradient signs in 1.3).
- Caveat 1: Table 2 does not state its confidence level, and the central values are probably marginal medians (author's second reading §4). "1σ" is an inference.
- Caveat 2: a quartic built from marginal medians is not the posterior's best curve.

3.3 **Corrections to the module docstring:**
- (a) "SNe + GRBs … matched by Ω ≈ 0.34" should read Ω ≈ 0.354 (root of R_ex = 3.04409). The author's s.py evaluated R(1/3) = 3.058, not the root.
- (b) The title says the fits "are not the image of any flat ΛCDM model over the quasar range". This overstates three things:
  - It is a two-redshift shape statement about the *central curves* (and the marginal box).
  - It is proved only for Ω ∈ [0, 1]. It is true numerically for all Ω ≥ 0 for the central curves, but not for the box.
  - "Image" is not defined; the theorems never mention ΛCDM's own quartic fit.
  - Suggested title: "the central L19 fourth-order curves rise less between z = 1.83 and 4.66 than any flat ΛCDM distance with Ω ∈ [0, 1]".
- (c) "the statement needs none [covariance]": true of the statement, but the box must not be read as a 68% joint region (see 4.3).
- All other floating-point numbers in the docstring reproduce: 5.09, 2.859, 2.401, 2.470, 2.821, 2.829, 3.044.

## 4. Meaning for the dispute

4.1 **What it establishes.**
- The L19 central quartics, compared with the exact flat ΛCDM distance and not with the Taylor point of Eq. (8), have a z = 1.83 → 4.66 rise smaller than every flat ΛCDM with Ω ∈ [0, 1]. Numerically this extends to every Ω ≥ 0.
- The gap is by more than 0.38 and 0.32 mag, and no normalisation, k or offset can absorb it.
- So the headline "deviation" of the central fit is **not** a truncation artefact of the Taylor point, which was the Yang et al. 2020 / Banerjee et al. 2021 mechanism.
- Direction: the fitted curve, normalised at low z, is brighter than ΛCDM(0.3) at high z (−0.67 mag at z = 4.66 and −1.04 mag at z = 6.7 for SNe+QSO; profile.py). This agrees with L19 Fig. 2, my render fig2-3.png. It is equivalent to preferring Ω_M > 1, which matches Yang et al. 2020 ("no dark energy within 1σ") and Khadka & Ratra 2020 (Ω_m0 ≈ 0.5–0.6, driven by z ≈ 2–5).
- This is a certified, curve-level version of the known conclusion that the RL quasar Hubble diagram is not flat-ΛCDM-shaped. It confirms the critique's other branch: the tension is real for these data, but it sits in the data and not in the expansion.

4.2 **Where the effect lives.**
- The pair (z = 0.41, 1.83) is matched by flat ΛCDM at Ω ≈ 0.47 (SNe+QSO) and Ω ≈ 0.49 (SNe+QSO+GRB) (profile.py).
- The whole two-point inconsistency therefore comes from the 1.83 → 4.66 leg.
- L19 itself says the data tension "has a peak at z ≃ 3 … but seems to decrease at z > 3 where the data quality reduces". Yet the central quartic keeps diverging monotonically to z = 7.
- The z = 4.66 point thus reads the polynomial where the data are sparse and, by the authors' own statement, closest to ΛCDM. The margin there is partly the a₄ term's extrapolation behaviour, not the data's.
- A two-point comparison is a fair *necessary* test of whether a curve is ΛCDM-shaped. It is not a fair summary of a fit over the whole range, and it carries no weights or errors.
- Yang et al.'s own refit (a₂ = 3.22, a₃ = 2.65, a₄ = −1.32, central values "consistent within 1σ" of L19) gives R_p = 2.5304. That is 0.265 mag below Einstein–de Sitter but only 0.033 mag below the Ω → ∞ limit. The size of the effect depends on the fit details.

4.3 **What it does not establish.**
- (i) **Significance.**
  - The box theorems fail once all three one-sided ends move by 1.10σ (Ω = 1) or 1.73σ / 1.82σ (Ω = 0.3) (more.py).
  - The marginal ±1σ box contains only the Δχ² = 1 ellipsoid, about 20% joint probability for three Gaussian parameters. The 68% joint region projects to about 1.88σ per axis, which is beyond the 1.1σ failure point.
  - The positive result that does follow, for any covariance: R_p is a linearised functional, and its σ is at most Σ|gᵢ|σᵢ. So ΛCDM's ratio lies at least about 0.95σ (Ω = 1) or 1.4–1.5σ (Ω = 0.3) away in that derived quantity, under Gaussian and linear assumptions.
  - Nothing here reaches the claimed 4σ, and nothing contradicts it either: covariances are not printed.
- (ii) Data and standardisation are not tested:
  - quasar L_X–L_UV standardisation (Khadka & Ratra 2021, 2022: relation parameters depend on cosmology and redshift for the full compilation, especially the SDSS-4XMM subsample, which is about 2/3 of the QSOs);
  - selection or Eddington bias, intrinsic dispersion, the k cross-calibration between samples, GRB Amati calibration, and whether a quartic is adequate at all.
- (iii) **Curvature: the conclusion does not survive.**
  - Closed ΛCDM models reproduce the central ratio: (Ω_M, Ω_Λ) = (1, 1) gives R = 2.365 and (0.3, 1.2) gives 2.325, both below 2.401.
  - The minimum over [0,1]² is 2.365 at (1, 1) (more.py).
  - Even the box corners are matched by milder closed models: (1, 0.5) gives 2.653 and (0.5, 1) gives 2.555.
  - This agrees with Bargiacchi et al. 2022 (arXiv:2111.02420): SNe+QSO "show evidence of a closed space".
  - The statement is flat-specific, and the module text should say so.
- (iv) **Ω > 1:** see 2.6. The central strict statement survives every flat Ω ≥ 0. The box statements and the 7/20 and 3/10 constants do not survive past Ω of about 1.19–1.34.

## 5. Prior art

The search used WebSearch, with papers read as arxiv.org/pdf only.
- Yang, Banerjee & Ó Colgáin 2020 (arXiv:1911.01681):
  - Their Fig. 1 compares the fourth-order log polynomial with Eq.-(8)-type coefficients against exact flat ΛCDM over Ω_m. It shows > 1% deviations beyond z ≈ 2 for most Ω_m, and at Ω_m = 0.3 1% near z ≈ 4.3. This is prior art for item 6.
  - They also fit flat ΛCDM directly to the QSOs and find Ω_m within 1σ of 1: the QSOs are "irreconcilable" with flat ΛCDM. This is the statistical, model-fit counterpart of the present theorems.
- Banerjee et al. 2021 (arXiv:2009.04109): mock tests; the log polynomial is trustworthy only to z ≈ 1.5–2.
- Velten & Gomes 2020 (arXiv:1911.11848): Ω_m0 ≳ 0.4 drives the tension; QSOs cannot establish acceleration.
- Khadka & Ratra 2020, 2021, 2022 (arXiv:2004.09979, 2012.09291, 2107.07600): the Ω_m0 preference and the standardisability problems.
- Bargiacchi et al. 2021 (arXiv:2101.08278, A&A 649, A65): fit *ΛCDM mocks* with (orthogonalised) log polynomials, i.e. "ΛCDM's image". They report > 4σ tension for the Lusso et al. 2020 sample. This is the closest prior art for "fits inconsistent with ΛCDM's image", done statistically and at fixed Ω.
- Lusso et al. 2020 (arXiv:2008.08586) uses a fifth-order polynomial and a w₀w_a fit; I found no exact-curve comparison of the fitted polynomial there.
- I found no paper that evaluates the *fitted* L19 (or L20) curves against the exact ΛCDM distance uniformly in Ω, or that proves the fitted curves differ from every flat ΛCDM curve.
- What is new is modest: a certified, Ω-uniform, normalisation-free two-point shape statement. The qualitative conclusion is already in Yang et al. 2020, Khadka & Ratra 2020 and Bargiacchi et al. 2021. My search was not exhaustive.

## 6. Lusso et al. 2019, Sect. 3.2: "maximum difference below 2%"

6.1 I read the typeset page myself: v4 p. 3 (sec32-3.png, eq8-3.png). Eq. (8), including a₄ = ln³10·(−135/64 Ω³ + 18/4 Ω² − 47/16 Ω + 5/8), is exactly the fourth-order Taylor coefficient set of H₀d_L in u = ln(1+z). I verified this with a sympy series (taylor.py): the difference is 0 for all four coefficients.

6.2 **The sentence is false as a general claim.** Method: maximum of |quartic/exact − 1| for 0 < z ≤ 6.7, with the trapezoid rule on 67,001 points (twopct_fine.py), cross-checked with mpmath (twopct.py).
- At z ≤ 6.7 the claim holds only for **Ω_M ∈ [0.054, 0.074] ∪ [0.252, 0.267]**.
- At Ω_M = 0.3, the value used for L19's own comparison, the maximum is 4.5% at z = 6.7 (0.100 mag). On z ≤ 5.1 it is 2.16%.
- At 0.35 it is 8.1%; at 0.5, 15.2%; at 0.6, 16.0% (0.38 mag); at 1.0, 8.6%; at 0.1, 4.5%; at 0.2, 3.8% (at z = 4.2).
- On z ≤ 5.1 the windows widen to [0.054, 0.075] ∪ [0.252, 0.297].
- Over L19's plotted ΛCDM line Ω_M = 0.1–0.9 (Fig. 4), the expansion is off by up to 16%.
- For comparison, the cubic at Ω = 0.3 is off by 14.9% at z = 6.7.

## 7. Comparison with the author's material (read after my numbers were fixed)

- The author's s.py gives R_min = 2.859185388, corner ratios 2.82128 and 2.82911, central ratios 2.40093 and 2.46971, and s_max ≈ 1.12 / 1.10. All agree with mine.
- The second reading's Table 2 matches my render.
- The certificate plan in gen_l19.py proves R_ex ≥ 2.84 on [0, 1]. That suffices for all four theorems, but for l19_sqg_central the slack is only 2.84/2.4697 = 1.14995 against 10^{0.06} = 1.14815, about 0.0007 mag. The final step will need tight bounds on ln 10 and log₁₀ 2.
- R_ex ≥ 2.85 would give about 0.004 mag of slack.

## Memory note
I read the program context in `/areas/formalization-program.md` from the user's memory. Nothing in it changed this review.
