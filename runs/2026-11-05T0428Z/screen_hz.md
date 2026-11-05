# Screen: H(z) table + printed claim candidates (run 2026-11-05T0428Z)

**Recommendation:** use **Moresco et al. 2016 (arXiv:1601.01701v2, JCAP 05 (2016) 014), Table 4 + Table 5, the oΛCDM row.**
- The printed AICc = 21.41 and BIC = 25.71 cannot both be right. By Eqs. 5.3 and 5.4, AICc − BIC depends only on (k, N), and no k from 1 to 6 with N = 30 or 31 reproduces the printed difference.
- Our fit gives χ²_min = 14.96704. The printed AICc implies χ² = 14.52 and the printed BIC implies χ² = 15.41 (k = 3, N = 31). Both are off by more than 0.44 in opposite directions.
- The same internal inconsistency appears in all three rows of Table 5.
- The transcription itself is validated: it reproduces the paper's z_t = 0.64 (+0.11/−0.07) and the linear-fit AICc = 32.42.

Downloads, text dumps and renders are in /tmp/claude-0/screen0428/, outside the repository. Scripts:
- `scripts/screen_moresco16.py`: table, the three fits, and z_t posteriors.
- `scripts/screen_moresco16_margins.py`: Newton minimiser, Hessian and level sets.
- `scripts/screen_moresco16_exact.py`: exact-rational line fit and the (k, N) arithmetic.
- `scripts/screen_farooq17.py`.

Crops of Tables 4 and 5, read and verified against the 200-dpi render, are in `typeset/moresco16_table4.png` and `typeset/moresco16_table5.png`.

No erratum was found; a web search for "Moresco 2016 … erratum" returns only the paper and its repository copies. Note that mpmath is not installed here, so all numbers are float64. The Newton minimiser converges to about 1e-9 in F.

## Candidates examined

| # | Paper | Table | Rows | Diagonal? | Reproducible from print alone? | Outcome |
|---|---|---|---|---|---|---|
| A | Moresco et al. 2016, 1601.01701v2 | Tab. 4 (PDF p. 18, printed p. 16), Tab. 5 (PDF p. 20) | 30 CC + H0 prior | yes | **yes** | **Mismatch in Table 5 (AICc/BIC)**; z_t reproduced |
| B | Farooq, Madiyar, Crandall & Ratra 2017, 1607.03537v? (ApJ 835, 26) | Tab. 1 (p. 2), 38 rows; Tab. 3 (p. 8) | 38 | no: uses Blake 2012 and Alam 2016 3×3 blocks, not printed | **no** | best fit about right, χ²_min off by 0.15 to 1.5 depending on the assumed covariance |
| C | Yu, Ratra & Wang 2018, 1711.03437 | Tab. 1 (p. 4), 36 rows; Alam covariance printed (Eq. 1) | 36 | 31 CC rows diagonal | n/a | all claims (H0, z_da, Table 2) come from a Gaussian process, so they are not a closed-form statistic and are unsuitable |

### A. Moresco et al. 2016 (arXiv:1601.01701v2, 2 May 2016)

**Table 4** ("H(z) measurements … used for the cosmological analysis"): 30 cosmic-chronometer rows with diagonal σ, BC03 values. The pdftotext output was checked against the rendered PNG, and all 30 rows match.
- **Printed typo:** row 15 has z = **0.44497**. The same paper's Table 1 (line 591 of the text dump) and Table 1 of Farooq et al. 2017 both give 0.4497.
- Effect of the typo: χ²_min shifts by −0.017 (oΛCDM), −0.028 (piecewise) and +0.005 (line). It changes none of the conclusions below.
- The frozen statement should use the table **as printed**, with 0.44497.

**Statistic (Sec. 5.2).**
- χ² = Σᵢ (H_mod(zᵢ) − Hᵢ)²/σᵢ² + (H0 − 73)²/2.4².
- The Gaussian prior is "H0 = 73 ± 2.4 km/s/Mpc" (p. 15; Table 5 caption: "all constraints assume a gaussian prior on the Hubble constant H0 = 73 ± 2.4").
- oΛCDM (Eq. 5.1): H = H0 [Ωm(1+z)³ + Ωk(1+z)² + ΩΛ]^{1/2}, with Ωk = 1 − Ωm − ΩΛ. This can be rewritten as E² = (1+z)²(1 + Ωm z − ΩΛ) + ΩΛ, which is linear in (Ωm, ΩΛ).
- Priors (p. 15): "uniform priors Ωm ∈ [0, 1] and zt ∈ [0, 1.5]", with z_t = (2ΩΛ/Ωm)^{1/3} − 1 (Eq. 5.2).
- Information criteria: "AIC = −2 ln Lmax + 2k, BIC = −2 ln Lmax + k ln N" (Eq. 5.3), and "AICc = AIC + 2k(k+1)/(N−k−1)" (Eq. 5.4).
- The piecewise and linear fits use f = H/(1+z) on "31 H(z)/(1+z) measurements", which are the 30 CC rows plus H0 = 73 ± 2.4 at z = 0.

**Printed claims.**
- p. 15: "We obtained zt = 0.64+0.11−0.07". Table 5 prints 0.64+0.1−0.06.
- Table 5:

  | model | result | AICc | BIC |
  |---|---|---|---|
  | oΛCDM | zt = 0.64+0.1−0.06 | 21.41 | 25.71 |
  | piecewise linear fit | zt = 0.4 ± 0.1 | 23.99 | 28.72 |
  | linear fit | – | 32.42 | 35.29 |

- p. 18: "the model preferred by the data is the oΛCDM … a straight-line is strongly disfavored".

**Reproduction.** For the profile over H0 there is a closed form, F(Ωm, ΩΛ) = γ − β²/α, with
- α = 1/2.4² + Σ E²/σ²
- β = 73/2.4² + Σ E·H/σ²
- γ = 73²/2.4² + Σ H²/σ²

Results:

| Model | Fit | χ²_min | AICc (N = 31) | BIC (N = 31) |
|---|---|---|---|---|
| oΛCDM, minimum over (H0, Ωm, ΩΛ) | Ωm* = 0.4361732, ΩΛ* = 0.9814386, H0* = 72.28651, z_t* = 0.650991. The global unconstrained minimum is the same point and lies inside the prior wedge. | **14.9670382** | 21.856 [N = 30: 21.890] | 25.269 [N = 30: 25.171] |
| Piecewise, continuous broken line a + b₁·min(z − z_t, 0) + b₂·max(z − z_t, 0), k = 4 | z_t* = 0.30643 | 14.0898 | 23.63 | 27.83 |
| Straight line f = a + bz, k = 2 | a = 67.13281, b = −4.585920 (exact rational) | **27.9712060** | 32.400 [N = 30: **32.416**, which matches 32.42] | 34.839 [N = 30: 34.774] |

Printed BICs for comparison: 25.71 (oΛCDM), 28.72 (piecewise), 35.29 (line).

How the oΛCDM z_t compares with the paper:
- Profile Δχ² < 1 gives z_t ∈ [0.574, 0.773], i.e. 0.651 +0.12 −0.08. The paper's 0.64 +0.11 −0.07 is **reproduced** to within the 0.01 rounding.
- The marginal posterior over (Ωm, z_t), uniform on the prior box, has mode 0.627 and 68% interval [0.577, 0.818].
- The 3σ text claim is "0.41 < zt < 2.2". Profile Δχ² < 9 gives a lower end of 0.443; the upper end is cut by the z_t ≤ 1.5 prior, so the paper evidently widened the prior for that claim. This is a soft mismatch.

The piecewise z_t = 0.4 ± 0.1 is roughly reproduced:
- The profile 68% interval is [0.22, 0.49] around a best fit of 0.31.
- The 95% claim "0.2 < zt < 0.8" is **not** reproduced. The profile Δχ² < 4 interval reaches down to z_t → 0. The paper's parameterisation of the broken line may differ (it is not specified exactly), so this is a soft finding only.

**MISMATCH 1 (rigorous, data-independent).** For every model, AICc − BIC = 2k + 2k(k+1)/(N−k−1) − k ln N.

| Row | k | Required (N = 31) | Required (N = 30) | Printed |
|---|---|---|---|---|
| oΛCDM | 3 | −3.413 | −3.281 | **−4.30** |
| piecewise | 4 | −4.198 | −4.005 | **−4.73** |
| line | 2 | −2.439 | −2.358 | **−2.87** |

Each printed value has a rounding tolerance of ±0.01.
- An integer search over k = 1 to 6 and N = 10 to 80 finds only (3, 39), (4, 34) and (2 or 4, 37 or 25) respectively. That is a different N for each row, and never 30 or 31.
- So no single χ² is consistent with both printed numbers in any row.

**MISMATCH 2 (fit-dependent).**
- For oΛCDM, the printed AICc implies χ²_min = 14.521 (N = 31) or 14.487 (N = 30), and the printed BIC implies 15.408 or 15.506.
- The certified target is 14.9670, which is 0.45 above the first and 0.44 below the second.
- For the line, the AICc agrees (32.42 with N = 30) but the BIC is 0.45 to 0.52 too high.
- For the piecewise fit, AICc = 23.99 is 0.36 high and BIC = 28.72 is 0.89 high. This row is softer, because the exact piecewise form is not pinned down.

**Qualitative conclusions survive.**
- ΔAICc(line − oΛCDM) = 10.5 and ΔBIC = 9.6, against printed 11.0 and 9.6. Both are above 5, so the straight line is still "strongly disfavoured".
- The piecewise fit stays within 2.6 of oΛCDM.
- So this is a Table-5 numerics erratum. The paper's science stands.

**Is the new question already published?** I found no reproduction or erratum of Table 5. A certified oΛCDM χ²_min and minimiser box for this table, with z_t of the minimiser, is not in print; the paper quotes only marginal/profile z_t.

### B. Farooq et al. 2017 (arXiv:1607.03537)

**Table 1** has 38 rows: CC data, the Alam 2016 values 81.5/90.4/97.3 at z = 0.38/0.51/0.61, the Blake 2012 values at 0.44/0.6/0.73, and Lyα at 2.34/2.36. **Table 3** (p. 8) is the non-flat ΛCDM row.

The statistic is the FR13 normalised-prior marginal, F = γ − β²/α + ln(ασ_H²), with E² linear in (Ωm, ΩΛ). But the paper says (p. 9) it is "accounting for the non-diagonal correlation matrices of the Blake et al. (2012) and the Alam et al. (2016) measurements". Neither matrix is printed, and Blake 2012 gives its covariance only in (A, F, fσ8), not in H.

Results:

| Covariance | h prior | Best fit (Ωm, ΩΛ) | χ²_min | Printed |
|---|---|---|---|---|
| Diagonal | 0.68 ± 0.028 | (0.2280, 0.5862) | 22.548 | (0.23, 0.60), 22.4 |
| Diagonal | 0.7324 ± 0.0174 | (0.2567, 0.7898) | 24.900 | (0.25, 0.78), 24.2 |
| Alam correlations (Yu+18 Eq. 1 pattern) | 0.68 | — | 22.765 | 22.4 |
| Alam correlations | 0.7324 | — | 25.721 | 24.2 |
| Alam plus a guessed Blake r = 0.4 | 0.68 | — | 22.04 | 22.4 |
| Alam plus a guessed Blake r = 0.4 | 0.7324 | — | 25.14 | 24.2 |
| Unnormalised prior, diagonal | 0.68 / 0.7324 | — | 19.59 / 22.93 | 22.4 / 24.2 |

- The h = 0.7324 value of 24.2 is not reached by any variant I tried.
- The verdict is **not decisive**, because the paper does not contain the inputs needed to define the statistic.
- The z_da column of Table 3 is a 2-D posterior mean (Eq. 18), which would need certified 2-D integrals.
- Not recommended.

### C. Yu, Ratra & Wang 2018 (arXiv:1711.03437)

Table 1 has 36 rows. It is useful as a data source: 31 CC rows with diagonal errors, plus the Alam covariance printed in Eq. 1. But every numerical claim in the paper comes from GP reconstructions. Not suitable.

Other leads not pursued, since time was spent on A and B:
- Cao/Ryan/Khadka/Ratra papers: their H(z) results combine CC with BAO, and the BAO part has a covariance.
- Jesus et al. 2018 (1712.01075): polynomial or kinematic fits to 31 CC points.

These remain options if A is rejected.

## Proposed frozen statement (candidate A, oΛCDM row)

The data are Table 4 exactly as printed, in printed order (left column, then right column):

```python
MORESCO16_T4 = [  # (z, H [km/s/Mpc], sigma_H)
 (0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
 (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
 (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9),
 (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12),
 (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17),
 (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]
H0_PRIOR = (73, 2.4)   # Gaussian, enters chi2 as (H0-73)^2/2.4^2
```

**Statistic.**
- χ²(H0, Ωm, ΩΛ) = Σᵢ (H0·√E²(zᵢ) − Hᵢ)²/σᵢ² + (H0 − 73)²/2.4², with E²(z) = (1+z)²(1 + Ωm z − ΩΛ) + ΩΛ.
- Profile over H0 ∈ ℝ: F(Ωm, ΩΛ) = inf_{H0} χ² = γ − β²/α, with α, β, γ as above. This is exact, has no log term, and α > 0 always.
- Domain: D = {0 ≤ Ωm ≤ 1, 0 ≤ ΩΛ ≤ 2, E²(zᵢ) > 0 for all i}.
- Box values: the minimum over [0,1]×[0,2] is the same point. The minimum over ΩΛ ≥ 1.3 is 16.95. On the edges, F ≥ 22.19 at Ωm = 0, F ≥ 28.2 at Ωm = 1, and F ≥ 31.1 at ΩΛ = 0.
- The paper's prior wedge (z_t ≤ 1.5 allows ΩΛ up to 7.8 Ωm) was scanned on an 801×601 grid. Its minimum is the same point (14.96716 on the grid). About 28% of wedge cells have E² ≤ 0 at some zᵢ and must be excluded; the paper does not say how it treated them.
- Optional variant: state the result on the wedge with the positivity side condition.

Float values from `screen_moresco16_margins.py`:
- argmin: Ωm* = 0.4361732, ΩΛ* = 0.9814386
- F* = 14.9670382
- z_t(argmin) = 0.6509911, H0* = 72.286514
- Hessian of F at the minimum: [[526.98, −321.04], [−321.04, 231.37]], eigenvalues about 733 and 25.7. One direction is soft, along the Ωm–ΩΛ degeneracy.

Level sets (grid in Ωm and z_t):

| Level | Ωm range | z_t range |
|---|---|---|
| F ≤ F* + 0.01 | [0.4213, 0.4512] | [0.6425, 0.6600] |
| F ≤ F* + 0.05 | [0.4012, 0.4700] | [0.6325, 0.6725] |
| F ≤ F* + 0.10 | [0.3875, 0.4850] | [0.6250, 0.6800] |

**Suggested certified statements**, with the margins in brackets:
1. min_D F ∈ (14.96, 14.975). The margins are 0.007 below and 0.008 above. This interval excludes the AICc-implied values 14.49 and 14.52 and the BIC-implied values 15.41 and 15.51, each by more than 0.4.
2. Every minimiser of F on D has Ωm ∈ (0.40, 0.475) and z_t = (2ΩΛ/Ωm)^{1/3} − 1 ∈ (0.63, 0.675). The +0.05 level set fits inside, so a proof needs to enclose F to about 0.02. If the soft direction makes that costly, use the +0.1 box: Ωm ∈ (0.385, 0.49), z_t ∈ (0.62, 0.685).
3. Arithmetic corollary, cheap and needing only bounds on ln 30 and ln 31: for k = 3 and N ∈ {30, 31}, no real χ satisfies both |χ + 2k + 2k(k+1)/(N−k−1) − 21.41| ≤ 0.005 and |χ + k ln N − 25.71| ≤ 0.005. The analogous statements hold for the piecewise row (k = 4) and the line row (k = 2).
4. Optional, exact: the line-fit χ²_min is a rational number, 27.97120603518…, with a 71-digit denominator, computed in `screen_moresco16_exact.py`. With N = 31, its BIC is 34.839, not 35.29.

**Before freezing:**
- Recheck F* at 30 or more digits; mpmath was unavailable here.
- An independent referee should confirm the reading that the H0 prior enters −2 ln L_max as a χ² term, i.e. that H0 is fitted, not marginalised. Eq. 5.3 says "Lmax", so the profile is correct. Marginalising instead adds a positive term ln(α·2.4²) (not evaluated for this table), which shifts both implied χ² values but cannot fix the (k, N) inconsistency.
