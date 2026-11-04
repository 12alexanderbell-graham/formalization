# Second reading: Lusso et al. 2019, A&A 628, L4, arXiv:1907.07692

Blind second reading, transcribed from PNG renders of the arXiv PDFs. Pages were rendered at 200 dpi, and Table 2 again at 400 dpi.
Sources: https://arxiv.org/pdf/1907.07692v1, v2, v3, v4. v5 returns 404, so there are 4 versions.
MD5 of the PDFs: v1 49645c68..., v2 8eec9e83..., v3 401f5574..., v4 d03b1f17...
All versions are 5 pages long. Eq. (7) and Eq. (8) are on p.3 (left column, Sect. 3.2), and Table 2 is on p.4 (top of the right column).
Crops: `typeset/l19_table2_second.png` (v4, 200 dpi) and `typeset/l19_eq7_second.png` (Eq. 7 and Eq. 8 from v1 and from v4, stacked).

## 1. Eq. (7)

v1 and v2 (the lead-in reads "we define a cosmographic function of the **distance modulus** as:"):

    log[D_L(z)] = k ln(10) (c/H_0) × [log(1+z) + a_2 log^2(1+z) +
                  + a_3 log^3(1+z) + a_4 log^4(1+z)] + O[log^5(1+z)],      (7)

v3 and v4 (the lead-in reads "we define a cosmographic function of the **luminosity distance** as:"):

    D_L(z) = k ln(10) (c/H_0) × [log(1+z) + a_2 log^2(1+z) +
             + a_3 log^3(1+z) + a_4 log^4(1+z)] + O[log^5(1+z)],           (7)

- Normalisation factor: `k ln(10) c/H_0`, where `ln` is the natural log of 10.
- Variable: `log(1+z)`. The paper writes `log` and `ln` separately, so `log` here is the base-10 log, and that is why the factor ln(10) appears. The paper never states the base in words.
- The text after Eq. (7) says: "where k, a2, a3, and a4 are free parameters. The parameter k is fitted separately for SNe Ia, quasars, and GRBs in order to cross-calibrate the samples ... H0 is degenerate with the k parameter, so we can fix it to an arbitrary value (H0 = 70 km s^-1 Mpc^-1)."

## 2. Eq. (8)

v1, v2 and v3 (no ln(10) factors; the image crops are pixel-identical):

    a_2 = 3/2 - (3/4) Ω_M
    a_3 = (9/8) Ω_M^2 - 2 Ω_M + 7/6
    a_4 = -(135/64) Ω_M^3 + (18/4) Ω_M^2 - (47/16) Ω_M + 5/8.

v4 (with ln(10) factors):

    a_2 = ln(10)   × (3/2 - (3/4) Ω_M)
    a_3 = ln^2(10) × ((9/8) Ω_M^2 - 2 Ω_M + 7/6)
    a_4 = ln^3(10) × (-(135/64) Ω_M^3 + (18/4) Ω_M^2 - (47/16) Ω_M + 5/8).

The fraction in the Ω_M^2 term of a_4 is printed as "18/4" (not reduced) in every version.

## 3. Table 2: "Cosmographic results using the logarithmic polynomial function."

Columns: sample | a2 | a3 | a4. Each entry is a central value followed by +upper and −lower uncertainties.

| sample | a2 | a3 | a4 |
|---|---|---|---|
| SNe, quasars, GRBs | 3.205 +0.165 −0.162 | 3.564 +0.916 −0.938 | −2.510 +1.595 −1.536 |
| SNe, quasars | 3.075 +0.172 −0.169 | 4.466 +1.013 −1.040 | −3.716 +1.922 −1.852 |
| SNe, GRBs | 3.304 +0.186 −0.183 | 2.069 +1.1217 −1.252 | 2.571 +2.631 −2.506 |

Notes:
- In the SNe, GRBs row, the a3 upper uncertainty is printed with four decimals: **+1.1217**. This is the only entry with four decimals, and it looks like a typo for 1.217 or 1.122.
- The SNe, GRBs a4 value is **positive**: 2.571. The other two a4 values are negative.
- Table 2 is **pixel-identical** in v1, v2, v3 and v4 (I compared 400 dpi crops with PIL ImageChops.difference, and the bounding box was None for every pair).

## 4. What the central values and uncertainties are

- The Table 2 caption does not say whether the central values are medians or best fits, and does not give the confidence level of the uncertainties.
- Sect. 3.2, after Eq. 7 (v4): "The best-fit parameters and their uncertainties were obtained through the Python package emcee ... affine invariant Markov chain Monte Carlo (MCMC) ensemble sampler." v1 has "The best fit parameters and their uncertainties have been obtained ...".
- Sect. 4.1, which describes the MCMC procedure in the context of the standard cosmography fit: "We finally extracted the constraints on cosmographic parameters by coadding the thinned chains and inferred the median values and the confidence ranges from the marginalisation [v1: marginalization] of the posterior probability distributions of the parameters." The paper does not say whether this recipe also applies to Table 2.
- Sect. 4.2: "A summary of the results obtained from the MCMC regression analysis of the fourth order is provided in Table 2." Fig. 4 shows 1σ and 4σ contours (1σ and 2σ for Pantheon+GRBs).
- The confidence level of the Table 2 uncertainties (1σ / 68%) is **not stated**. The best reading is marginal posterior medians with asymmetric confidence ranges, but that is an inference.

## 5. Differences between versions

- Eq. (7), left-hand side: `log[D_L(z)]` in v1 and v2, `D_L(z)` in v3 and v4. The lead-in changes to match, from "distance modulus" (v1, v2) to "luminosity distance" (v3, v4).
- Eq. (8): no ln(10) prefactors in v1, v2 and v3. v4 multiplies a2, a3 and a4 by ln(10), ln^2(10) and ln^3(10).
- Table 2: identical in all four versions.
- The other changes are editorial: language edits (e.g. "we fit" in v1 becomes "we fitted" in v2 and later), "§" becomes "Sect.", hyphenation, and the manuscript label (v1 "qsogrbsn", v4 "36223corr").

## Consistency check: Eq. (8) at Ω_M = 0.3 (Python)

| form | a2 | a3 | a4 |
|---|---|---|---|
| v1–v3 Eq. (8) (no ln10) | 1.275 | 0.667917 | 0.091797 |
| v4 Eq. (8) (with ln10) | 2.935796 | 3.541226 | 1.120663 |

Only the v4 (ln10-scaled) form is on the same scale as the Table 2 values (a2 ≈ 3.1–3.3, a3 ≈ 2–4.5). This means the v1–v3 Eq. (8), which has no ln(10) factors, does not match the coefficients in the published table. For example, a2 = 1.275 is far from 3.2.

Compared with the v4 ΛCDM point, the full-sample a2 is (3.205 − 2.936)/0.162 ≈ +1.7σ, a3 is (3.564 − 3.541)/0.938 ≈ 0.02σ, and a4 is (−2.510 − 1.121)/1.595 ≈ −2.3σ. These are one-dimensional marginal comparisons only. The paper's 4σ claim comes from the 3D contours.
