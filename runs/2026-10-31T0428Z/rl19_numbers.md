# RL19 / Lusso+19 / Lusso+20: log-polynomial coefficients, ranges, tension method

Sources: arXiv PDFs only, downloaded to /tmp/rl_b1/ on 2026-10-31. Pages were rendered with pdftoppm and read as images; pdftotext was used only to find them.

| Paper | arXiv id / version read | PDF pages |
|---|---|---|
| RL19, Risaliti & Lusso, Nat. Astron. 3, 272 | 1811.02590**v1** (the only version; "re-submitted version in the authors' custom format") | 41 |
| L19, Lusso et al., A&A 628, L4 | 1907.07692**v4** (A&A proofs, ms 36223corr, 24 Jul 2019) | 5 |
| L20, Lusso et al., A&A 642, A150 | 2008.08586**v1** (only version; ms paper_sample_rev2) | 24 |

Page numbers below are PDF page numbers. For RL19 they equal the printed page numbers. For L19 and L20 they equal "Article number, page N".

Crops in `typeset/` (each ≤ 150 KB):
- `rl19_p9_fig3.png`
- `rl19_p15_methods_cosmological_fits.png`
- `rl19_p22_suppfig5.png`
- `lusso19_p3_eq7_8.png`
- `lusso19_p4_table2.png`

Not checked: the published journal versions (Nat. Astron. / A&A). Their figure numbering (for example "Extended Data Fig. 5") and any changed numbers are **UNVERIFIED**.

---

## 0. Coefficient convention (important)

The fitted function is D_L = ln(10)(c/H0)(x + a2 x² + a3 x³ [+ a4 x⁴ (+ a5 x⁵)]), with x = log10(1+z).
- RL19 p.15 (Methods, "Cosmological fits"): "D_L=ln(10)c/H0 (x +a2x²+a3x³), where x=log(1+z)".
- L19 p.3, Eq. (7): the same with "k ln(10) c/H0", up to a4.
- L20 p.13, Eq. (12): the same up to a5.

**The ΛCDM-implied coefficients in these log10 units** are given by L19 p.3, Eq. (8), as printed:
- a2 = ln(10) × (3/2 − 3/4 Ω_M)
- a3 = ln²(10) × (9/8 Ω_M² − 2Ω_M + 7/6)
- a4 = ln³(10) × (−135/64 Ω_M³ + 18/4 Ω_M² − 47/16 Ω_M + 5/8)

I checked these numerically by Taylor-fitting the flat-ΛCDM D_L in u = ln(1+z) (script /tmp/rl_b1_scripts/chk2.py). The bracketed factors match the u-coefficients to better than 1e-8 at Ω_M = 0.1, 0.3 and 0.5.

At Ω_M = 0.3 the values are **a2 = 2.93580, a3 = 3.54123, a4 = 1.12066** (computed by me, not printed).

**RL19 printed formulas (p.15, verified on the image) have two problems:**
1. They are written as "a2 = 3/2 − 3/4 Ω_M" and "a3 = 7/6 − 2Ω_M + 9/8 Ω_M". These are the *natural-log* (u = ln(1+z)) coefficients: the ln(10) and ln²(10) factors are missing.
2. The last term of a3 is missing its square. It should be 9/8 Ω_M².

RL19 also prints the ΛCDM curve as "a3 = 5/3 − 10/3 a2 + 2a2²". This is correct only in natural-log units. In the log10 units of Fig. 3 the curve is

  a3 = ln²10 · [5/3 − (10/3)(a2/ln10) + 2(a2/ln10)²].

RL19 Fig. 3 itself (p.9) is drawn in log10 units, as these checks show:
- The black dot ("value for Ω_M=0.3") sits at the dashed cross-hairs, about (2.93, 3.54), matching the log10-unit values above.
- The black curve has its minimum at about (1.92, 1.47). In log10 units the minimum is predicted at a2 = (5/6)ln10 = 1.919, a3 = (5/18)ln²10 = 1.473.

## 1. Best-fit a2, a3 (a4) and uncertainties

### RL19 (SNe JLA + quasars)
- **No numerical best-fit values or 1σ errors for a2, a3 are printed anywhere in the arXiv PDF.** I searched the text of all 41 pages and checked by eye: the only "±" values are γ, Ω_M and δ.
- Results are shown only as contours in **Fig. 3, p.9**. The caption says:
  - "The filled contours are obtained from the fit of the third order polynomial P[log(1+z)] of the combined quasar and supernove Hubble diagram."
  - "The empty contours are obtained from the same fit to the data at z<1.4. Contour levels are at 1, 2, and 3σ."
- Read off the image (approximate, **not printed**):
  - The filled 1σ region is centred near a2 ≈ 3.45, a3 ≈ 1.6. It spans about a2 ≈ 3.2–3.7, a3 ≈ 1.0–2.2.
  - The ellipse is strongly anti-correlated (long axis slope ≈ −3 to −4 in a3 per unit a2).
  - The outer edge of the filled 3σ (yellow) region comes close to the Ω_M = 0.3 dot.
  - The empty z<1.4 contours are centred near (2.95, 3.4) and enclose the black dot within 1σ.
- **No correlation coefficient or ellipse parameters are printed.**
- No quasars-only fit is reported.
- a4: p.15 says "Adding a fourth order does not improve the fit, and the coefficient a4 is poorly constrained." No value is given.

### L19 (Pantheon + quasars ± GRBs): **Table 2, p.4, right column**, "Cosmographic results using the logarithmic polynomial function." Verified on the image (crop `typeset/lusso19_p4_table2.png`):

| sample | a2 | a3 | a4 |
|---|---|---|---|
| SNe, quasars, GRBs | 3.205 (+0.165 / −0.162) | 3.564 (+0.916 / −0.938) | −2.510 (+1.595 / −1.536) |
| SNe, quasars | 3.075 (+0.172 / −0.169) | 4.466 (+1.013 / −1.040) | −3.716 (+1.922 / −1.852) |
| SNe, GRBs | 3.304 (+0.186 / −0.183) | 2.069 (+1.1217 / −1.252) | 2.571 (+2.631 / −2.506) |

Notes on Table 2:
- "+1.1217" is printed with four decimals.
- These are fourth-order fits (free k per sample, plus a2, a3, a4).
- The table does not say whether the central values are medians or modes. Sect. 3.2 calls them "best-fit parameters and their uncertainties ... obtained through ... emcee". The ±1σ meaning is implied by the format but not stated in the caption.
- **No covariance or correlation coefficients are printed.**
- Fig. 4 (p.5) shows only 3D point clouds: "1σ (dark colours) and 4σ (light colours) error contours" for Pantheon+quasars and Pantheon+quasars+GRBs, and 1σ and 2σ for Pantheon+GRBs.

Observation (my arithmetic): measured against the Ω_M = 0.3 point (2.936, 3.541, 1.121), the *marginal* offsets for SNe+quasars are only about 0.8σ (a2), 0.9σ (a3) and 2.6σ (a4). The claimed ~4σ therefore depends on the parameter correlations, and the paper does not print them. **A theorem cannot reproduce "4σ" from Table 2 alone.**

L19 standard cosmography (not log-polynomial): **Table 1, p.3**, q0 / j0 / s0:

| | q0 | j0 | s0 |
|---|---|---|---|
| Best fit | −0.802 | 3.02 | 5.9 |
| Mean | −0.8 | 3.04 | 5.6 |
| 2σ | (−0.95, −0.66) | (2.15, 4.4) | (3.7, 9.8) |

### L20 (Pantheon + 2,421 quasars)
- The fit is a **fifth-order** log polynomial (p.13, Eq. 12): "where k, a2, a3, a4 and a5 are free parameters".
- **No values of a2–a5 are printed anywhere in the PDF** (text searched, p.13–14 checked by eye).
- The only plot of the result is the red curve in Fig. 9 (p.13).
- p.14 defers details: "More details on our cosmographic technique will be provided in a companion publication (Bargiacchi et al., in preparation)."
- γ is marginalised in this fit; it was fixed in earlier works (p.13).

## 2. Redshift ranges and where the deviation appears

### RL19
- Quasar range, p.11 (Methods first line): "1,598 quasars, covering the redshift range z=0.036-5.100, and showing a 4-σ deviation from the standard ΛCDM model at z>1.5". p.3 says "0.04<z<5.1".
- SN cross-calibration range: "z=0.1-1.4" (p.4, p.15).
- p.4 says the quasar Hubble diagram "show a significant deviation from the extrapolation of the ΛCDM model in the poorly explored redshift range z>1.4".
- p.16 says "~4σ tension" and "precise estimate of the expansion of the Universe at z>2".
- No GRBs are used.

### L19
- Quasars: "1598 sources in the redshift range 0.04 < z < 5.1" (p.2).
- Pantheon: "1048 objects in the range 0.01 < z < 2.26" (p.2). JLA maximum is "z ≃ 1.3".
- GRBs: "162 GRBs ranging from 0.03 < z < 6.67 ... excluding the two highest redshift objects at z = 8.1 and z = 9.3" (p.2).
- Where the deviation appears:
  - "deviation from the ΛCDM model emerging at high redshifts (z > 1.4)" (p.1, Intro, quoting RL19).
  - "becomes increasingly statistically significant at redshifts higher than 1" (p.4, Fig. 5 discussion).
  - "tension ... has a peak at z ≃ 3 ... seems to decrease at z > 3" (p.4).

### L20
- Quasars: "0.009 ≤ z ≤ 7.52", 2,421 quasars (p.12); "0.009 < z < 7.52" (p.3, parent sample).
- Fit uses Pantheon SNe (no GRBs).
- The "best" sample in Sect. 8 removes photometric-UV quasars at z < 0.7.
- Where the deviation appears:
  - Abstract (p.1): "well reproduced by the standard flat ΛCDM model up to z ∼ 1.5–2, but strong deviations emerge at higher redshifts".
  - p.14: "up to z ∼ 1.5 ... a statistically significant deviation emerges at higher redshifts".
  - p.16: "starts to be important for z > 2".
  - p.19: "at z > 1.5".

## 3. How the tension is computed

### RL19
- **Fit:** Methods p.15:
  - "H0 is fixed to 70 km/s/Mpc in our cosmographic fit"
  - "DM=m+5[log(D_L/Mpc)+5], where m, a2, and a3 are the free parameters. The parameter m depends on the deviation of H0 from the chosen reference value"
  - Main text p.4: k and a1 "are set to be equal to ln(10)c/H0 and 1".

  So the **normalisation is free**, through the offset m. The quasar normalisation β is set by cross-matching with JLA over z = 0.1–1.4 (p.4, p.15). The arXiv text does not say whether β is fitted jointly or fixed beforehand.
- **Test:**
  - p.4: "The comparison between the values of a2 and a3 obtained from the fit and this relation [the a2–a3 curve implied by flat ΛCDM] represent a model-independent, cosmographic test ... discrepancy ... statistically significant at the 4σ level."
  - Fig. 3 caption, p.9: "it is in tension with the whole data set at a statistical significance of 99.98%, corresponding to ~4σ".
- **Reference:** the comparison is against the **whole ΛCDM curve** (a2(Ω_M), a3(Ω_M)). Ω_M = 0.3 is only marked as a dot. RL19 does not fix Ω_M for the tension number.
- **Not stated:** the exact statistic is not given. The text does not say whether it is the 2D contour level of the curve's closest approach, a Δχ², or the Mahalanobis distance. The figures 99.98% and ~4σ are the only numbers.
- **Side note (my arithmetic):** 99.98% two-sided Gaussian is about 3.7σ. For a 2-dof χ² it corresponds to Δχ² ≈ 17.0, about 3.7σ-equivalent. The paper rounds this to "~4σ".

### L19
- **Fit:**
  - Normalisation k is free and "fitted separately for SNe Ia, quasars, and GRBs in order to cross-calibrate the samples".
  - H0 is fixed to 70, being "degenerate with the k parameter" (p.3).
  - Free parameters are k (per sample), a2, a3, a4, sampled with emcee.
- **Test:**
  - Eq. (8) "describe a curve in the (a2, a3, a4) parameter space that we can directly compare with the results of the MCMC" (p.3).
  - Fig. 4 caption, p.5: "The black solid line represents a flat ΛCDM model with Ω_M in the interval 0.1–0.9, where the black point marks the value Ω_M = 0.3".
  - p.4: "it is apparent that the tension of our cosmographic fit with the standard model is at 4σ for Pantheon+quasars, and remains significant even with the inclusion of the GRBs".
  - Abstract (p.1): "∼4σ with SNe Ia and quasars, at ∼2σ with SNe Ia and GRBs, and at > 4σ with the whole SNe Ia+quasars+GRB data set".

  The significance is therefore judged **visually**: does the ΛCDM curve lie outside the plotted 4σ (or 2σ) contour in 3D? No formula is given.
- **Separate test:** the standard cosmography gives "j0 = 1 (i.e. ΛCDM) is off at > 4σ" (Fig. 3 caption, p.3).

### L20
- No a_i-space tension number.
- **Fit:** k is a "rigid shift of the quasar Hubble diagram to match the one of supernovae" and is free. H0 is fixed to 70 (p.13).
- **Test:** p.14, via a w0waCDM fit to SNe + "best" quasars: "the ΛCDM model (recovered for values w0 = −1 and wa = 0) is in tension with our data at more than 3σ, in agreement with RL19." p.23 (App. C) repeats "more than 3σ".
- The ~4σ is only quoted from earlier work (p.2: "a deviation from ΛCDM emerges at higher redshift, with a statistical significance of about 4σ").

## 4. RL19 "Extended Data Fig. 5" (log expansion vs ΛCDM)

**Which figure.** In the arXiv PDF the figure is **Supplementary Figure 5, p.22**. Methods p.15 calls it "Extended Figure 5" ("we show, as an example, the ratio between the distance-redshift relation obtained from a ΛCDM model with Ω_Λ=0.7, Ω_M=0.3, and the polynomial expansions in z and log(1+z)").

The numbering in the arXiv text is internally inconsistent:
- p.15 also says "constrains of the a2 and a3 parameters ... as shown in Extended Figure 5" and "The blue curve in the Extended Figure 5". Those describe the a2–a3 plot, which is main-text Fig. 3, whose curve is black.
- Main text p.4 cites "Supplementary Figure 2" for the faster convergence. But Supp. Fig. 2 (p.20) is luminosity versus redshift.
- L19 p.3 cites it as "their Supplementary Figure 5".

Mapping to the published "Extended Data Fig. 5" is **UNVERIFIED**.

**Caption (p.22):** "Ratio between the luminosity distance – redshift relation in a flat ΛCDM model and its approximation with a third order expansion in log(1+z) (red continuous line) and a fourth order polynomial expansion (blue dashed line)... the logarithmic expansion is a reasonable approximation of the theoretical values up to high redshift, while the standard polynomial expansion can be used up to z~0.8."

The caption does not say whether the coefficients are ΛCDM-implied or fitted. Methods p.15 ("ratio between ... a ΛCDM model with Ω_Λ=0.7, Ω_M=0.3, and the polynomial expansions") points to the **ΛCDM-implied (Taylor) coefficients at Ω_M = 0.3**.

**Numerical check (mine, /tmp/rl_b1_scripts/chk.py).** The plotted curves match the Ω_M = 0.3 Taylor polynomials to plotting accuracy, as **P/D_L** (the axis labels say "D_L/P_3[log(1+z)]" and "D_L/P_4(z)"):

| z | P3_log/D_L (Taylor) | plot (red) | P4_z/D_L (Taylor) | plot (blue) |
|---|---|---|---|---|
| 1.4 | 0.9836 | ≈0.983 (inset) | 0.9409 | ≈0.94 (inset edge) |
| 3 | 0.9461 | ≈0.95 | 0.5536 | ≈0.55 |
| ~4.2 | 0.914 | ≈0.91 | 0.03 (zero crossing ≈4.2) | crosses 0 ≈4.2 |
| 5.9 | 0.8701 | ≈0.87 | −0.971 | ≈ −0.98 |

- The inverse ratio D_L/P3 rises to 1.15 at z = 6 and does not match the plot. The labels are therefore inverted relative to what is drawn: the plot shows P/D_L.
- A fitted-like log polynomial (for example a2 = 3.4, a3 = 1.6) gives about 0.73 at z = 5.9, so the fitted coefficients are clearly excluded.
- **Conclusion:** the figure shows the polynomial with the ΛCDM-implied coefficients (Ω_M = 0.3), not a fitted one. This is my inference: the numbers match, but the caption does not say so.

Related quantitative claims, with my Taylor values for comparison:
- RL19 says the third-order log expansion is accurate to "a few per cent". My Taylor value is a 13% deficit at z = 6 (about 5.4% at z = 3).
- L19 p.3 says the fourth-order expansion matches "with a maximum difference below 2%" up to z ~ 6.7. **My Taylor computation disagrees:** P4_log/D_L = 0.980 at z = 5 and 0.955 at z = 6.7, so the deviation exceeds 2% above z ≈ 5.
