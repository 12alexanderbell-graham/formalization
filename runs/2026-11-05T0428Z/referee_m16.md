# Referee report: Work/Data/Moresco16.lean (Moresco et al. 2016, arXiv:1601.01701v2, Table 5)

**VERDICT: STANDS-WITH-CORRECTIONS.**
- All five frozen statements are true, and their numerical margins are real.
- Corrections are needed in the module doc and docstrings. They overstate what claim 1 shows, and they justify "−2 ln L_max = χ²" with a reading that the paper's own N contradicts.
- None of the corrections changes the Lean statements.

Source: arXiv PDF v2, fetched with `curl` from arxiv.org/pdf into the scratchpad outside the repository.
- Pages read: PDF pp. 16–20 (printed pp. 14–18), via pdftotext.
- Renders: 200-dpi PNGs of PDF p. 18 (Table 4, Fig. 7) and p. 20 (Table 5, Eqs. 5.3–5.4), read visually.

Scripts, all in `runs/2026-11-05T0428Z/scripts/`. They are independent of the screen scripts: the table was re-typed from the render, and mpmath runs at 30–50 digits.
- `referee_m16.py`: fits.
- `referee_m16_variants.py`: reading search.
- `referee_m16_witness.py`: exact or 50-digit checks of short decimal witnesses.

## 1. Independent derivation

**oΛCDM, χ² with prior (H0−73)²/2.4², profiled over H0.**
- The profile is exact: F = γ − β²/α. The gradient root was found with mpmath findroot at 40 digits, and the full 3-parameter χ² was re-evaluated at the root and agrees.
- Best fit: Ωm* = 0.436173190, ΩΛ* = 0.981438580, H0* = 72.2865137.
- χ²_min = **14.96703817488452**.
- z_t* = 0.6509910 and 2ΩΛ/Ωm = 4.5002, which is inside [1, 15.625].
- min E²(zᵢ) at the optimum is 1.038.
- A float grid over the whole prior wedge (Ωm ∈ (0,1], z_t ∈ [0,1.5], E² > 0) finds no lower basin: its minimum is 14.9674, at (0.435, 0.6525).
- The optimum is interior, so the prior region does not bind. A wider z_t range gives the same minimum.

**Line f = a + bz on 31 points** (Table 4 as H/(1+z) with σ_H/(1+z), plus 73 ± 2.4 at z = 0), exact rational:
- a = 67.13281392, b = −4.58591957.
- χ²_min = **27.971206035183**.

**Piecewise row** (soft: the paper does not pin down the form). Continuous broken line with amplitude, two slopes and z_t, so k = 4, on the 31 points:
- χ²_min = 14.0898 at z_t = 0.3065.
- Without the H0 point: 13.673.

**Frozen numbers and their margins:**

| Statement | Bound | Value | Margin |
|---|---|---|---|
| `oL_bic_exceeds` χ² clause | 14.975 | 14.96704 | 0.0080 |
| `oL_bic_exceeds` at the worst N = 35 | 25.705 | 14.96704 + 3 ln 35 = 25.6331 | 0.072 |
| `line_bic_exceeds` χ² clause | 27.972 | 27.97121 | 0.00079 |
| `line_bic_exceeds` at the worst N = 35 | 35.285 | 27.97121 + 2 ln 35 = 35.0819 | 0.203 |

- The line χ² margin is small, but the value is an exact rational, so the margin is real.
- Short witnesses work and were checked exactly:
  - `line_bic_exceeds`: (a, b) = (67.13, −4.586) gives χ² = 27.9712114 < 27.972, checked in exact rationals.
  - `oL_bic_exceeds`: (H0, Ωm, ΩΛ) = (72.29, 0.436, 0.981) gives χ² = 14.9670744, evaluated at 50 digits with mpmath (the χ² has square roots, so it is not exact), and lies in the wedge.

**Claim 1, arithmetic, for every real N in (k+1, 31].**
- Let h(N) = 2k + 2k(k+1)/(N−k−1) − k ln N.
- h′(N) = −2k(k+1)/(N−k−1)² − k/N < 0, so h is strictly decreasing and its minimum on the range is h(31). A dense check of 2·10⁵ points agrees.
- Under the hypothesis, c + k ln N − BIC_printed lies within 0.005 of (AICc − BIC)_printed − h(N). The theorem therefore needs h(31) − (AICc − BIC)_printed > 0.01.

| Row | k | h(31) | printed AICc − BIC | Margin beyond 0.01 |
|---|---|---|---|---|
| oΛCDM | 3 | −3.41307 | −4.30 | 0.877 |
| piecewise | 4 | −4.19749 | −4.73 | 0.523 |
| line | 2 | −2.43940 | −2.87 | 0.421 |

- All three are true with large margins.
- Since the AICc penalty decreases in N and k ln N increases, the claim also holds with **independent** N_A, N_B ≤ 31 at the same margin. This is a free strengthening if wanted.
- With Eq. 5.4 and one (k, N < 200), the only reconciling values are:
  - oΛCDM: (3, 39)
  - piecewise: (4, 34) and (2, 85)
  - line: (2, 37), (4, 25) and (1, 134–135)
- None of these is plausible.

## 2. Fidelity

**Junk values and quantifiers: no exploitable issue.**
- Claim 1: N > k+1, so the division and the log are safe. c is universally quantified over ℝ. The tolerance (closed ≤ 0.005 in the hypothesis, strict > 0.005 in the conclusion) is right for 2-decimal rounding.
- `chiSqOL`: √ is guarded by ∀i, 0 < E²(zᵢ). H0 is unrestricted, which is correct because the prior is Gaussian.
- `chiSqLine`: 1+z > 0 and σ > 0, so it is safe.
- The existentials cannot be met by junk, because the true minimum is far below every alternative.

**Definitions match the paper.**
- Eq. 5.1 with Ωk = 1 − Ωm − ΩΛ.
- The prior term (H0−73)²/2.4²: p. 15, and the Table 5 caption ("all constraints assume a gaussian prior on … H0 = 73 ± 2.4").
- "31 H(z)/(1+z) measurements": p. 15, "Combining them with literature data as presented in Tab. 4 and adopting the most recent local distance ladder measurement of H0". That is 30 + H0 at z = 0, so the extra term in `chiSqLine` is right.
- σ_f = σ_H/(1+z) is not stated, but it is the only error propagation consistent with the print. Not dividing gives χ² = 11.91, which is nowhere near any printed number.

**Prior region.** z_t ∈ [0, 1.5] ⟺ (1+z_t)³ = 2ΩΛ/Ωm ∈ [1, 15.625], since 2.5³ = 15.625. The encoding Ωm ≤ 2ΩΛ ≤ 15.625·Ωm with 0 ≤ Ωm ≤ 1 is correct.
- Nit: the encoding admits Ωm = ΩΛ = 0, where z_t is undefined. This is harmless for an existential: F ≥ 22 on Ωm = 0.
- Note: Fig. 7 (left) plots z_t up to 2.5, and the text quotes a 3σ range 0.41 < z_t < 2.2, so the paper's effective z_t range was probably wider than 1.5. This is irrelevant, because the minimum is interior.

**The k values are the paper's.**
- oΛCDM: H0, Ωm, z_t, so k = 3.
- Piecewise: "transition redshift … together with the slope of the two lines and the overall amplitude", so k = 4.
- Line: k = 2.

**CORRECTION A (main finding): there is a reading under which two rows are internally consistent.**
- Read the column headed "AICc" as **plain AIC**, i.e. without the 2k(k+1)/(N−k−1) term of Eq. 5.4.
- Then AIC − BIC = 2k − k ln N, and with N = 31 (the paper's own count):

| Row | 2k − k ln 31 | printed AICc − BIC | Implied c (AICc col / BIC col) |
|---|---|---|---|
| oΛCDM, k = 3 | −4.3018 | −4.30 | 15.410 / 15.408 |
| line, k = 2 | −2.8679 | −2.87 | 28.420 / 28.422 |

- Both rows are consistent within rounding.
- The piecewise row stays inconsistent under every variant tried with one k and one N (k = 1–6, N = 28–32). The formulas tried were AICc(5.4), AIC, AICc with N−k or N−k+1, and BIC with ln N, log₁₀ N or ln(N/2π).
- Claim 1 is still a true theorem, because it is about Eq. 5.4 as printed. But the module doc's gloss, "So in each row the two printed criteria are not values for one and the same maximum likelihood", is **not** established for the oΛCDM and line rows without the premise "the AICc column is Eq. 5.4's AICc".
- Replace the gloss with: *"Under Eqs. 5.3–5.4 as printed (k as stated, any N ≤ 31), no single −2 ln L_max gives both printed numbers in any row. The oΛCDM and linear rows are consistent if the 'AICc' column is plain AIC with N = 31; the piecewise row is consistent under no reading found."*
- So the defect is best described as "the printed AICc values do not satisfy Eq. 5.4 (they match AIC)", plus the χ² offset in Correction C.

**CORRECTION B: the justification "(when −2 ln L is χ², as the linear row's AICc indicates)" is weak.**
- The line row's AICc matches χ²_min + 4 + 12/(N−3) only for **N = 30**: 32.4157. With the paper's N = 31 it gives 32.3998, which is off by 0.020, outside rounding.
- Under the AIC reading of Correction A, the same AICc is off by 0.449.
- Better justification for −2 ln L = χ² (no additive constant):
  - The Gaussian normalisation Σ ln 2πσ² would add 227.5 to the oΛCDM row and 199.5 to the line row, and the printed values plainly lack it.
  - Eq. 5.3 says "L_max", so a maximised likelihood is meant, not a marginal.
- Reword the module doc accordingly. The conditional nature of claims 2 and 3 should stay explicit.

**C. Claims 2 and 3 (BIC exceeds the BIC of the fit) are robust.**
- With c = our χ²_min, no penalty k ln N with k ≤ 6 and N ≤ 100 reproduces 25.71: it would need N = 35.9 at k = 3.
- Other natural variants all fail to reach the implied c = 15.41:
  - H0 fixed at 73: 15.076
  - prior counted twice: 15.016
  - H0 prior 73.8 ± 2.4: 15.186; 73.24 ± 1.74: 15.080
  - typo z = 0.4497 instead of 0.44497: 14.950
  - χ² at the posterior-mean (Ωm, z_t) = (0.386, 0.702): 15.264
- Two variants overshoot:
  - Analytic marginalisation over H0: F + ln(α·2.4²) = 16.10.
  - −2 ln(prior-averaged L over the box): 21.48.
- The line prior variants (73.8, 73.24, …) move the line χ² by 1.7 to 4.8, so they cannot give a common fix.
- Curiosity, not explained: under the AIC reading, all four oΛCDM and line numbers are reproduced by one common additive offset δ ∈ [0.4458, 0.4460] on top of our χ²_min. That would be "the paper's −2 ln L_max was χ²_min + 0.446 in both fits", for example a non-converged minimiser or slightly different inputs. It is not a normalisation constant, because those differ by 28 between the rows.
- The theorems' conclusions hold under the stated premise −2 ln L_max = χ²_min.

**Is the conclusion valid only if −2 ln L_max = χ²_min?**
- Yes. The docstrings say so; keep it explicit.
- If the authors' −2 ln L included any constant ≥ 0.45, the BIC clauses would say nothing about the paper. None of the natural constants (normalisation 199–228, H0 marginal +1.13) is close to 0.45.

**Is any reading of the whole of Table 5 consistent?** No.
- Best partial readings:
  - (i) Eq. 5.4 with N = 30 reproduces exactly one number, the line AICc.
  - (ii) The AIC reading with N = 31 makes the oΛCDM and line rows internally consistent, but each is 0.44–0.45 above our fit.
- No reading reproduces both numbers of any row from our χ²_min.
- For the piecewise row, from our χ²_min the AICc column needs N = 26 and the BIC column needs an exotic k ln(N/2π) with k = 6, N = 72.

## 3. Transcription

- `m16Table` was compared with the 200-dpi render of PDF p. 18 and with `typeset/moresco16_table4.png`.
- All 30 rows match in z, H and σ, in order (left column, then right column). This includes 0.44497 / 92.8 / 12.9, which is a printed typo for Table 3's 0.4497, correctly flagged and kept as printed.
- "69.0" in row 1 versus "69" in row 2 is immaterial.
- Table 5 (render p. 20 and `typeset/moresco16_table5.png`) reads 21.41 / 25.71, 23.99 / 28.72, 32.42 / 35.29. These are the constants in the three theorems.
- k values: 3, 4 and 2 in the Lean file, as in the paper.
- The z_t cell reads 0.64 +0.1 −0.06, against 0.64 +0.11 −0.07 in the text. This is cosmetic and not used.

## 4. Prior art

- **arXiv:** the abs page lists only v1 (7 Jan 2016) and v2 (2 May 2016). No v3, and no erratum note.
- **Accepted manuscript:** the St Andrews repository copy is itself titled "arXiv:1601.01701v2 … Prepared for submission to JCAP", so it is the v2 text.
- **JCAP version:** the iopscience page could not be read, because the fetch permission request went unanswered. The publisher version and any corrigendum remain **unchecked**; this needs a human check.
- **Web searches:**
  - The six printed values with "Moresco": none found.
  - "erratum" / "corrigendum" with the title or DOI: none found.
  - AICc/BIC recomputation: none found.
- No paper was found that notes the inconsistency or recomputes these criteria.

**Corrected values** (Eq. 5.4, N = 31, k as stated, c = χ²_min; piecewise per our broken-line form):

| Row | AICc printed → corrected | BIC printed → corrected |
|---|---|---|
| oΛCDM | 21.41 → **21.86** | 25.71 → **25.27** |
| piecewise | 23.99 → 23.63 | 28.72 → 27.83 |
| line | 32.42 → **32.40** | 35.29 → **34.84** |

- ΔAICc (line − oΛCDM) = 10.54 and ΔBIC = 9.57, against printed 11.01 and 9.58. Both are > 5, so the straight line is still "strongly disfavored".
- Piecewise − oΛCDM = 1.77 / 2.56 (printed 2.58 / 3.01). Both are < 5, so the two are still "without significant difference".
- oΛCDM is still preferred by both criteria.
- **No stated conclusion changes.**

## 5. Consequence

- The impact is low: a numerics erratum in a model-selection table whose qualitative verdicts survive.
- The paper is heavily cited, mostly for the Table 3/4 H(z) data and z_t. The citing papers sampled use the data and z_t only, not Table 5's numbers:
  - Jesus et al., arXiv:1704.08089, has its own AICc/BIC Table 5.
  - arXiv:2108.05409.
- I found no later paper that reuses 21.41 / 25.71 / 23.99 / 28.72 / 32.42 / 35.29.
- The value of the certificate is as a demonstration that printed information criteria can be checked against their own definitions. The claim should be phrased as "Table 5 does not satisfy Eqs. 5.3–5.4 as printed, and its BICs exceed the fit's", not as a scientific refutation.

## Specific corrections (docs only; the statements are fine)

1. Module doc, after claim 1: qualify "So in each row the two printed criteria are not values for one and the same maximum likelihood" with "under Eq. 5.4 as printed". Add that the oΛCDM and linear rows are consistent if the AICc column is plain AIC with N = 31 (implied c = 15.41 and 28.42), and that the piecewise row is consistent under no reading found.
2. Module doc, claim 2: replace "(… as the linear row's AICc indicates)". The line AICc matches χ²_min only with N = 30, while the paper says 31. Justify −2 ln L = χ² by Eq. 5.3's "L_max" and by the absence of the normalisation constant (≈ 200–228).
3. Optional: note that claim 1 also holds with independent N for the AICc and BIC columns, and that the formal wedge includes the degenerate point Ωm = ΩΛ = 0 (harmless).
4. Optional: record the corrected Table 5 values above, and that the paper's conclusions are unchanged.
