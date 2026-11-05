# Referee report: Work/Data/Moresco16Min.lean (certified minimum of the oΛCDM χ², Moresco et al. 2016)

**VERDICT: STANDS-WITH-CORRECTIONS.**
- All five frozen statements are true, with real margins. The file elaborates: `lake env lean` gives only five `sorry` warnings.
- The corrections are to the docstrings and module doc only. No Lean statement needs to change.

Scripts, all in `runs/2026-11-05T0628Z/scripts/`. They are independent of the program's `feas_wide.py` and `opt_float.py`: own data entry, own enclosure method, and 50-digit mpmath.
- `referee_min.py`: global branch and bound plus 50-digit refinement.
- `referee_min_variants.py`: grids, boundary minima and alternative readings.
- `referee_min_hyp.py`: whether the hypotheses are needed.

Source: arXiv PDF v2 (arxiv.org/pdf), Sec. 5.2 and Table 5. Text dumps are in `/tmp/claude-0/referee/m16/`.

## 1. Independent global minimum

**Method.**
- For fixed (Ωm, ΩΛ), χ² is a quadratic in H0 with positive leading coefficient α. So the minimum over all real H0 is exactly F = γ − β²/α. That minimum is attained, so free H0 is handled exactly.
- I ran branch and bound over (Ωm, ΩΛ). Each box gets a lower bound, the better of:
  - a natural interval bound, with E² clipped at 0;
  - a centred mean-value form, using an interval gradient, on boxes where every E² > 0.
- The bounds are computed in floats with a safety margin of 1e-6. Float error is about 1e-11.
- Soundness spot-check: over 20,000 random boxes and points, the smallest value of F(p) minus the box's bound was +4.8e-6, so the bounds never failed.

**Wide region (Ωm ≤ 1, ΩΛ ≥ 0, E²(zᵢ) ≥ 0 at all 30 zᵢ).**
- The region is compact: Ωm ≥ −1/1.965 = −0.5089 (forced by ΩΛ ≥ 0), and ΩΛ ≤ 2.60100 (the LP vertex maximum).
- B&B proves F ≥ 14.9665 everywhere: 7,951 boxes, 0 failures.
- It also proves F ≥ 14.967037 everywhere: 12,167 boxes, 0 failures, safety margin 1e-9.
- Every point with F < 14.968 lies in Ωm ∈ [0.421, 0.452], ΩΛ ∈ [0.959, 1.003]. So there is one basin and no second minimum.
- Boundary pieces:
  - On E²(zᵢ) = 0, the lowest value is F = 104.5, at Ωm = −0.509, ΩΛ = 0, with E²(1.965) = 0. The other ten reachable E² = 0 lines have F > 400.
  - On ΩΛ = 0, the minimum is 28.14.
  - On Ωm = 1, the minimum is 28.23.
  - Near the E² = 0 boundary, including large ΩΛ (up to 2.6 at Ωm = 1), F is far above the minimum.
  - A dense 1200² grid gives 14.96706, at the same point.

**Minimum, at 50 digits** (findroot on the gradient, starting from the best B&B box rather than the known optimum):
- χ²_min = **14.967038174884521725**
- Ωm = 0.436173190212, ΩΛ = 0.981438580058, H0 = 72.2865137376
- z_t = 0.65099, Ωk = −0.4176, min E²ᵢ = 1.0377
- The Hessian is positive definite (det 1.89e4), so this is an interior minimum.
- This matches the previous referee's 14.96703817488452.

**Paper's prior region** (0 ≤ Ωm ≤ 1, 0 ≤ z_t ≤ 1.5):
- The prior region lies inside the wide region.
- The minimiser lies inside the prior region: 2ΩΛ/Ωm = 4.5002, which is in [1, 15.625].
- So the minimum over the prior region is the same 14.96703817…, attained at an interior point.

**Margins:**
- Lower: χ²_min − 14.9665 = 5.38e-4.
- Upper: 14.9675 − χ²_min = 4.62e-4.
- **Nothing lies below 14.9665 in either region.**

## 2. Attack on the statements

**`chiSqOL_ge`: true. Its hypotheses are sufficient but not minimal.**
- Drop Ωm ≤ 1 and ΩΛ ≥ 0, keeping only E² ≥ 0: B&B over [−1000, 1000]² still proves F ≥ 14.9665.
- Drop every hypothesis and use Lean's junk value √(negative) = 0: B&B over [−1000, 1000]² still proves it.
- Beyond that box, F tends to at least 73²/2.4² ≈ 925, because y(0) = 1 and large parameters force H0 → 0.
- So even the unconditional statement is true.
- Keeping `hy` is still the honest choice, because it excludes junk values.
- `hm` and `hl` are only proof conveniences, for compactness. The docstring could say so.
- Note that `hy` constrains E² only at the 30 table redshifts, not on all of [0, 1.965]. That makes the region larger, which strengthens the claim.
- Junk √ cannot enter: `hy` (≥ 0), and > 0 in the prior set, rule it out. Divisions by σᵢ², 2.4² and N − 4 are all safe.

**`chiSqOL_lt`: true** (margin 4.6e-4). A decimal witness needs Ωm to within about 1e-3, given Hessian ≈ 527 in Ωm.

**`chiSqOL_glb_prior` / `chiSqOL_glb_wide`: true and honest.**
- Each set is nonempty and bounded below, so the content is the location of the bound. That content is exactly claims 1 and 2 combined; claim 2's witness lies in both sets.
- `IsLeast` would also be true, because both infima are attained at the same interior point. It is not needed: `IsGLB` does not overclaim.
- Quantifiers are correct, and the GLB is unique.
- Nit: the prior set's encoding admits Ωm = ΩΛ = 0, where z_t is undefined. This is harmless.
- Nit: the paper's own text (Fig. 7 to z_t = 2.5; 3σ range 0.41 < z_t < 2.2) suggests the effective z_t range was wider than 1.5. The wide-region result covers that.

**`table5_oL_aicc_unattainable`: true, and it says what its docstring says.**
- The smallest AICc over N ∈ (4, 31] occurs at N = 31: χ² + 6 + 24/27 ≥ 14.9665 + 6.8889 = 21.855 > 21.415.
- The actual margin is 0.44, far more than the stated 0.005. The theorem is a direct corollary of claim 1.
- **Correction:** "no parameter values give the printed number" is true only for Eq. 5.4 with k = 3 and −2 ln L = χ² including the prior term. The docstring should say that it is conditional and point to §4 below. Without that, it reads like a plain "the number is wrong".

**Module doc corrections:**
- **(i)** Say explicitly that 14.967 is the χ² **including the prior term** (H0 − 73)²/2.4². The 30-point data part at the optimum is 14.879.
  - This matters because a data-only (no-prior) number is in print (§3), and it is 0.5 lower.
- **(ii)** Mention the plain-AIC reading under claim 4, as the previous referee did for `Moresco16.lean`.

## 3. Prior art

**Is claim (A) already in print?**
- Searched: arXiv v2 PDF, web searches, and the later papers that reuse the 30 points (arXiv PDFs 1612.08491, 1604.00183, 1607.03537, 1704.08089, 1802.02255).
- **I found no printed −2 ln L_max or χ²_min for this exact fit (Table 4, open ΛCDM, H0 = 73 ± 2.4).** The paper prints only AICc and BIC.
- Moresco et al. 2016b (arXiv:1604.00183) uses the same prior, but prints no χ² values.
- Farooq et al. 2017 (arXiv:1607.03537) prints χ²_min, but for 38 points (including BAO) with h priors 0.68 ± 0.028 and 0.7324 ± 0.0174. That is a different fit.

**Nearest printed neighbour: Wei, Melia & Wu 2017 (arXiv:1612.08491), Table 1, oΛCDM.**
- They fit the same 30 points **without** the H0 prior, deliberately.
- They print H0 = 69.0, Ωm = 0.36, ΩΛ = 0.77, AIC = 20.46, BIC = 24.66, so χ²_min ≈ 14.46.
- I reproduce this, using z = 0.4497 (Table 3's value, which corrects the Table 4 typo 0.44497):
  - data-only χ²_min = 14.4616 at (69.00, 0.360, 0.766);
  - AIC = 20.462, BIC = 24.665.
- With the typo as printed, I get 14.4784.
- So the no-prior counterpart is in print, as a minimiser output. The with-prior value 14.967 is not.
- This also independently validates the program's data and χ² definition.

**Moresco 2016 versions and errata.**
- JCAP version: the INAF repository lists a publisher PDF, but its download link returned an HTML page. The publisher text and any corrigendum therefore remain **unchecked**, as in the previous report.
- No erratum or corrigendum was found by search.

**Certified global minima of cosmological χ².**
- None found.
- Generic tools exist:
  - formal proofs for nonlinear optimisation (Magron et al., arXiv:1404.7282);
  - a Lean interval-optimisation library ("LeanCert").
- I found no published certified or interval-based global minimum of any cosmological fit. The certification aspect appears new, as far as this search reaches.

## 4. Readings of Table 5's oΛCDM AICc (21.41) under which claim 4 would be unfair

To print 21.41 under Eq. 5.4 with k = 3, the authors' c = −2 ln L_max would have to be 14.521 (N = 31) or 14.487 (N = 30). Both are below the certified minimum 14.967.

| Reading | What it implies | Effect on claim 4 |
|---|---|---|
| (a) Column is plain AIC (no 2k(k+1)/(N−k−1) term) | c = 15.41. AIC at the optimum is 20.967, so the printed value is 0.443 *too high*. This reading also makes AICc − BIC match with N = 31 (previous report). | **Unfair.** The printed number is attainable, by non-optimal parameters, and claim 4 does not apply. This is the most plausible reading. |
| (b) k = 2 (H0 treated as a prior, not counted) | AICc(N=31) at the optimum is 19.40 < 21.41 | Unfair, but contradicts the paper's three free parameters (H0, Ωm, z_t). k = 4 or more keeps the claim true. |
| (c) L_max of the 30 data only; the prior is used in the fit but left out of L | Data-only min is 14.478 (14.462 with the typo fixed). AICc is 21.367 (N = 31) or 21.401 (N = 30), so 21.41 is attainable and within 0.01 of the optimum's value at N = 30. But BIC would then be 24.68–24.78, against the printed 25.71, so the row still does not reconcile. | **Unfair under this reading.** It conflicts with the Table 5 caption ("all constraints assume a gaussian prior on H0"). |
| (d) N ≥ 59 | χ²_min + 6 + 24/(N−4) = 21.41 requires N = 58.2 | Unfair only for an implausible N. With 30 data plus the H0 point, N ≤ 31. |
| (e) H0 marginalised instead of profiled | c = 16.10, AICc = 22.99 | Fair: still unattainable. |
| (f) Gaussian normalisation Σ ln 2πσ² included | c rises by about 200 | Fair. |
| (g) Typo z = 0.4497 fixed | χ²_min = 14.950, AICc = 21.84 | Fair. |
| (h) Non-converged minimiser or posterior-mean point | c can only rise | Fair: a sloppy minimiser cannot explain a printed value that is too low. |
| (i) Other H0 priors (73.24 ± 1.74, 73.8 ± 2.4) | c = 15.08 or 15.19 (previous report) | Fair. |

Bottom line for claim 4:
- It is correct as stated, under its stated premises: Eq. 5.4, k = 3, χ² with the prior.
- Readings (a) and (c) are the ones a reader must be told about. Under either, "unattainable" says nothing against the paper's number.
- Recommended wording: *"Under Eq. 5.4 with k = 3 and −2 ln L = χ² (prior included), the printed 21.41 is below every attainable AICc. If the column is plain AIC, or if L_max omits the prior term, the printed value is attainable and the discrepancy is instead 0.44 above (AIC), or 0.01–0.04 above (data-only AICc), the value at the optimum."*

## Specific corrections (docs only)

1. Module doc and the claim 1 docstring: state that the χ² includes the prior term. Optionally note that 14.46 (no prior, z = 0.4497) is in print in Wei, Melia & Wu 2017, Table 1, and that this program reproduces it.
2. Claim 1: optionally note that `hm`, `hl` and even `hy` are not needed for truth (checked numerically over [−1000, 1000]²), and that they are kept for physical meaning and compactness.
3. Claim 4: make the premises explicit, and add readings (a) and (c) from §4.
4. Novelty line: say that the with-prior χ²_min was not found in print, and that the JCAP publisher version and any corrigendum are unchecked.
