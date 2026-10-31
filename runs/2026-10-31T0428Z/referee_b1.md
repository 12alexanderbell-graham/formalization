VERDICT: STANDS-WITH-CORRECTIONS (all four frozen statements are true, non-vacuous and faithful; corrections are to the module docstring's claims of significance, not to any statement)

Referee report on Work/Cosmography/B1Truncation.lean (frozen in run 2026-10-31T0428Z). Independent referee, 2026-10-31.
Scratch scripts: /tmp/referee_b1/{taylor,num,fit,extra}.py (outside the repo).

## 1. Bridge `lumDistFlat_flatLCDM`: correct
1. My derivation: put x = a(s)/a(t0), so dt = dx/(xH) and H = H0 sqrt(Omega x^-3 + 1 - Omega). Then
   a0 * Int_t^t0 ds/a = H0^-1 Int_{a(t)/a0}^1 dx / (x^{1/2} sqrt(Omega + (1-Omega)x^3)). Substituting x = v^2 gives
   H0^-1 Int_{sqrt(a(t)/a0)}^1 2 dv / sqrt(Omega + (1-Omega)v^6). Multiplying by (1+z) gives the stated RHS.
   Checks: sympy confirms d/dz of the v-integral with w = (1+z)^-1/2 equals 1/E(z) exactly. A numerical check of
   the z-form against the v-form agrees to 1e-17 at (Omega, z) = (0.3, 3) and (0.25, 7).
2. The hypotheses are sufficient. a > 0 and DifferentiableAt on Icc make 1/a continuous, hence integrable, so
   `comoving` is a genuine value and not the junk 0. With 0 <= Omega <= 1 and 1 + z = a0/a > 0, the radicand
   Omega(1+z)^3 + 1 - Omega is > 0. So H > 0 on [t, t0], a is strictly increasing, and deriv a = a*H0*sqrt(...) is
   continuous on Icc (a is C^1 there), which is what the substitution lemma needs. The case t = t0 makes both sides 0.
3. The hypotheses are consistent (not vacuous). The exact solution a(t) ∝ sinh^{2/3}(1.5 sqrt(1-Omega) H0 t), t > 0,
   meets all of them and reaches z = 3 and z = 7.
4. `hH0` is genuinely needed. `hH` at s = t0 reduces to H0 = H0*1, which carries no information. With H0 = 0, a
   constant a makes LHS = t0 - t while RHS = (..)/0 = 0. `hΩ₁ : Ω ≤ 1` is not needed (for v <= 1 the integrand
   stays positive when Omega > 1) but is harmless. Two-sided DifferentiableAt at the endpoints is slightly stronger
   than needed, but a is defined on all of R, so this is harmless.
5. Junk values cannot make any conclusion true for the wrong reason. H0 > 0 rules out division by zero. Both
   sqrt arguments are positive. If `logPolyDL3` were <= 0, Real.logb would silently use |.|, and the explicit
   `0 < logPolyDL3 ...` conjunct guards against that (it holds anyway: a2 > 0 for Omega < 2, and a3 has negative
   discriminant 4 - 21/4, so a3 > 0). lumDistFlat > 0 follows from the bridge. A junk lumDistFlat = 0 would make
   logb = 0 and the statement false, not true. `cubic_shape_miss` has no positivity conjunct, but it does not need
   one: the true values are positive, so logb is the genuine log there too.

## 2. Numerics: all three bounds hold with margin
1. Taylor coefficients, re-derived with sympy (H0 d_L as a series in u = ln(1+z)): coefficients 1, 3/2 - 3Ω/4 and
   9Ω²/8 - 2Ω + 7/6. Converting to x = log10(1+z) multiplies the u^n coefficient by ln10^(n-1), which reproduces
   `lusA2`/`lusA3` and Lusso+19 Eq. (8) exactly. (The 4th-order coefficient
   -135Ω³/64 + 9Ω²/2 - 47Ω/16 + 5/8 also matches L19 Eq. (8).) Note: RL19 Methods prints a3 = 7/6 - 2Ω + 9/8 Ω,
   which lacks the square on Ω and the ln10 powers. The module docstring mentions only the ln10 issue.
2. Misses (mpmath, 30 digits, Omega grid step 2e-4 on [0.2, 0.4]), with miss(z) = 5 log10(dL_LCDM / dL_cubic):

   | quantity | true min over Ω | argmin Ω | max (Ω) | frozen bound |
   |---|---|---|---|---|
   | miss(z=3) | 0.11535 | 0.3496 | 0.1746 (0.2) | > 0.09 |
   | miss(z=7) | 0.36833 | 0.3128 | 0.4226 (0.2) | > 0.3 |
   | miss(7) - miss(3) | 0.24462 | 0.244 | 0.2683 (0.4) | > 0.18 |

   The miss is not monotone in Omega. For Omega = 0.3, dL_LCDM/dL_cubic is 1.010, 1.030, 1.057, 1.088, 1.120,
   1.153, 1.185 at z = 1..7.
3. Proof-engineering note. Both dL_LCDM and the cubic decrease in Omega on [0.2, 0.4], so the bound can be proved
   by monotone bracketing on Omega sub-intervals. Worst-case lower bounds for N equal sub-intervals:
   - N = 8: z3 0.068, z7 0.308, shape 0.114.
   - N = 16: z3 0.0917, z7 0.338, shape 0.180.
   So z7 needs N >= 8, and z3 and the shape bound need N >= 32 (or a sharper bound) to clear 0.09 and 0.18.

## 3. Fidelity of statements to docstrings
1. The quantifiers and hypotheses express "flat ΛCDM on [t, t0]" correctly. The Friedmann law is imposed at every
   s in the interval, with H0 := hubble a t0 > 0. `cubic_shape_miss` imposes it on [t7, t0], which contains t3.
   Its conclusion is the intended normalisation-free quantity: multiplying the polynomial by a constant (H0 or a
   magnitude offset) cancels in the difference. No hypothesis is vacuous, and none is unused except possibly
   `hΩ₁ : Ω ≤ 1` in the bridge (finding 1.4).
2. The theorem docstrings are accurate, including "underestimates": every miss is positive.
3. Correction (header item 3). "a fit with a free normalisation cannot absorb it" is true only if (a2, a3) are
   held at the Taylor point. RL19's fit also frees a2 and a3, and moving them absorbs the shape (see 4.2).
   Suggested rewording: "cannot be absorbed by the normalisation alone; it can only be absorbed by moving (a2, a3)
   away from the ΛCDM Taylor point". Optionally add the immediate corollary: for every m,
   max(|miss3 - m|, |miss7 - m|) > 0.09. That is, the Taylor-point cubic cannot match ΛCDM to within 0.09 mag on
   {3, 7}, even with a free zero point.
4. Correction (scope). As far as I recall, RL19's quasar sample ends at about z ≈ 5.1 (I did not check this against
   the paper). Lusso+19 reaches z ≈ 6.7 only with GRBs and a 4th-order polynomial. So the z = 7 statements lie
   outside the range where the cubic was actually used, and the docstring should say so.
   Recommended companion statements, both true:
   - miss(z=5) > 0.24: true min 0.2440. Margin is thin, so use 0.2.
   - miss(5) - miss(1) > 0.2: true min 0.2251.
   - miss(5) - miss(3) is only ≥ 0.124, so a 3-to-5 shape bound would be weaker.

## 4. Meaning for the dispute
1. Reconciling Lusso+19. Their sentence "reproduce flat ΛCDM up to z > 5 with only a few per cent difference"
   cannot describe the Taylor-coefficient cubic: at Omega = 0.3 that cubic is 12.0% (0.246 mag) low at z = 5.
   It does fit a cubic fitted to ΛCDM. Least-squares fits of x + a2x² + a3x³ to exact ΛCDM (Omega = 0.3,
   z ∈ [0, 5]) have a maximum deviation of 2.1% (fixed normalisation) or 3.1% (free normalisation); minimax fits
   get 0.03 mag. I could not see RL19 Extended Fig. 5 itself, so which curve it plots is unresolved. For
   comparison, the 4th-order Taylor polynomial at Omega = 0.3 is 2.1% low at z = 5 and 4.7% low at z = 6.7.
2. The fitted point lies far from the Taylor point. At Omega = 0.3 the Taylor point is (a2, a3) = (2.936, 3.541).
   Least-squares cubic fits to exact ΛCDM on [0, 5] land at:
   - fixed normalisation: (2.59, 4.85)
   - free normalisation: (2.31, 4.93)
   - z_max = 3: (2.67-2.79, 4.32-4.40)
   This is a shift of about 1.3-1.4 in a3. So data generated exactly by ΛCDM would be fitted at a point displaced
   from the Taylor point, and RL19's tension is measured relative to the Taylor point.
3. Strongest honest statement. For every flat ΛCDM model with 0.2 ≤ Ωm ≤ 0.4, the log-polynomial that RL19/L19
   use as the ΛCDM reference point is certifiably not ΛCDM at the redshifts that drive the claim. It
   underestimates the distance modulus by more than 0.09 mag at z = 3 and more than 0.3 mag at z = 7. The growth
   between them (more than 0.18 mag) cannot be removed by H0 or by any magnitude offset. Comparing fitted (a2, a3)
   with the Taylor point is therefore not a test of ΛCDM unless the truncation offset is accounted for. This
   certifies the mechanism behind the "phantom tension" critique. It does not, by itself, show that RL19's 4σ
   disappears, because that depends on the data's error ellipse.
4. Decisive next step. Prove a separation theorem:
   - Statement: for each Omega in [0.2, 0.4] and each (a2, a3, m) with sup over z in [0, z*] of
     |5 log10(dL_LCDM / cubic) - m| <= ε (e.g. z* = 5, ε = 0.05 mag), the distance from (a2, a3) to the Taylor
     point is at least δ(ε).
   - Numerically δ is about 1 in a3 (from 4.2).
   - Then compare δ with RL19's 1σ ellipse to see what fraction of the 4σ is truncation bias. A weaker,
     shape-only version (sup over z in [3, 5] or [1, 5], with free m) follows the same pattern as
     `cubic_shape_miss`.

## 5. Prior art (numerical only; none proved)
1. Yang, Banerjee & Ó Colgáin 2020 (arXiv:1911.01681, PRD 102, 123532):
   - Plots Δd_L of the 4th-order log polynomial against exact ΛCDM for several Ωm. It says this stays under 1%
     to z ≈ 4.3 at Ωm = 0.3.
   - Mock fits displace H0, a2 and a3 by about 2σ from the canonical values.
   - No 3rd-order mag-level numbers at z = 3 or 7.
2. Banerjee et al. 2021 (arXiv:2009.04109, PLB):
   - Fig. 1 plots the fractional Δd_L of the Taylor polynomials (n = 3, 4, 5; Ωm = 0.1-0.9) against exact ΛCDM,
     and states only that deviations exceed 1% beyond z ~ 1.5-2.
   - n = 3 fits to ΛCDM mocks miss ΛCDM by 8σ (Ωm = 0.1) and 6σ (Ωm = 0.9), which they call "phantom tensions".
   - The content is qualitatively ours, read off a plot. There are no tabulated values, no Ωm-uniform bounds, and
     no normalisation-free shape quantity.
3. Bargiacchi et al. 2021 (arXiv:2101.08278, A&A 649, A65):
   - Plots the ratio of the 5th-order Taylor polynomial to ΛCDM up to z ≈ 7.5. They concede that the Taylor
     comparison is "strictly valid only up to z ~ 1".
   - Mock fits with orthogonal polynomials at Ωm = 0.28 shift a3 and a4 by 0.7σ and 1.5σ.
   - Nothing about the 3rd-order Taylor cubic at z = 3 or 7.
4. Conclusion: the qualitative fact (the Taylor-point cubic departs from ΛCDM at high z) is known and documented
   numerically and graphically, mainly in 2009.04109 Fig. 1. The specific Ωm-uniform mag bounds, the
   normalisation-free z = 7 minus z = 3 shape bound, and any certified (proved) version appear to be new. The
   significance claim should credit 2009.04109 for the mechanism.

Sources: https://arxiv.org/abs/1911.01681v3 , https://ar5iv.labs.arxiv.org/html/1911.01681 , https://arxiv.org/pdf/2009.04109 , https://ar5iv.labs.arxiv.org/html/2101.08278 , https://www.aanda.org/articles/aa/full_html/2021/05/aa40386-21/aa40386-21.html
