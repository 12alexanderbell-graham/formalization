STANDS-WITH-CORRECTIONS

# Referee: `Work/Cosmography/B1L19Curved.lean`

Both statements are true, with margins of 0.10 and 0.14 mag. The hypotheses are sound. The docstring overstates the theorems in three places. The qualitative answer is already in print (class **(a)**).

## 1. Attack

**Own computation.** Scripts are in `/tmp/claude-0/ref/`: mpmath at 30 digits on a 91×21 grid plus a refined grid at the corner. Setup: `E² = Ωu³ + Ω_k u² + 1 − Ω − Ω_k` and `d_L ∝ u sin(√−Ω_k χ)/√−Ω_k`.

- The minimum of `d_L(z₅)/d_L(z₃)` is **2.822662**, at Ω = 1, Ω_k = −0.1.
- The quartic ratios `P(x₅)/P(x₃)` are **2.400931** (SQ) and **2.469705** (SQG).
- The smallest residual differences are **0.3514** mag (bound 1/4, margin **0.101**) and **0.2901** mag (bound 3/20, margin **0.140**). All of these match the docstring.

**Sign and normalisation.** The goal is `5 log₁₀[(d₅/d₃)/(P₅/P₃)]`, so the factor `ln10/H` cancels. The direction is correct.

**Junk values and vacuity.**
- With Ω_k ≤ 0 and Ω_Λ ≥ 0, `E² ≥ Ωu³ + 1 − Ω > 0` for every u > 0. On [1, 4√2], E² ≥ 1. So no √ of a negative ever occurs.
- The `logb` arguments are positive (P₃ ≈ 1.34, P₅ ≈ 3.2).
- The sine argument is at most 0.852, so `d_L > 0`.
- The true ΛCDM scale factor satisfies every hypothesis, so the statements are not vacuous. Still add a curved `hyps_satisfiable` at promotion.

**Same K in the law and the distance.** `1 − omega0 = −K/(H₀²a₀²)` is exactly the Friedmann coefficient of `(1+z)²`. In the distance, `√K·χ = √(Ω₀−1)∫dz/E`. This is the same K, and Ω₀ ≥ 1 forces K ≥ 0, so the sine branch applies.

**Hypotheses.**
- `hdiff` and `hH₀` can be derived from the others, because `deriv` returns 0 off differentiability while `hH` makes the Hubble rate positive. Both are harmless.
- `h₅₃` and `h₃₀` are needed.
- **Ω ≥ 1/10 is load-bearing.** At Ω = 0.01, Ω_k ≈ −0.088 already reproduces both fitted ratios; at Ω = 0.05 the threshold is −0.19.

## 2. Physics meaning

The theorems certify only that reproducing the central fitted two-point ratio needs Ω_k < −0.1. The −0.26 figure is floating point, as stated.

Least-closed Ω_k that reproduces each fitted ratio (scanned, because the ratio is not monotone in Ω_k near the bounce):

| Ω | 0.1 | 0.2 | 0.3 | 0.5 | 1.0 |
|---|---|---|---|---|---|
| SQ | −0.268 | −0.378 | −0.469 | −0.624 | −0.948 |
| SQG | −0.259 | −0.359 | −0.439 | −0.572 | −0.841 |

"Below about −0.26" is confirmed. "Near the bounce boundary" is loose: the no-Big-Bang limit at Ω = 0.1 is Ω_k ≈ −0.45.

**Planck** (arXiv:1807.06209, Eq. (46b), p. 41): "ΩK = −0.044+0.018−0.015 (68 %, Planck TT,TE,EE+lowE)". The citation is correct. The 99 % region given on the same page is −0.095 < ΩK < −0.007. However, Table 4 (p. 40) gives the TT+lowE 95 % interval as −0.056+0.044−0.050, which reaches −0.106.

## 3. Prior art

Page numbers are PDF pages.

- **Khadka & Ratra 2020** (2004.09979), 2019 QSOs alone, non-flat ΛCDM:
  - p. 8: "Ωk0 = −0.48+0.51−0.43".
  - Table 3, p. 6: best fit Ωm0 = 0.56, ΩΛ = 0.98, Ωk0 = −0.54.
- **Khadka & Ratra 2021** (2012.09291), full 2038 QSOs, non-flat ΛCDM:
  - Table 3, p. 7: Ωm0 > 0.595, ΩΛ = 1.595, Ωk0 = −1.410+0.110−0.200.
  - p. 11: the subsets "tend to favor closed geometries".
- **Bargiacchi et al. 2022** (2111.02420, MNRAS 515, 1795), Lusso 2020 QSOs + Pantheon SNe:
  - Abstract: "SNe+QSO show evidence of a closed space"; BAO "confirms the flatness condition".
  - Table 2, p. 7: non-flat ΛCDM, SNe+QSO, Ω_M = 0.504 ± 0.029 and ΩΛ = 1.107, which implies Ω_k ≈ −0.61.
  - §4.2, p. 7: combining with BAO "is not proper".
  - This best fit lies on our threshold curve at Ω = 0.5.
- **Yang, Banerjee & Ó Colgáin** (1911.01681): flat ΛCDM only (QSO best fit has Ωm within 1σ of 1); no curvature fit.
- **Risaliti & Lusso 2019** (1811.02590): no non-flat fit (p. 4: "beyond the purposes of this work").
- **Lusso et al. 2019 / 2020** (1907.07692, 2008.08586): flat models only.

**Class (a).** Already published: in non-flat ΛCDM the quasar Hubble diagram needs a strongly closed universe (Ω_k ≈ −0.5 to −0.6; ≈ −1.4 on the full set), and that conflicts with flat-consistent probes. New: only the certified, likelihood-free bound on the central fitted curves.

## 4. Docstring corrections

1. Replace "|Ω_k| ≤ 1/10 contains every curvature allowed by the CMB alone". The theorems cover [−1/10, 0] only. Use "contains the 99 % region of Planck TT,TE,EE+lowE", since TT+lowE at 95 % reaches −0.106.
2. In "closing the universe within that range cannot …", add "for Ω_m ≥ 1/10". Without it the sentence is false.
3. In the title, change "shape of the fitted curves" to "two-redshift distance ratio of the *central* fitted curves". Coefficient uncertainties are ignored.
4. Drop "near the bounce boundary".
5. Cite Khadka & Ratra 2020, Khadka & Ratra 2021 and Bargiacchi et al. 2022.
