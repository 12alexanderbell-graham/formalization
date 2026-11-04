# Blind restatement notes: Farooq & Ratra 2013 (arXiv:1301.5243v1), flat ΛCDM, prior 68 ± 2.8

Sources read: arXiv:1301.5243v1 (Sec. 2, Table 1, Figs. 1–3 captions); for the likelihood,
arXiv:1211.4253v1 (Farooq, Mania & Ratra), Eqs. 14–18. Both came from arxiv.org/pdf.
Note: the brief said "Farooq et al. (2013) = arXiv:1212.4264". The paper's bibliography says
otherwise: Farooq et al. 2013 is 1211.4253, and 1212.4264 is Farooq & Ratra 2012. Eq. 18
with the likelihood is in 1211.4253.

## Interpretive choices
1. Table: 28 rows (z, H, σ_H) copied in printed order. I checked them against a rendered
   image of page 4. Units are km/s/Mpc.
2. Model: H = H0 √(Ωm(1+z)³ + 1 − Ωm), which is the φCDM model at α = 0 (Fig. 3 claim). The
   Fig. 1 ΛCDM fit is non-flat. Its χ²_min is also 18.24, but its best fit is (0.29, 0.72),
   not flat.
3. χ²_H(H0, Ωm) = Σ (H0 E(z_i) − H_i)²/σ_i² (Eq. 14 of 1211.4253).
4. Marginalisation: Eq. 16 of 1211.4253. H0 is integrated over (0, ∞), and the prior is
   normalised by 1/√(2πσ²). Ambiguity: the closed-form Eq. 18 as printed has the prefactor
   1/√(2ασ²). The correct value of the Eq. 16 integral is 1/√(4ασ²), so the two differ by
   ln 2 ≈ 0.693 in χ². I followed Eq. 16 (the definition) rather than Eq. 18 (its claimed
   evaluation). Neither choice moves the maximiser. Integrating over ℝ instead of (0, ∞)
   changes χ² by less than 1e-10 here.
5. χ²(p) := −2 ln L_H(p), as 1211.4253 states. χ²_min means its value at the maximiser.
6. Allowed range: Ωm0 ∈ [0, 1]. The paper does not say this explicitly. Figs. 1–3 show
   Ωm0 ∈ [0, 0.5]. For flat φCDM, non-negative scalar-field energy needs Ωm0 ≤ 1. The
   maximiser is interior, and χ² is unimodal on [0, 1], so this choice does not matter.
7. "Best fit Ωm0 = 0.29" is read as: every maximiser lies in [0.285, 0.295).
8. Transition redshift: q(z) = −1 + (1+z)H'/H. Setting q = 0 gives
   z_da = (2(1−Ωm)/Ωm)^{1/3} − 1 (valid for 0 < Ωm < 2/3). I added a spec lemma for this.

## Numerical results (numpy/scipy, bounded minimisation; checked by quadrature)
- Maximiser: Ωm0 = 0.287793. It rounds to 0.29, so the main theorem looks TRUE.
- χ²_min (Eq. 16 reading) = 18.1987. At Ωm0 = 0.29 it is 18.2046. Printed: 18.24, a gap of
  0.04. With the Eq. 18 prefactor as printed: 17.5055. Profile χ² (minimised over H0,
  including the prior term) = 16.379. None of these gives 18.24, so the literal χ²_min
  theorem looks FALSE. I kept it in the file for comparison only.
- Non-flat ΛCDM 2-D fit (a cross-check): (0.2923, 0.7238), χ² = 18.1935. Printed:
  (0.29, 0.72), 18.24.
- z_da at the true maximiser = 0.7042. The printed φCDM value is 0.698, which equals
  z_da(0.29) = 0.6981. So the paper evaluated z_da at the rounded (or grid) best fit. The
  literal "z_da rounds to 0.698" statement looks FALSE. The range statement
  z_da ∈ (0.684, 0.713) follows from Ωm0 ∈ [0.285, 0.295) and holds.
