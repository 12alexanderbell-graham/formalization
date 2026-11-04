# Referee report: Work/Data/FR13.lean (frozen statements)

**Verdict: STANDS-WITH-CORRECTIONS.** All corrections are to docstrings and citations. No theorem statement has to change.

All eight frozen statements are true by independent high-precision numerics, and each holds with margin. The definitions follow the procedure the paper cites, with no junk-value exposure. The corrections concern (a) what the header says about the integration range and where Eq. 18 lives, and (b) recording that the paper's printed digits come from a 0.01 grid, so the frozen intervals are meant to exclude the printed 0.698 and 0.817, and that the printed 18.24 cannot be reproduced.

Sources read, all from arxiv.org/pdf and kept in /tmp/claude-0/ref/:
- FR13 = arXiv:1301.5243v1. I rendered p. 4 at 200 dpi and read the PNG.
- arXiv:1212.4264v1.
- arXiv:1211.4253v1.

Scripts (mpmath, 25 to 40 digits) are in /tmp/claude-0/-home-claude-formalization/9d43bf59-0c2d-5e29-a61c-6776788929a6/scratchpad/fr13num.py, fr13b.py, fr13c.py, fr13d.py and fr13e.py.

## 1. Attack on the statements

**Table.** I checked all 28 rows (z, H, σ_H) against the rendered page 4. `fr13Table` matches in printed order. The real literals elaborate to exact rationals, and every σᵢ is greater than 0.

**chiSqHz.** This is Eq. 14 of Farooq, Mania & Ratra 2013 with H_th = H₀E(z), and E² = Ω(1+z)³ + 1 − Ω. It is faithful.

**margChiSq and the source of "Eq. 18".**
- FR13's "Farooq et al. (2013)" is **Farooq, Mania & Ratra 2013, arXiv:1211.4253**, according to FR13's bibliography.
- arXiv:1212.4264 is FR13's "Farooq & Ratra (2012)". It has only seven numbered equations and no Eq. 18. The brief's identification "Eq. 18 = arXiv:1212.4264" is wrong.
- In 1211.4253, Eq. 16 gives L_H(p) = (2πσ²_H₀)^{-1/2} ∫₀^∞ e^{−χ²_H/2} e^{−(H₀−H̄₀)²/(2σ²_H₀)} dH₀, and Eqs. 17–18 give the erf closed form.
- The frozen definition is −2 ln of Eq. 16, with ∫₀^∞ replaced by ∫_ℝ. The prior is normalised the same way. This is faithful.
- Eq. 18 as printed has the prefactor (2ασ²)^{-1/2}. The correct closed form of Eq. 16 has (4ασ²)^{-1/2}, so Eq. 18 is off by a factor √2, which would shift χ² by −ln 2. The paper's printed 20.64 matches Eq. 16, not Eq. 18 (see Section 2), so the frozen choice is the right one.
- Integration range: ℝ versus (0, ∞) changes the integral by a relative amount erfc(β/√(2α))/2.
  - 68 prior: 1.9·10⁻⁷⁹³.
  - 73.8 prior: 4.0·10⁻⁸⁷⁰.
  - The posterior on H₀ is about 68.05 ± 1.13 and 71.10 ± 1.13, which puts H₀ = 0 more than 60σ away.
  - The header's "below 10⁻¹⁰⁰" is true. Its "the paper does not state the integration range" is true of FR13 but not of the procedure FR13 cites (correction 1).

**Junk values.** There are none.
- The prior σ is 2.8 or 2.4, and all σᵢ are nonzero.
- For Ω ∈ [0, 1] and zᵢ ≥ 0, the radicand is 1 + Ω((1+z)³ − 1) ≥ 1.
- The integrand is a continuous, strictly positive Gaussian in H₀, because α = 1/σ² + Σ E²/σᵢ² > 0. So it is integrable with a positive integral, and the log is finite.
- Proof note: the prover must establish integrability. A non-integrable Bochner integral would be 0, which would make margChiSq = 0. This is a proof obligation, not a statement defect.

**Quantifiers and domain.**
- The "every minimiser over [0, 1] lies in I" statements, together with the existence statements, make a non-vacuous certification. Uniqueness is not claimed and is not needed.
- [0, 1] is the natural physical range: Ωm0 ≥ 0 and Ω_Λ = 1 − Ω ≥ 0. The minimiser is interior: F(0) = 458.5 and F(1) = 163.3 for the 68 prior, and 442.7 and 233.5 for 73.8. On a 0.005 grid, F′ changes sign exactly once (not proved). So the choice of domain does not matter.
- "Best fit = minimiser of the flat-law marginal χ² over Ω" is the right reading. Two caveats:
  - The paper's φCDM best fit is a 2-D maximum over (Ωm0, α). It equals the flat-law fit only because it lands on α = 0, which is the paper's claim and is not certified here.
  - The paper's numbers are 0.01-grid values. The frozen statements concern the continuous minimiser.

**Transition redshift.** For E² = Ω(1+z)³ + 1 − Ω, the deceleration parameter is q(z) = [Ω(1+z)³/2 − (1 − Ω)]/E². So q = 0 exactly when Ω(1+z)³ = 2(1 − Ω), and for Ω ∈ (0, 1) there is a unique solution with z > −1. The definition is correct, and it is the same formula that reproduces the paper's printed values (Section 2).

The zda theorems follow from the bestfit theorems:
- zda(0.2875) = 0.70501 and zda(0.2881) = 0.70334, both inside (0.703, 0.706).
- zda(0.2531) = 0.80717 and zda(0.2537) = 0.80527, both inside (0.805, 0.808).

## 2. Independent numerics

The closed form is F(Ω) = γ − β²/α + ln(ασ²), with α, β, γ from Eq. 17. Direct `mp.quad` integration of the frozen integrand over ℝ, and over (0, ∞), agrees with the closed form to 15 digits.

| Prior | Ω* (continuous) | Frozen Ω interval | F(Ω*) | Frozen min interval | zda(Ω*) | Frozen zda interval |
|---|---|---|---|---|---|---|
| 68 ± 2.8 | 0.2877933 | (0.2875, 0.2881) | 18.198665 | (18.19, 18.21) | 0.704192 | (0.703, 0.706) |
| 73.8 ± 2.4 | 0.2533852 | (0.2531, 0.2537) | 20.616742 | (20.61, 20.62) | 0.806266 | (0.805, 0.808) |

**Margins.**
- Ω: about 0.0003 on each side. F″(Ω*) = 2439 for the 68 prior and 3515 for 73.8. F rises above its minimum at the interval ends by 1.05·10⁻⁴ and 1.15·10⁻⁴ (68), and by 1.43·10⁻⁴ and 1.74·10⁻⁴ (73.8). A proof that encloses F directly needs accuracy better than about 5·10⁻⁵. An argument from the sign of F′ has a comfortable margin, with |F′| ≈ 0.7 to 1.1 at the ends.
- Minimum value: 0.0087 and 0.0113 (68); 0.0067 and 0.0033 (73.8).
- zda: at least 0.0012 everywhere.

**Conventions compared with the printed values**, at the paper's grid points Ω = 0.29 [0.25] and at the continuous minimum:

| Convention | Value at 0.29 [0.25] | Minimum | Argmin |
|---|---|---|---|
| Frozen: normalised prior, over ℝ (same as over H₀ > 0) | 18.2046 [20.6371] | 18.1987 [20.6167] | 0.28779 [0.25339] |
| Eq. 18 as printed (√2 prefactor) | 17.5114 [19.9440] | — | same |
| Unnormalised prior | 14.3074 [17.0483] | — | same |
| Quadratic part only (profile over H₀ with prior term) | 16.3824 [19.1271] | — | 0.28843 [0.25383] |
| Profile, no prior | 16.3816 | 16.3794 | 0.28830 |
| χ² at H₀ = H̄₀ | 16.386 [24.098] | — | 0.28859 [0.22699] |
| H₀ truncated to ±1σ, ±2σ, [60, 80] or [65, 80] | shifts of +0.003 to +1.6 that do not fit the pattern | — | — |

What each printed number reduces to:
- **Ω = 0.29 [0.25]:** reproduced as 0.01-grid rounding of 0.2878 [0.2534]. The best grid point under the frozen convention is exactly 0.29 [0.25].
- **zda = 0.698 [0.817]:** reproduced exactly as zda at the grid Ω: zda(0.29) = 0.69810 and zda(0.25) = 6^{1/3} − 1 = 0.81712. The continuous values are 0.7042 [0.8063], which differ by +0.006 [−0.011].
- **χ²_min = 20.64:** reproduced by the frozen convention at Ω = 0.25, which gives 20.637.
- **χ²_min = 18.24: not reproduced by any natural convention.**
  - The frozen convention gives 18.205 at Ω = 0.29.
  - The paper's other captions are also 0.03 to 0.075 above my values at their printed points:
    - ΛCDM (0.29, 0.72): 18.195 against the printed 18.24.
    - ΛCDM (0.32, 0.91): 19.225 against 19.30.
    - XCDM (0.29, −1.04): 18.149 against 18.18.
    - XCDM (0.26, −1.30): 18.089 against 18.15.
  - The offset is not constant, so it is not a convention. One possibility is that Fig. 3's 18.24 was copied from Fig. 1's ΛCDM value of 18.24.
  - This affects no conclusion: every value is a good fit for 26 degrees of freedom.

**Effect on z_da = 0.74 ± 0.05.**
- Six printed values: mean 0.7365, sample sd 0.052, population sd 0.047.
- Replacing the two φCDM values with the continuous 0.7042 and 0.8063: mean 0.7357, sample sd 0.047, population sd 0.043. This is still 0.74 ± 0.05, or 0.74 ± 0.04 if the paper used the population sd, which the printed values cannot settle.
- Outside frozen scope and not certified: refitting all six continuously changes three more values.
  - ΛCDM: 0.7046 and 0.7836.
  - XCDM: 0.6950 and 0.7052. The 73.8-prior XCDM continuous best fit is (0.2646, −1.3098) with χ² = 18.048, against the printed (0.26, −1.30) and zda 0.718.
  - The result is mean 0.733, sd 0.049 (sample) or 0.044 (population), giving 0.73 ± 0.05. The headline value moves in its last digit, driven mostly by the XCDM [73.8] grid effect.

## 3. Prior art (short web search)

I found no published certified, formally verified or interval-arithmetic best fit of a cosmological data set, and nothing certified on this table.

Nearby work:
- Rigorous interval-arithmetic global maximum likelihood in phylogenetics (Sainudiin & Yoshida, "Applications of interval methods to phylogenetics", in *Algebraic Statistics for Computational Biology*).
- A Lean-verified BET adsorption analysis (AIChE 2023 abstract).
- Lean interval-arithmetic libraries (`girving/interval`, LeanCert).

Reanalyses of the same 28-point compilation by the same group exist: Farooq, Crandall & Ratra, arXiv:1305.1957, which bins the data, and Farooq et al. 2017, arXiv:1607.03537, which uses 38 points. Neither reports a continuous, non-gridded flat-law best fit for this table, as far as the search showed.

## Corrections

1. **Header, lines 23–25.** Replace "The paper does not state the integration range" with: "FR13 does not state it. The procedure it cites (Eq. 16 of Farooq, Mania & Ratra 2013, arXiv:1211.4253) integrates over H₀ ∈ (0, ∞), and over that range the integral changes by a relative amount of about 2·10⁻⁷⁹³ [4·10⁻⁸⁷⁰], not proved." Keeping "below 10⁻¹⁰⁰" is also acceptable.
2. **Citation, in the brief, annex and source map if they carry it.** "Eq. 18 of Farooq et al. 2013" is arXiv:1211.4253, not arXiv:1212.4264, which is Farooq & Ratra 2012 and has 7 equations. Also record that Eq. 18 as printed carries a spurious factor √2, a −ln 2 shift in χ². The frozen definition follows Eq. 16, which is the normalisation consistent with the printed 20.64.
3. **Header, lines 11–13.** Add that the printed Ω = 0.29 [0.25] and zda = 0.698 [0.817] are 0.01-grid values (zda(0.29) = 0.6981 and zda(0.25) = 0.8171 exactly). The frozen zda intervals therefore exclude the printed 0.698 and 0.817 on purpose: the certified continuous values are 0.7042 and 0.8063.
4. **Header.** Add that the printed χ²_min = 18.24 is not reproduced: the definition gives 18.205 at Ω = 0.29 and 18.199 at the minimiser, and no natural convention closes the gap. The printed 20.64 is reproduced (20.637 at Ω = 0.25).
5. **Optional, header.** Say that the identification of these statements with the paper's φCDM best fit relies on the paper's claim that the 2-D (Ωm0, α) best fit lies on α = 0, which is not certified here.
6. **Optional, statement extension.** Add uniqueness of the minimiser. Numerics show a single sign change of F′ on [0, 1].
