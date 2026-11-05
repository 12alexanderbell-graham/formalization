import Mathlib

/-!
# Blind restatement: Moresco et al. 2016 (arXiv:1601.01701v2), Sec. 5.2, Tables 4-5

Modelling choices.
* Model: open LCDM, Eq. 5.1, `H(z) = H0 * sqrt(Om (1+z)^3 + Ok (1+z)^2 + OL)`, `Ok = 1 - Om - OL`.
* Parametrisation: `(H0, Om, zt)` as in the paper's priors; `OL = Om (1+zt)^3 / 2`
  (inverse of Eq. 5.2, `zt = (2 OL/Om)^(1/3) - 1`). (For Om = 0 this gives OL = 0; fine.)
* Prior region: `H0 > 0` (the Gaussian prior has unbounded support; only positivity of H0 is imposed),
  `Om in [0,1]`, `zt in [0,1.5]` (uniform priors, Sec. 5.2).
* Domain condition: the fit region additionally requires `E^2(z_i) > 0` at all 30 data redshifts, so
  `Real.sqrt` is never applied to a nonpositive number and no junk value 0 enters chi^2.
  No division by zero occurs (all sigma_i > 0 and the H0 prior width is 2.4).
* chi^2 = sum_i ((H_i - H(z_i))/sigma_i)^2 + ((H0 - 73)/2.4)^2 : i.e. -2 ln L, no additive constant.
  H0 prior: 73 +- 2.4 km/s/Mpc (Sec. 5.2).
* Claim A is phrased as: the set of attained chi^2 values over the (nonempty) valid region has
  greatest lower bound `L` (`IsGLB`), with `|L - 14.967| <= 0.0005`. IsGLB of an empty set is
  impossible, so junk sInf = 0 cannot satisfy it; nonemptiness is also stated explicitly.
* Claim B: k = 3 free parameters (H0, Om, zt); AICc = chi2 + 2k + 2k(k+1)/(N-k-1) (Eqs 5.3, 5.4,
  with -2 ln Lmax = chi2). Table 5 prints AICc = 21.41 for oLCDM; tolerance 0.005 (rounding of the
  printed 2-decimal value). N range: integers 5 <= N <= 50 (N > k+1 = 4 needed for the formula;
  the natural values are N = 30 data points or 31 counting the H0 point; 50 is a generous cap).
  NOTE: with chi2 = 14.967 and k = 3 the printed 21.41 would need N ~ 58, outside this range, so
  the claim is about "reasonable" N only. The claim is over all valid parameter values (not just
  the minimiser), which is stronger than just the minimum.
* Transcription: Table 4 copied by hand from the PDF (z, H, sigma in the two column blocks, merged
  in order of z). Check: a numerical minimisation (outside Lean, scipy) of this chi^2 over the prior
  region gives 14.96704 at (H0, Om, zt) ~ (72.29, 0.436, 0.651), reproducing the 14.967 in claim A
  and a zt consistent with the printed 0.64 (+0.1 -0.06) in Table 5.
-/

namespace Work.Data.Moresco16MinBlind

/-- Table 4 redshifts. -/
noncomputable def zD : Fin 30 → ℝ := ![0.07, 0.09, 0.12, 0.17, 0.179, 0.199, 0.20, 0.27, 0.28,
  0.352, 0.3802, 0.4, 0.4004, 0.4247, 0.44497, 0.4783, 0.48, 0.593, 0.68, 0.781, 0.875, 0.88,
  0.9, 1.037, 1.3, 1.363, 1.43, 1.53, 1.75, 1.965]

/-- Table 4 H(z) values. -/
noncomputable def HD : Fin 30 → ℝ := ![69.0, 69, 68.6, 83, 75, 75, 72.9, 77, 88.8, 83, 83, 95, 77,
  87.1, 92.8, 80.9, 97, 104, 92, 105, 125, 90, 117, 154, 168, 160, 177, 140, 202, 186.5]

/-- Table 4 uncertainties. -/
noncomputable def sD : Fin 30 → ℝ := ![19.6, 12, 26.2, 8, 4, 5, 29.6, 14, 36.6, 14, 13.5, 17, 10.2,
  11.2, 12.9, 9, 62, 13, 8, 12, 17, 40, 23, 20, 17, 33.6, 18, 14, 40, 50.4]

/-- Dark-energy density from `(Om, zt)` (inverse of Eq. 5.2). -/
noncomputable def OL (Om zt : ℝ) : ℝ := Om * (1 + zt) ^ 3 / 2

/-- `E(z)^2 = (H/H0)^2` of Eq. 5.1. -/
noncomputable def E2 (Om zt z : ℝ) : ℝ :=
  Om * (1 + z) ^ 3 + (1 - Om - OL Om zt) * (1 + z) ^ 2 + OL Om zt

/-- The fit region: paper priors plus positivity of `E^2` at every data redshift. -/
def Valid (p : ℝ × ℝ × ℝ) : Prop :=
  0 < p.1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ 1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ 3 / 2 ∧
    ∀ i, 0 < E2 p.2.1 p.2.2 (zD i)

/-- chi^2 = -2 ln L (no constant), including the Gaussian H0 prior 73 ± 2.4. -/
noncomputable def chi2 (p : ℝ × ℝ × ℝ) : ℝ :=
  (∑ i, ((HD i - p.1 * Real.sqrt (E2 p.2.1 p.2.2 (zD i))) / sD i) ^ 2) + ((p.1 - 73) / 2.4) ^ 2

/-- AICc of Eqs. 5.3-5.4 with `-2 ln Lmax = c`, `k` parameters, `N` data points. -/
noncomputable def AICc (c : ℝ) (k N : ℕ) : ℝ :=
  c + 2 * k + 2 * k * (k + 1) / ((N : ℝ) - k - 1)

/-- (A) The infimum of chi^2 over the valid region exists, region nonempty, equals 14.967 ± 0.0005. -/
theorem claimA :
    (chi2 '' {p | Valid p}).Nonempty ∧
    ∃ L : ℝ, IsGLB (chi2 '' {p | Valid p}) L ∧ |L - 14.967| ≤ 0.0005 := by
  sorry

/-- (B) Printed AICc 21.41 (k = 3, tolerance 0.005) is not attained by any valid parameters
for any N in 5..50. -/
theorem claimB :
    ∀ p, Valid p → ∀ N : ℕ, 5 ≤ N → N ≤ 50 →
      0.005 < |AICc (chi2 p) 3 N - 21.41| := by
  sorry

end Work.Data.Moresco16MinBlind
