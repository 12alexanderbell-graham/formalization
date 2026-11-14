import Mathlib.Data.Real.Basic
/-! An independent reader transcribed, from the typeset pages of the PDF, several formulas
of Section XI (testing F(R) gravity by cosmography) of K. Bamba, S. Capozziello, S. Nojiri,
S. D. Odintsov, "Dark energy cosmology: the equivalent description via different theoretical
models and cosmography tests", 2012, arXiv:1205.3421 version 3. The equations read are
(11.25), (11.26), (11.31), (11.39), (11.42) and (11.43). Nothing was corrected: every
coefficient is as printed. -/
namespace Checked.Trust.SecondReading
/-- Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421v3, Eq. (11.25), PDF page 116.
Symbol: script P with subscript 0. It is the polynomial in the cosmographic parameters
q0, j0, s0, l0 that multiplies the matter density parameter in the numerator of F(R0)/(6 H0^2)
in Eq. (11.21). Arguments: q = q0, j = j0, s = s0, l = l0. Reading choice: the printed
formula is split over two lines; the first line ends with a plus sign and the second line
begins with a minus sign before the square bracket, which I read as a single minus sign
(subtraction of the bracket times j0). The last bracket is printed with round parentheses. -/
noncomputable def bamba12PrintedP0 (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s
    - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j
    - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)
/-- Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421v3, Eq. (11.26), PDF page 116.
Symbol: script Q with subscript 0. It is the polynomial in q0, j0, s0, l0 that is added to
the term with the matter density parameter in the numerator of F(R0)/(6 H0^2) in Eq. (11.21).
Arguments: q = q0, j = j0, s = s0, l = l0. Reading choice: the printed formula is split over
three lines; each line break repeats a plus sign (a line ends with plus and the next begins
with plus), which I read as a single plus sign. -/
noncomputable def bamba12PrintedQ0 (q j s l : ℝ) : ℝ :=
  (q ^ 2 - j * q + 2 * q) * l
    + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s
    + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j
    + 3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64
/-- Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421v3, Eq. (11.31), PDF page 116.
Symbol: script R. It is the common denominator polynomial in q0, j0, s0, l0 of the
expressions for F(R0)/(6 H0^2), the second derivative and (times j0 - q0 - 2) the third
derivative of F in Eqs. (11.21), (11.23), (11.24). Arguments: q = q0, j = j0, s = s0, l = l0.
Reading choices: the printed formula is split over two lines, the first ending with a plus
sign and the second beginning with a plus sign, read as a single plus. The last bracket is
printed as 3 q0^4 + 34 q0^3 + 246 q0 + 104 with no q0^2 term; I kept it as printed
(possible misprint, not corrected). -/
noncomputable def bamba12PrintedR (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    + ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q + 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 246 * q + 104)
/-- Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421v3, Eq. (11.39), first line, PDF
page 120. Symbol: q0 (deceleration parameter today) in the LCDM model, printed as
1/2 - (3/2)(1 - Omega_M^(0)). Argument: Ω = the matter density parameter Omega_M^(0).
No reading difficulty. -/
noncomputable def bamba12LCDMq0 (Ω : ℝ) : ℝ :=
  1 / 2 - (3 / 2) * (1 - Ω)
/-- Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421v3, Eq. (11.39), fourth line, PDF
page 120. Symbol: l0 (the lerk, fourth cosmographic parameter today) in the LCDM model,
printed as 1 + 3 Omega_M^(0) + (27/2)(Omega_M^(0))^2. Argument: Ω = the matter density
parameter Omega_M^(0). No reading difficulty. -/
noncomputable def bamba12LCDMl0 (Ω : ℝ) : ℝ :=
  1 + 3 * Ω + (27 / 2) * Ω ^ 2
/-- Bamba, Capozziello, Nojiri, Odintsov, arXiv:1205.3421v3, Eqs. (11.42) and (11.43), PDF
page 121. No single symbol: it is the polynomial printed as the denominator of the fraction
in both eta_20 and eta_30, namely [3(9 Omega + 74) Omega - 556] Omega^2 + 16 with Omega the
matter density parameter Omega_M^(0). Argument: Ω. The separate factors that multiply
epsilon (27 in (11.42), 243 Omega^2 in (11.43)) are not included. No reading difficulty. -/
noncomputable def bamba12PrintedEtaDen (Ω : ℝ) : ℝ :=
  (3 * (9 * Ω + 74) * Ω - 556) * Ω ^ 2 + 16
end Checked.Trust.SecondReading
