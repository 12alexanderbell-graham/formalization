import Mathlib.Data.Real.Basic
/-! Second, blind reading by an independent reader of one printed coefficient in S. Capozziello, V. F. Cardone, V. Salzano, Cosmography of f(R) gravity, 2008, arXiv:0802.1583 version 2 (downloaded as version 2). The equation read is the coefficient D⁴_z of the series (A2) in Appendix A, transcribed from the typeset image of the PDF page. -/
namespace Checked.Trust.SecondReading
/-- Capozziello, Cardone, Salzano, arXiv:0802.1583v2, Appendix A, the list of coefficients following Eq. (A2), read on PDF page 16. The paper writes it as a calligraphic D with superscript 4 and subscript z. It is the coefficient of z to the fourth power in the series of the distance D(z) in the redshift z, in terms of q₀ (deceleration), j₀ (jerk), s₀ (snap) and l₀ (lerk); here q = q₀, j = j₀, s = s₀, l = l₀. Printed on three lines: 1 + 2q₀ + 3q₀² + (5/2)q₀³ + (7/2)q₀⁴ on the first line; then a leading minus sign, (5/3)q₀j₀, minus (7/8)q₀²j₀, minus j₀, plus j₀²/12 on the second; then a leading minus sign, (1/8)q₀s₀, minus s₀/6, minus l₀/120 on the third. Reading choice: the minus signs that start the second and third lines are taken as binary minus signs continuing the sum, so the whole expression is one sum. No symbol was uncertain and no misprint is suspected. -/
noncomputable def ccs08PrintedD4z (q j s l : ℝ) : ℝ :=
  1 + 2 * q + 3 * q ^ 2 + (5 / 2) * q ^ 3 + (7 / 2) * q ^ 4
    - (5 / 3) * q * j - (7 / 8) * q ^ 2 * j - j + j ^ 2 / 12
    - (1 / 8) * q * s - s / 6 - l / 120
end Checked.Trust.SecondReading
