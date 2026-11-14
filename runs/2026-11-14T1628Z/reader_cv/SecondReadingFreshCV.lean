import Mathlib.Data.Real.Basic
/-! Second reading by an independent reader of C. Cattoën and M. Visser, Cosmographic Hubble fits to the supernova data, 2007, arXiv:0710.1887 version 1. The reading was taken from the typeset image of PDF page 13 and covers the y squared coefficient inside the braces of Eq. (59), the series for the deceleration distance d_Q in the y-redshift. -/
namespace Checked.Trust.SecondReading
/-- Cattoën and Visser, arXiv:0710.1887v1, Eq. (59), PDF page 13. The paper writes d_Q(y) = d_H y {1 - (q₀/2) y + (1/12) [3 - 2q₀ + 12 q₀² - 4(j₀ + Ω₀)] y² + O(y³)}. This is the whole printed y² term without the factor y²: the prefactor 1/12 times the bracket. Arguments: q for q₀, j for j₀, Ω for Ω₀. No reading choice was needed; all signs, the 12 on q₀² and the 4 on the sum j₀ + Ω₀ are clearly legible in a 2x crop. No misprint was suspected by the reader. -/
noncomputable def cv07PrintedQ2 (q j Ω : ℝ) : ℝ :=
  (1 / 12) * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))
end Checked.Trust.SecondReading
