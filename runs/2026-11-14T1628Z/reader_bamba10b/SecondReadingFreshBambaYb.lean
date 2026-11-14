import Mathlib.Data.Real.Basic
/-! An independent reader transcribed, from the typeset page images, coefficients of the
y-redshift series (y = z / (1 + z)) of the luminosity distance and of the angular diameter
distance in Section X (cosmography) of K. Bamba, S. Capozziello, S. Nojiri, S. D. Odintsov,
"Dark energy cosmology: the equivalent description via different theoretical models and
cosmography tests", 2012, arXiv:1205.3421v3 [gr-qc] 18 Jul 2012 (as printed in the left margin
of the first page). Equations read: (10.54), (10.55), (10.56)-(10.57), (10.61), (10.62)-(10.63).
All coefficients are copied as printed, without correction. -/
namespace Checked.Trust.SecondReading
/-- Bamba, Capozziello, Nojiri, Odintsov 2012, equation (10.54), PDF page 111. Symbol: the
script D with upper index 2 and lower index L,y. It is the coefficient of y^2 in the
y-redshift series of the luminosity distance, in terms of q = q0, j = j0 and Ω = Ω0.
Printed as minus one sixth times a parenthesis. No reading difficulty. -/
noncomputable def bambaYReadDL2 (q j Ω : ℝ) : ℝ :=
  -(1 / 6) * (12 - 5 * q + 3 * q ^ 2 - j - Ω)
/-- Bamba, Capozziello, Nojiri, Odintsov 2012, equation (10.55), PDF page 111. Symbol: the
script D with upper index 3 and lower index L,y. It is the coefficient of y^3 in the
y-redshift series of the luminosity distance, in terms of q = q0, j = j0, s = s0 and
Ω = Ω0. Printed as one twenty-fourth times a square-bracketed sum. No reading difficulty. -/
noncomputable def bambaYReadDL3 (q j s Ω : ℝ) : ℝ :=
  (1 / 24) * (52 - 20 * q + 21 * q ^ 2 - 15 * q ^ 3 - 7 * j + 10 * q * j + s
    - 2 * Ω * (1 + 3 * q))
/-- Bamba, Capozziello, Nojiri, Odintsov 2012, equations (10.56) and (10.57) (one
displayed formula over two lines), PDF page 111. Symbol: the script D with upper index 4
and lower index L,y. It is the coefficient of y^4 in the y-redshift series of the
luminosity distance, in terms of q = q0, j = j0, s = s0, l = l0 and Ω = Ω0. Printed as
one one-hundred-twentieth times a square-bracketed sum. Reading choices: the first line
ends with a plus sign after 15 q0 s0 and the second line begins with a minus sign before
57 j0; I read the term as minus 57 j0 (the trailing plus sign is a line-break sign).
The term 10 j^2 is printed with j and no subscript 0; I read it as j squared with j = j0,
and the printed square is on the j. Suspected misprint: the missing subscript only. -/
noncomputable def bambaYReadDL4 (q j s l Ω : ℝ) : ℝ :=
  (1 / 120) * (359 - 184 * q + 186 * q ^ 2 - 135 * q ^ 3 + 105 * q ^ 4 + 90 * q * j
    - 105 * q ^ 2 * j - 15 * q * s - 57 * j + 10 * j ^ 2 + 9 * s - l
    - 5 * Ω * (17 - 6 * q + 9 * q ^ 2 - 2 * j))
/-- Bamba, Capozziello, Nojiri, Odintsov 2012, equation (10.61), PDF page 111. Symbol: the
script D with upper index 3 and lower index A,y. It is the coefficient of y^3 in the
y-redshift series of the angular diameter distance, in terms of q = q0, j = j0, s = s0 and
Ω = Ω0. Printed as minus one twenty-fourth times a parenthesis. No reading difficulty. -/
noncomputable def bambaYReadDA3 (q j s Ω : ℝ) : ℝ :=
  -(1 / 24) * (-2 * q + 3 * q ^ 2 + 15 * q ^ 3 - j - 10 * q * j - s + 2 * Ω)
/-- Bamba, Capozziello, Nojiri, Odintsov 2012, equations (10.62) and (10.63) (one
displayed formula over two lines), PDF page 111. Symbol: the script D with upper index 4
and lower index A,y. It is the coefficient of y^4 in the y-redshift series of the angular
diameter distance, in terms of q = q0, j = j0, s = s0, l = l0 and Ω = Ω0. Printed as minus
one one-hundred-twentieth times a parenthesis. Reading choices: the first line ends with a
plus sign after 15 q0 s0 and the second line begins with a minus sign before 3 j0; I read
the term as minus 3 j0. The term 10 j^2 is printed with j and no subscript 0; I read it as
j squared with j = j0. Suspected misprint: the missing subscript only. -/
noncomputable def bambaYReadDA4 (q j s l Ω : ℝ) : ℝ :=
  -(1 / 120) * (1 - 6 * q + 9 * q ^ 2 - 15 * q ^ 3 - 105 * q ^ 4 + 10 * q * j
    + 105 * q ^ 2 * j + 15 * q * s - 3 * j - 10 * j ^ 2 + s + l + 5 * Ω)
end Checked.Trust.SecondReading
