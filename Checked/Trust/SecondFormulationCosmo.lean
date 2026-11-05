import Mathlib.Data.Real.Basic
import Checked.Trust.SecondReading
import Checked.Trust.SecondReadingFR

/-!
# Blind second formulation of FORMULA definitions (trust track T2/T3, run 2026-11-05T0828Z)

Copied verbatim (by script) from `runs/2026-11-05T0828Z/blind/SecondFormulationCosmo.lean`, written by subagent
B (cosmography series coefficients and templates; brief `runs/2026-11-05T0828Z/blind/briefB.md`, derivation `runs/2026-11-05T0828Z/blind/derive_cosmo.py`), which did not read the program's definitions: it was given only each definition's name,
argument order and the quantity the name promises, and derived the formula itself.
`Checked/Trust/Formulations.lean` proves each program definition equal to its second formulation
(red team J, defects d03 and d06: a FORMULA definition's name and constants were unchecked).
-/

namespace Checked.Trust.SecondFormulation

/-- the z⁴ coefficient D⁴ of the lookback time H₀(t₀−t) in z; derived by sympy in derive_cosmo.py. -/
noncomputable def correctD4 (q j s l : ℝ) : ℝ :=
  7 / 8 * q ^ 4 + 5 / 2 * q ^ 3 - 7 / 8 * j * q ^ 2 + 3 * q ^ 2
     + 1 / 12 * j ^ 2 - 5 / 3 * j * q - 1 / 8 * q * s
     - j + 2 * q - 1 / 6 * s
     - 1 / 120 * l + 1

/-- The truncated lookback series z(1 + D¹z + D²z² + D³z³ + d4·z⁴) with the printed D¹, D², D³; derived by sympy in derive_cosmo.py (series shape from the brief). -/
noncomputable def series (d4 q j s z : ℝ) : ℝ :=
  z * (1 + Checked.Trust.SecondReading.D1 q * z + Checked.Trust.SecondReading.D2 q j * z ^ 2
    + Checked.Trust.SecondReading.D3 q j s * z ^ 3 + d4 * z ^ 4)

/-- the y² coefficient of the luminosity distance d_L in y (curved, Ω = 1 + K/(H₀²a₀²)); derived by sympy in derive_cosmo.py. -/
noncomputable def correctD2y (q j Ω : ℝ) : ℝ :=
  1 / 2 * q ^ 2 - 5 / 6 * q - 1 / 6 * Ω - 1 / 6 * j
     + 2

/-- The truncated y-series y(1 + D¹y + d2·y²) with the printed D¹ of d_L; derived by sympy in derive_cosmo.py (D¹ = (3 − q)/2 confirmed there). -/
noncomputable def seriesY (d2 q y : ℝ) : ℝ :=
  y * (1 + Checked.Trust.SecondReading.D1y q * y + d2 * y ^ 2)

/-- the y³ coefficient of d_L in y (curved); derived by sympy in derive_cosmo.py. -/
noncomputable def correctD3y (q j s Ω : ℝ) : ℝ :=
  -5 / 8 * q ^ 3 + 7 / 8 * q ^ 2 + 1 / 4 * Ω * q + 5 / 12 * j * q
     - 7 / 24 * j - 5 / 12 * Ω - 4 / 3 * q
     + 1 / 24 * s + 5 / 2

/-- the y⁴ coefficient of d_L in y (curved); derived by sympy in derive_cosmo.py. -/
noncomputable def correctD4y (q j s l Ω : ℝ) : ℝ :=
  7 / 8 * q ^ 4 - 9 / 8 * q ^ 3 - 7 / 8 * j * q ^ 2 - 3 / 8 * Ω * q ^ 2
     + 1 / 12 * j ^ 2 + 1 / 120 * Ω ^ 2 + 31 / 20 * q ^ 2
     - 1 / 8 * q * s + 1 / 12 * Ω * j + 2 / 3 * Ω * q
     + 3 / 4 * j * q - 39 / 20 * q - 29 / 40 * Ω
     - 19 / 40 * j - 1 / 120 * l + 3 / 40 * s
     + 3

/-- The truncated y-series y(1 + D¹y + d2y² + d3y³ + d4y⁴) with the printed D¹ of d_L; derived by sympy in derive_cosmo.py (series shape from the brief). -/
noncomputable def seriesY4 (q d2 d3 d4 y : ℝ) : ℝ :=
  y * (1 + Checked.Trust.SecondReading.D1y q * y + d2 * y ^ 2 + d3 * y ^ 3 + d4 * y ^ 4)

/-- the y³ coefficient of the angular-diameter distance d_A in y (curved); derived by sympy in derive_cosmo.py. -/
noncomputable def correctDA3 (q j s Ω : ℝ) : ℝ :=
  -5 / 8 * q ^ 3 - 1 / 8 * q ^ 2 + 1 / 4 * Ω * q + 5 / 12 * j * q
     - 1 / 6 * q - 1 / 12 * Ω + 1 / 24 * j
     + 1 / 24 * s

/-- the y⁴ coefficient of d_A in y (curved); derived by sympy in derive_cosmo.py. -/
noncomputable def correctDA4 (q j s l Ω : ℝ) : ℝ :=
  7 / 8 * q ^ 4 + 1 / 8 * q ^ 3 - 7 / 8 * j * q ^ 2 - 3 / 8 * Ω * q ^ 2
     + 1 / 12 * j ^ 2 + 1 / 120 * Ω ^ 2 + 3 / 10 * q ^ 2
     - 1 / 8 * q * s - 1 / 12 * j * q + 1 / 6 * Ω * q
     + 1 / 12 * Ω * j - 7 / 60 * q - 7 / 120 * Ω
     - 7 / 120 * j - 1 / 120 * l - 1 / 120 * s
    

/-- the z⁴ coefficient of d_L in z (curved, k = K/(H₀²a₀²)); derived by sympy in derive_cosmo.py. -/
noncomputable def correctDL4z (q j s l k : ℝ) : ℝ :=
  7 / 8 * q ^ 4 + 11 / 8 * q ^ 3 - 7 / 8 * j * q ^ 2 - 3 / 8 * k * q ^ 2
     + 1 / 12 * j ^ 2 + 1 / 120 * k ^ 2 + 27 / 40 * q ^ 2
     - 11 / 12 * j * q - 1 / 3 * k * q - 1 / 8 * q * s
     + 1 / 12 * j * k - 11 / 120 * s - 9 / 40 * j
     - 1 / 24 * k - 1 / 120 * l + 1 / 20 * q
     - 1 / 20

/-- the z⁴ coefficient of d_A in z (curved); derived by sympy in derive_cosmo.py. -/
noncomputable def correctDA4z (q j s l k : ℝ) : ℝ :=
  7 / 8 * q ^ 4 + 21 / 8 * q ^ 3 - 7 / 8 * j * q ^ 2 - 3 / 8 * k * q ^ 2
     + 1 / 12 * j ^ 2 + 1 / 120 * k ^ 2 + 137 / 40 * q ^ 2
     - 7 / 4 * j * q - 5 / 6 * k * q - 1 / 8 * q * s
     + 1 / 12 * j * k - 137 / 120 * j - 17 / 24 * k
     - 7 / 40 * s - 1 / 120 * l + 163 / 60 * q
     + 137 / 60

/-- The truncated series z(1 + d1 z + d2 z² + d3 z³ + d4 z⁴); derived by sympy in derive_cosmo.py (series shape from the brief). -/
noncomputable def seriesZ (d1 d2 d3 d4 z : ℝ) : ℝ :=
  z * (1 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)

/-- the y² coefficient of the deceleration distance d_Q = d_L/(1+z)^{3/2} in y (curved); derived by sympy in derive_cosmo.py. -/
noncomputable def correctQ2 (q j Ω : ℝ) : ℝ :=
  1 / 2 * q ^ 2 - 1 / 6 * Ω - 1 / 6 * j - 1 / 12 * q
     + 1 / 8

/-- The truncated series y(1 − (q/2)·y + d2·y²) for d_Q; derived by sympy in derive_cosmo.py (the y¹ coefficient −q/2 confirmed there). -/
noncomputable def seriesQ (d2 q y : ℝ) : ℝ :=
  y * (1 - (q / 2) * y + d2 * y ^ 2)

/-- the ε-derivative at ε=0 of η₂₀ on the ΛCDM-scaled family (F(R) ratio); derived by sympy in derive_cosmo.py. -/
noncomputable def correct20 (Ω : ℝ) : ℝ :=
  (-54*Ω^2 - 48*Ω + 64) / (27*Ω*(Ω - 2)*(27*Ω^2 + 60*Ω + 112))

/-- the ε-derivative at ε=0 of η₃₀ on the ΛCDM-scaled family (F(R) ratio); derived by sympy in derive_cosmo.py. -/
noncomputable def correct30 (Ω : ℝ) : ℝ :=
  (-162*Ω^2 + 120*Ω + 32) / (243*Ω^2*(Ω - 2)*(27*Ω^2 + 60*Ω + 112))

end Checked.Trust.SecondFormulation
