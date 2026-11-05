import Mathlib.Data.Real.Basic

namespace Checked.Trust.SecondReading

/-- Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 v1 and v2 (identical),
Eq. (15), p. 10.  Printed: `l₀ = 1 + 3Ω_m − (27/2) Ω_m²`. -/
noncomputable def avilesL0 (Ω : ℝ) : ℝ := 1 + 3 * Ω - (27 / 2) * Ω ^ 2

/-- Aviles et al., arXiv:1204.2007 v1 and v2, Eq. (15), p. 10.
Printed: `m₀ = 1 − (27/2) Ω_m² − 81 Ω_m² − (81/2) Ω_m³` (two separate Ω_m² terms, exactly as printed). -/
noncomputable def avilesM0 (Ω : ℝ) : ℝ := 1 - (27 / 2) * Ω ^ 2 - 81 * Ω ^ 2 - (81 / 2) * Ω ^ 3

/-- Capozziello, Lazkoz, Salzano, PRD 84, 124061 (2011), arXiv:1104.3096 v1 and v2 (identical), Eq. (22), p. 4.
Printed: `l₀ = 35/2 + (1−Ω_m)/4 [213 + (7−Ω_m) w_a] w_a + (1−Ω_m)/4 [489 + 9(82 − 21Ω_m) w_a] w₀
 + (9/2)(1−Ω_m) [67 − 21Ω_m + (3/2)(23 − 11Ω_m) w_a] w₀² + (27/4)(1−Ω_m)(47 − 24Ω_m) w₀³
 + (81/2)(1−Ω_m)(3 − 2Ω_m) w₀⁴`. -/
noncomputable def clsL0 (Ω w₀ wₐ : ℝ) : ℝ :=
  35 / 2 + (1 - Ω) / 4 * (213 + (7 - Ω) * wₐ) * wₐ
    + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
    + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
    + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
    + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4

/-- Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583 v2 (Appendix A is absent in v1),
Eq. (A2), p. 15: `D(z) = (c z / H₀) {𝒟⁰_z + 𝒟¹_z z + 𝒟²_z z² + 𝒟³_z z³ + 𝒟⁴_z z⁴}`.
Power of z in the prefactor. -/
def ccsA2Prefactor : ℕ := 1

/-- Same, Eq. (A2): highest power of z inside the braces with a printed coefficient (𝒟⁴_z z⁴). -/
def ccsA2Last : ℕ := 4

/-- Cattoën & Visser, CQG 24, 5985 (2007), arXiv:0710.1887 v1 (only version), Eq. (59), p. 13:
`d_Q(y) = d_H y {1 − (q₀/2) y + (1/12)[3 − 2q₀ + 12q₀² − 4(j₀+Ω₀)] y² + O(y³)}`.
Power of y in the prefactor. -/
def cvdQ59Prefactor : ℕ := 1

/-- Same, Eq. (59): highest power of y inside the braces with a printed coefficient (y²; O(y³) excluded). -/
def cvdQ59Last : ℕ := 2

/-- Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017), arXiv:1609.09631 v1 and v2 (identical here),
Eq. (13), p. 3: `d_L(z) = (c z/H₀)(𝒟⁰_L + 𝒟¹_L z + 𝒟²_L z² + 𝒟³_L z³ + 𝒟⁴_L z⁴ + O(z⁵))`.
Power of z in the prefactor. -/
def demDLPrefactor : ℕ := 1

/-- Same, Eq. (13): highest power of z with a printed coefficient (𝒟⁴_L z⁴). -/
def demDLLast : ℕ := 4

/-- Same paper, Eq. (18), p. 3: `d_A(z) = (c z/H₀)(𝒟⁰_A + 𝒟¹_A z + 𝒟²_A z² + 𝒟³_A z³ + 𝒟⁴_A z⁴ + O(z⁵))`.
Power of z in the prefactor. -/
def demDAPrefactor : ℕ := 1

/-- Same, Eq. (18): highest power of z with a printed coefficient (𝒟⁴_A z⁴). -/
def demDALast : ℕ := 4

end Checked.Trust.SecondReading
