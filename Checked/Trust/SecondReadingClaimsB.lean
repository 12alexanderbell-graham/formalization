import Mathlib.Data.Real.Basic

namespace Checked.Trust.SecondReading

/-- Bamba–Capozziello–Nojiri–Odintsov, arXiv:1205.3421 (v1 p.107, v2 p.108, v3 p.110), Eq. (10.38):
d_L(z) = (c z / H₀) { 𝒟⁰_L + 𝒟¹_L z + 𝒟²_L z² + 𝒟³_L z³ + 𝒟⁴_L z⁴ + O(z⁵) }.
Prefactor power of z = 1. -/
def bambaDLzPrefactor : ℕ := 1

/-- Same source, Eqs. (10.38)–(10.44): highest printed power of z inside the braces (𝒟⁴_L z⁴; O(z⁵) not counted). -/
def bambaDLzLast : ℕ := 4

/-- Same source (v1 p.107, v2 p.108, v3 p.110), Eq. (10.45):
d_A(z) = (c z / H₀) { 𝒟⁰_A + 𝒟¹_A z + 𝒟²_A z² + 𝒟³_A z³ + 𝒟⁴_A z⁴ + O(z⁵) }. Prefactor power of z = 1. -/
def bambaDAzPrefactor : ℕ := 1

/-- Same source, Eqs. (10.45)–(10.51): highest printed power inside the braces = 4. -/
def bambaDAzLast : ℕ := 4

/-- Same source (v1 p.108, v2 p.109, v3 p.111), Eqs. (10.52)–(10.57): only coefficients 𝒟⁰_{L,y}..𝒟⁴_{L,y}
are printed; the series in y = z/(1+z) itself is NOT printed. Implied: d_L = (c y/H₀){Σ_{n=0}^4 𝒟ⁿ_{L,y} yⁿ}
(prefactor y¹; checked against 𝒟¹_{L,y} = −½(−3+q₀) = (3−q₀)/2). -/
def bambaDLyPrefactor : ℕ := 1

/-- Same source, Eqs. (10.52)–(10.57): highest index of a printed coefficient = 4. -/
def bambaDLyLast : ℕ := 4

/-- Same source (v1 p.108, v2 p.109, v3 p.111), Eqs. (10.58)–(10.63): only coefficients printed; implied
d_A = (c y/H₀){Σ_{n=0}^4 𝒟ⁿ_{A,y} yⁿ} (checked: 𝒟¹_{A,y} = −½(1+q₀)). -/
def bambaDAyPrefactor : ℕ := 1

/-- Same source, Eqs. (10.58)–(10.63): highest index of a printed coefficient = 4. -/
def bambaDAyLast : ℕ := 4

/-- Same source (v1 p.111, v2 p.113, v3 p.114), Eq. (11.13), identical in v1–v3:
d³R₀/dt³ = −6H₀⁵ [l₀ − s₀ + 2(q₀+4)j₀ − 6(3q₀+8)q₀ − 24]. -/
noncomputable def bambaR3 (H q j s l : ℝ) : ℝ :=
  -6 * H ^ 5 * (l - s + 2 * (q + 4) * j - 6 * (3 * q + 8) * q - 24)

/-- Same source (v1 p.113, v2 p.114, v3 p.116), Eq. (11.21):
F(R₀)/(6H₀²) = − (𝒫₀(q₀,j₀,s₀,l₀) Ω_M + 𝒬₀(q₀,j₀,s₀,l₀)) / ℛ(q₀,j₀,s₀,l₀).
Normalisation constant c = 6. -/
noncomputable def bambaF0Norm : ℝ := 6

/-- Eq. (11.21): power of H₀ in the denominator of the left-hand side (6H₀²) = 2. -/
def bambaF0HPow : ℕ := 2

/-- Eq. (11.21): overall sign on the right-hand side = −1. -/
noncomputable def bambaF0Sign : ℝ := -1

end Checked.Trust.SecondReading
