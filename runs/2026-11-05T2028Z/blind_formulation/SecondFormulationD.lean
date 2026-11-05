import Checked.Cosmography.FREta
import Checked.Cosmography.BambaAngular
import Checked.Fidelity.FriedmannLCDM
namespace Checked.Trust.SecondFormulation
open Checked.Cosmography

/-- "x rounded to `k` decimals is `d`": `x` lies within half a unit of the `k`-th decimal place
of `d`, i.e. `|x - d| ≤ (1/2)·10^(-k)`, boundary included. -/
def RoundsTo (x d : ℝ) (k : ℕ) : Prop :=
  |x - d| ≤ (1 / 2) * (1 / (10 : ℝ) ^ k)

/-- Scale factor of the flat bouncing model `H² = 4/9 - (4/9) a⁻³`, `a(0) = 1`, even in `t`.
Derivation: put `u = a^{3/2}`; then `H = (2/3) u̇/u`.  With `u = cosh t`,
`H² = (4/9) tanh² t = (4/9)(1 - 1/cosh² t) = 4/9 - (4/9) a⁻³`.  So `a = (cosh t)^(2/3)`. -/
noncomputable def coshBounce : ℝ → ℝ := fun t => (Real.cosh t) ^ ((2 : ℝ) / 3)

/-- `η₂₀ = F″(R₀) H₀⁴ / F(R₀)`.  From (11.21),(11.23): `F = -6H₀²(𝒫₀Ω+𝒬₀)/ℛ`,
`F″ = -(𝒫₂Ω+𝒬₂)/(6H₀²ℛ)`, so `F″H₀⁴/F = (𝒫₂Ω+𝒬₂)/(36(𝒫₀Ω+𝒬₀))` (ℛ and H₀ cancel). -/
noncomputable def eta20Of (Ω q j s l : ℝ) : ℝ :=
  (FRCosmo.P2 q j s * Ω + FRCosmo.Q2 q j s) /
    (36 * (FRCosmo.P0 q j s l * Ω + FRCosmo.Q0 q j s l))

/-- `η₃₀ = F‴(R₀) H₀⁶ / F(R₀)`.  From (11.21),(11.24): `F‴ = -(𝒫₃Ω+𝒬₃)/(36H₀⁴(j₀-q₀-2)ℛ)`,
so `F‴H₀⁶/F = (𝒫₃Ω+𝒬₃)/(216 (j₀-q₀-2)(𝒫₀Ω+𝒬₀))`. -/
noncomputable def eta30Of (Ω q j s l : ℝ) : ℝ :=
  (FRCosmo.P3 q j s l * Ω + FRCosmo.Q3 q j s l) /
    (216 * (j - q - 2) * (FRCosmo.P0 q j s l * Ω + FRCosmo.Q0 q j s l))

/-- `j₀ - q₀ - 2` on the family `(q,j) = (1+ε)(qL Ω, jL)`. -/
noncomputable def Jfam (Ω ε : ℝ) : ℝ :=
  (1 + ε) * FREta.jL - (1 + ε) * FREta.qL Ω - 2

/-- Remainder of `H₀ d_A` after the `y`-series through `y⁴`:
`H₀ d_A - y (1 + 𝒟¹y + 𝒟²y² + 𝒟³y³ + 𝒟⁴y⁴)`, all coefficients evaluated at `t₀`. -/
noncomputable def remA (D3 : ℝ → ℝ → ℝ → ℝ → ℝ) (D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * BambaA.angDist K a t₀ t
    - BambaY.yred a t₀ t * (1
      + BambaA.DA1 (decel a t₀) * BambaY.yred a t₀ t
      + BambaA.DA2 (decel a t₀) (Aviles.cosmoCoeff 3 a t₀) (BambaK.omega0 K a t₀) * BambaY.yred a t₀ t ^ 2
      + D3 (decel a t₀) (Aviles.cosmoCoeff 3 a t₀) (Aviles.cosmoCoeff 4 a t₀) (BambaK.omega0 K a t₀) * BambaY.yred a t₀ t ^ 3
      + D4 (decel a t₀) (Aviles.cosmoCoeff 3 a t₀) (Aviles.cosmoCoeff 4 a t₀) (Aviles.cosmoCoeff 5 a t₀)
          (BambaK.omega0 K a t₀) * BambaY.yred a t₀ t ^ 4)

/-- The correct denominator ℛ of the F(R) cosmography system.  Derived (sympy) by taking, with
`F′(R₀)=1`, `F⁽⁴⁾=0`, `R=-6(Ḣ+2H²)`, `ρ_M=3H₀²Ω a⁻³`, `Ḣ=-H²(1+q)`, `Ḧ=H³(j+3q+2)`,
`H⃛=-H⁴(4j+3q²+12q-s+6)`, `H⁗=H⁵(10jq+20j+l+30q²+60q-5s+24)`: eq. (11.1) at `t₀`, (11.5) at `t₀`
and d/dt of (11.5) at `t₀`.  This is a linear system in `(F, F″, F‴)`; its determinant is
`-108 (q+2-j)·(…)`; ℛ is the factor `(…)` normalised so that the coefficient of `l₀` is `j₀-q₀-2`.
Then `F/(6H₀²) = -N₀/ℛ`, `6H₀²F″ = -N₂/ℛ`, `36H₀⁴(j₀-q₀-2)F‴ = -N₃/ℛ`; checked on flat ΛCDM
(`N₂=N₃=0` and `F=R+2Λ`). -/
noncomputable def correctR (q j s l : ℝ) : ℝ :=
  j * l - l * q - 2 * l - 3 * j ^ 2 * q - 10 * j ^ 2 - 11 * j * q ^ 2 - 4 * j * q + 2 * j * s
    + 18 * j - 3 * q ^ 4 - 34 * q ^ 3 - 6 * q ^ 2 * s - 180 * q ^ 2 - 50 * q * s - 246 * q
    - 3 * s ^ 2 - 40 * s - 104

end Checked.Trust.SecondFormulation
