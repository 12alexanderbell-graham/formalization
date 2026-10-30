import Checked.Cosmography.BambaCurved

/-!
# Red-team: plausible but wrong luminosity-distance definitions

Each `rtN` has the signature of `Checked.Cosmography.BambaK.lumDist` and is *wrong* for at
least one admissible input (`a > 0` smooth, `t < t₀`). The docstring of each states the
error, the region where it nevertheless agrees with the true `d_L`, and a concrete
admissible witness with both values (`e = Real.exp 1`).

True value: `d_L = a(t₀) (1 + z) S_K(χ)`, `1 + z = a(t₀)/a(t)`, `χ = ∫_t^{t₀} ds/a(s)`.
-/

namespace Work.Fidelity.RedTeam

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.Transverse

/-- **Error:** drops the overall factor `a(t₀)` (silently assumes the normalization
`a(t₀) = 1`), i.e. `d_L = (1 + z) S_K(χ)`.
Agrees whenever `a(t₀) = 1` (any `K`). Differs whenever `a(t₀) ≠ 1` and `S_K(χ) ≠ 0`.
Witness: `K = 0`, `a s = 2 * exp s`, `t₀ = 0`, `t = -1` (`χ = (e-1)/2`, `1+z = e`):
true `d_L = e(e-1) ≈ 4.67077`, `rt1 = e(e-1)/2 ≈ 2.33539`. -/
noncomputable def rt1 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  (1 + redshift a t₀ t) * transverse K (comoving a t₀ t)

/-- **Error:** applies the *comoving* curvature constant `K` to the *proper* distance
`a(t₀) χ`: `d_L = (1 + z) S_K(a(t₀) χ)` (mixes the comoving-`K` and physical-curvature
conventions; the correct physical form would be `(1+z) S_{K/a₀²}(a₀ χ)`).
Agrees when `K = 0` or `a(t₀) = 1`. Differs for `K ≠ 0`, `a(t₀) ≠ 1`.
Witness: `K = 1`, `a s = 2 * exp s`, `t₀ = 0`, `t = -1` (`χ = (e-1)/2`):
true `d_L = 2e sin((e-1)/2) ≈ 4.11701`, `rt2 = e sin(e-1) ≈ 2.68877`. -/
noncomputable def rt2 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  (1 + redshift a t₀ t) * transverse K (a t₀ * comoving a t₀ t)

/-- **Error:** uses the normalized-`k ∈ {-1, 0, 1}` form `S = sin χ / χ / sinh χ` chosen by
the sign of `K`, forgetting the `√|K|` rescaling for a general curvature constant.
Agrees exactly for `K ∈ {-1, 0, 1}`. Differs for any other `K ≠ 0` (with `χ > 0`).
Witness: `K = 4`, `a = exp`, `t₀ = 0`, `t = -1/2` (`χ = √e - 1`, `1+z = √e`):
true `d_L = √e sin(2(√e-1))/2 ≈ 0.79375`, `rt3 = √e sin(√e-1) ≈ 0.99610`. -/
noncomputable def rt3 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) *
    (if 0 < K then Real.sin (comoving a t₀ t)
     else if K < 0 then Real.sinh (comoving a t₀ t) else comoving a t₀ t)

/-- **Error:** curvature sign convention flipped (sinh for closed `K > 0`, sin for open
`K < 0`), as if `K` were `Ω_k ∝ -K`.
Agrees for `K = 0`, and to `O(χ²)` for every `K` (first deviation `+Kχ³/3`).
Witness: `K = 1`, `a = exp`, `t₀ = 0`, `t = -1/2` (`χ = √e - 1`):
true `d_L = √e sin(√e-1) ≈ 0.99610`, `rt4 = √e sinh(√e-1) ≈ 1.14617`. -/
noncomputable def rt4 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * transverse (-K) (comoving a t₀ t)

/-- **Error (Lean junk value):** the closed branch is guarded by `0 ≤ K` instead of `0 < K`,
so the flat case evaluates `sin (√0 · χ) / √0 = 0 / 0 = 0`.
Agrees for every `K ≠ 0`. Differs exactly at `K = 0` (gives `0`).
Witness: `K = 0`, `a = exp`, `t₀ = 0`, `t = -1`:
true `d_L = e(e-1) ≈ 4.67077`, `rt5 = 0`. -/
noncomputable def rt5 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) *
    (if 0 ≤ K then Real.sin (Real.sqrt K * comoving a t₀ t) / Real.sqrt K
     else Real.sinh (Real.sqrt (-K) * comoving a t₀ t) / Real.sqrt (-K))

/-- **Error (Lean junk value):** typo in the open branch denominator, `√K` instead of `√(-K)`;
for `K < 0`, `Real.sqrt K = 0`, so the branch is `sinh(…)/0 = 0`.
Agrees for every `K ≥ 0`. Differs for every `K < 0` (gives `0`).
Witness: `K = -1`, `a = exp`, `t₀ = 0`, `t = -1` (`χ = e - 1`):
true `d_L = e sinh(e-1) ≈ 7.33334`, `rt6 = 0`. -/
noncomputable def rt6 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) *
    (if 0 < K then Real.sin (Real.sqrt K * comoving a t₀ t) / Real.sqrt K
     else if K < 0 then Real.sinh (Real.sqrt (-K) * comoving a t₀ t) / Real.sqrt K
     else comoving a t₀ t)

/-- **Error:** replaces `S_K(χ)` by its fifth-order Taylor polynomial
`χ - Kχ³/6 + K²χ⁵/120` (the "small-curvature" approximation).
Agrees exactly for `K = 0`, and agrees to `o(χ⁵)` (hence every cosmographic coefficient of
`d_L` through 4th order in `z` or `y` is the same). Differs for `K ≠ 0`, `χ > 0`.
Witness: `K = 1`, `a = exp`, `t₀ = 0`, `t = -1` (`χ = e - 1`, `1+z = e`):
true `d_L = e sin(e-1) ≈ 2.68877`, `rt7 = e(χ - χ³/6 + χ⁵/120) ≈ 2.71167`. -/
noncomputable def rt7 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) *
    (comoving a t₀ t - K * comoving a t₀ t ^ 3 / 6 + K ^ 2 * comoving a t₀ t ^ 5 / 120)

/-- **Error:** argument order of `redshift` swapped (`redshift a t t₀ = a(t)/a(t₀) - 1`),
so the factor is `1/(1+z)`; the result is `a(t₀) S_K(χ)/(1+z) = a(t) S_K(χ)`, the angular
diameter distance, not `d_L`.
Agrees when `a(t) = a(t₀)`; agrees to first order in `z` / `χ` (both `≈ z/H₀`).
Witness: `K = 0`, `a = exp`, `t₀ = 0`, `t = -1`:
true `d_L = e(e-1) ≈ 4.67077`, `rt8 = (e-1)/e ≈ 0.63212`. -/
noncomputable def rt8 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t t₀) * transverse K (comoving a t₀ t)

/-- **Error:** physical-curvature form `(1+z) S_{K_phys}(a₀ χ)` with the physical curvature
evaluated at the *emission* epoch, `K_phys = K/a(t)²`, instead of today, `K/a(t₀)²`.
Agrees when `K = 0` or `a(t) = a(t₀)`; differs at `O(χ³)` otherwise (any normalization of `a`).
Witness: `K = 1`, `a = exp`, `t₀ = 0`, `t = -1/2` (`χ = √e - 1`, `1+z = √e`):
true `d_L = √e sin(√e-1) ≈ 0.99610`, `rt9 = sin(e - √e) ≈ 0.87699`. -/
noncomputable def rt9 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  (1 + redshift a t₀ t) * transverse (K / a t ^ 2) (a t₀ * comoving a t₀ t)

/-- **Error (Lean junk value):** the textbook `Ω_k` parametrization
`d_L = (1+z)/(H₀√Ω_k) sinh(√Ω_k H₀ a₀ χ)`, `Ω_k = -K/(H₀ a₀)²` (sin branch for `Ω_k < 0`,
flat branch for `Ω_k = 0`). It is exact whenever `H₀ ≠ 0` (any sign of `H₀`), but when
`H₀ = 0` Lean gives `Ω_k = -K/0 = 0`, so a curved model falls into the flat branch.
Differs exactly when `H₀ = 0` and `K ≠ 0` (e.g. at the bounce of closed de Sitter).
Witness: `K = 1`, `a = Real.cosh` (closed de Sitter), `t₀ = 0`, `t = -1`
(`H₀ = 0`, `χ = arctan(sinh 1)`, `1+z = 1/cosh 1`):
true `d_L = sinh 1 / cosh² 1 ≈ 0.49355`, `rt10 = arctan(sinh 1)/cosh 1 ≈ 0.56107`. -/
noncomputable def rt10 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  let H := hubble a t₀
  let Ωk := -K / (H ^ 2 * a t₀ ^ 2)
  let χ := comoving a t₀ t
  let zp := 1 + redshift a t₀ t
  if 0 < Ωk then zp * Real.sinh (Real.sqrt Ωk * H * a t₀ * χ) / (H * Real.sqrt Ωk)
  else if Ωk < 0 then zp * Real.sin (Real.sqrt (-Ωk) * H * a t₀ * χ) / (H * Real.sqrt (-Ωk))
  else zp * a t₀ * χ

/-- **Error:** comoving distance written as an integral over lookback time `τ ∈ [0, t₀ - t]`
but with the integrand `1/a(τ)` instead of `1/a(t₀ - τ)`.
Agrees whenever `t = 0` (then both are `∫₀^{t₀} 1/a`) and for constant `a`; differs
generically (even at leading order in `t₀ - t`, unless `a(0) = a(t₀)`).
Witness: `K = 0`, `a = exp`, `t₀ = 1`, `t = 1/2` (`1+z = √e`, `a₀ = e`):
true `d_L = e - √e ≈ 1.06956`, `rt11 = e^{3/2} - e ≈ 1.76341`. -/
noncomputable def rt11 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * transverse K (∫ τ in (0 : ℝ)..(t₀ - t), 1 / a τ)

/-- **Error:** bound-variable typo in the comoving integral, `1 / a t` instead of `1 / a s`,
so `χ` becomes `(t₀ - t)/a(t)`.
Agrees for constant `a`; agrees with `χ` to leading order as `t → t₀`. Differs whenever
`a` is not constant on `[t, t₀]`.
Witness: `K = 0`, `a = exp`, `t₀ = 0`, `t = -1`:
true `d_L = e(e-1) ≈ 4.67077`, `rt12 = e² ≈ 7.38906`. -/
noncomputable def rt12 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * transverse K (∫ _s in t..t₀, 1 / a t)

end Work.Fidelity.RedTeam
