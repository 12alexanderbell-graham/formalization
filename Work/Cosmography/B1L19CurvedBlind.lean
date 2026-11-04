import Checked.Cosmography.B1L19
import Checked.Cosmography.BambaCurved

/-!
# Blind restatement: Lusso et al. 2019 log-polynomial fits vs. curved ΛCDM

Interpretive choices (made blind, from the verbal claim only):

1. "A scale factor of such a universe" is encoded on a finite past interval `[t₂, t₀]` only,
   where `t₂` is the emission time of the farther source: `a > 0` there and `a` satisfies the
   expanding-branch Friedmann equation `a' = a H₀ E(a₀/a)`,
   `E(x) = √(Ω_m x³ + Ω_k x² + Ω_Λ)`, as a one-sided (`HasDerivWithinAt … (Icc t₂ t₀)`)
   derivative. Assuming it on all `t ≤ t₀` would be vacuous (ΛCDM with `Ω_m > 0` has a big bang
   at finite time), so the interval is deliberately bounded. No smoothness beyond this is assumed.
2. `H₀ > 0` is a parameter, tied to `a` only through the Friedmann equation (which forces
   `a'(t₀)/a(t₀) = H₀` one-sidedly). I do not use `hubble`/`omega0` because they need a
   two-sided derivative at `t₀`; instead the curvature relation is stated as
   `K = -Ω_k (H₀ a₀)²` (equivalent to `omega0 K a t₀ = 1 - Ω_k` when `hubble a t₀ = H₀`).
3. Ranges are closed: `0.1 ≤ Ω_m ≤ 1`, `-0.1 ≤ Ω_k ≤ 0` (closed = weaker hypothesis).
   `Ω_Λ := 1 - Ω_m - Ω_k`.
4. Emission times `t₁, t₂ ∈ [t₂, t₀]` are fixed by `redshift a t₀ tᵢ = 2√2 - 1`, `4√2 - 1`.
5. "Any normalisation" = every `Hfit > 0` in `logPolyDL4`; `D_L` is evaluated at the source's
   redshift. (The normalisation cancels in the difference; `Hfit ≠ 0` would also do.)
6. `μ_exact - μ_fit := 5 log₁₀(d_L / D_L)` with `d_L = BambaK.lumDist K a t₀ t` (c = 1).
7. "Exceeds by more than" = strict inequality `resid(t₂) - resid(t₁) > 1/4` (resp. `3/20`).

Ambiguities / plausibility: "between" could be open; I take closed. Ω_Λ may reach 0.1 at
`Ω_m = 1, Ω_k = -0.1` (allowed). A quick numerical scan (outside Lean) gives minimum differences
≈ 0.351 and ≈ 0.290 mag at `Ω_m = 1, Ω_k = -0.1`, so I believe both claims are true.
-/

namespace Work.Cosmography.B1L19CurvedBlind

open Checked.Cosmography Checked.Cosmography.BambaK Checked.Cosmography.B1L19

/-- Dimensionless expansion rate `E(x) = √(Ω_m x³ + Ω_k x² + Ω_Λ)` with `Ω_Λ = 1 - Ω_m - Ω_k`,
evaluated at `x = 1 + z`. -/
noncomputable def lcdmE (Ωm Ωk x : ℝ) : ℝ :=
  Real.sqrt (Ωm * x ^ 3 + Ωk * x ^ 2 + (1 - Ωm - Ωk))

/-- `a` is the scale factor of an expanding ΛCDM universe with parameters `H₀, Ω_m, Ω_k`
on the time interval `[t₂, t₀]`. -/
def IsLCDMOn (H₀ Ωm Ωk : ℝ) (a : ℝ → ℝ) (t₂ t₀ : ℝ) : Prop :=
  t₂ ≤ t₀ ∧
  (∀ t ∈ Set.Icc t₂ t₀, 0 < a t) ∧
  (∀ t ∈ Set.Icc t₂ t₀,
    HasDerivWithinAt a (a t * H₀ * lcdmE Ωm Ωk (a t₀ / a t)) (Set.Icc t₂ t₀) t)

/-- Residual distance modulus `μ_exact - μ_fit = 5 log₁₀(d_L / D_L)` of a source emitting at `t`. -/
noncomputable def residual (K : ℝ) (a : ℝ → ℝ) (t₀ t a₂ a₃ a₄ Hfit : ℝ) : ℝ :=
  5 * Real.logb 10 (lumDist K a t₀ t / logPolyDL4 a₂ a₃ a₄ Hfit (redshift a t₀ t))

/-- Shared hypothesis package for the two claims. -/
def Setup (H₀ Ωm Ωk K : ℝ) (a : ℝ → ℝ) (t₀ t₁ t₂ : ℝ) : Prop :=
  0 < H₀ ∧ 1 / 10 ≤ Ωm ∧ Ωm ≤ 1 ∧ -(1 / 10) ≤ Ωk ∧ Ωk ≤ 0 ∧
  K = -Ωk * (H₀ * a t₀) ^ 2 ∧
  IsLCDMOn H₀ Ωm Ωk a t₂ t₀ ∧
  t₁ ∈ Set.Icc t₂ t₀ ∧
  redshift a t₀ t₁ = 2 * Real.sqrt 2 - 1 ∧
  redshift a t₀ t₂ = 4 * Real.sqrt 2 - 1

/-- SNe + quasars fit (`a₂ = 3.075, a₃ = 4.466, a₄ = -3.716`): the residual at `1+z = 4√2`
exceeds the one at `1+z = 2√2` by more than `1/4` mag, for every normalisation. -/
theorem snQso_residual_gap (H₀ Ωm Ωk K : ℝ) (a : ℝ → ℝ) (t₀ t₁ t₂ : ℝ)
    (h : Setup H₀ Ωm Ωk K a t₀ t₁ t₂) (Hfit : ℝ) (hHfit : 0 < Hfit) :
    residual K a t₀ t₂ 3.075 4.466 (-3.716) Hfit
      - residual K a t₀ t₁ 3.075 4.466 (-3.716) Hfit > 1 / 4 := by
  sorry

/-- SNe + quasars + GRBs fit (`a₂ = 3.205, a₃ = 3.564, a₄ = -2.510`): the residual at
`1+z = 4√2` exceeds the one at `1+z = 2√2` by more than `3/20` mag, for every normalisation. -/
theorem snQsoGrb_residual_gap (H₀ Ωm Ωk K : ℝ) (a : ℝ → ℝ) (t₀ t₁ t₂ : ℝ)
    (h : Setup H₀ Ωm Ωk K a t₀ t₁ t₂) (Hfit : ℝ) (hHfit : 0 < Hfit) :
    residual K a t₀ t₂ 3.205 3.564 (-2.510) Hfit
      - residual K a t₀ t₁ 3.205 3.564 (-2.510) Hfit > 3 / 20 := by
  sorry

end Work.Cosmography.B1L19CurvedBlind
