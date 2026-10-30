import Mathlib

/-!
# Blind specification: flat ΛCDM Friedmann solution near `t₀`

Written from textbook first principles (no repository definitions used).

## Textbook equations used
* Friedmann equation (FLRW, units `c = 1`; e.g. Weinberg, *Cosmology* §1.5;
  Ryden, *Introduction to Cosmology* eq. 4.17/5.x):
    `(ȧ/a)² = (8πG/3) ρ − K/a² + Λ/3`.
  Here the universe is spatially flat, `K = 0`, and the only fluid is dust.
* Continuity (energy-conservation) equation `ρ̇ + 3 (ȧ/a)(ρ + p) = 0`, which for
  pressureless matter (`p = 0`) integrates to `ρ_m a³ = const`.
* Critical density `ρ_crit = 3 H² / (8πG)`, Hubble rate `H = ȧ / a`, and the matter
  density parameter `Ω_m = ρ_m(t₀) / ρ_crit(t₀)`.

## Conventions
* Units `c = 1` and `8πG/3 = 1`. Then the Friedmann equation reads
  `(ȧ/a)² = ρ_m + Λ/3` and the critical density is `ρ_crit = H²`.
* `a : ℝ → ℝ` is the scale factor as a function of cosmic time; it is not normalised
  (`a t₀` need not be `1`).
* The statement is local: everything holds on a neighbourhood of `t₀`
  (`∀ᶠ t in nhds t₀`). The neighbourhood contains `t₀`, so in particular `a t₀ > 0`
  and `a` is differentiable at `t₀`.
* No sign restriction on `Ω` or `Λ` (negative matter density or negative Λ allowed).
* Junk-value guards: `a t > 0` on the neighbourhood (so `ȧ/a` is a genuine quotient);
  `a` is required to be differentiable at each such `t` (so `deriv a t` is the true
  derivative, not the junk value `0`); expansion is `ȧ(t₀) > 0`, which also makes
  `H₀ = ȧ(t₀)/a(t₀) > 0`, so `ρ_crit(t₀) = H₀² ≠ 0` and the division defining `Ω`
  is genuine. No square roots are used.
* The matter density is an explicit function `ρ` with `ρ t · (a t)³ = ρ t₀ · (a t₀)³`
  (integrated dust continuity equation); `Λ` is an explicit real constant.
-/

namespace Work.Fidelity.FriedmannBlind

/-- Near `t₀`, `a` solves the flat dust + Λ Friedmann equation, the universe is
expanding at `t₀`, and `Ω` is the present matter density parameter
`ρ_m(t₀) / ρ_crit(t₀)` with `ρ_crit = H₀²` (units `c = 1`, `8πG/3 = 1`). -/
def FriedmannLCDM (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ∃ (ρ : ℝ → ℝ) (Λ : ℝ),
    (∀ᶠ t in nhds t₀,
        0 < a t ∧
        DifferentiableAt ℝ a t ∧
        -- dust continuity equation, integrated: ρ_m a³ = const
        ρ t * a t ^ 3 = ρ t₀ * a t₀ ^ 3 ∧
        -- flat Friedmann equation with 8πG/3 = 1:  H² = ρ_m + Λ/3
        (deriv a t / a t) ^ 2 = ρ t + Λ / 3) ∧
    -- expanding at t₀
    0 < deriv a t₀ ∧
    -- Ω = ρ_m(t₀) / ρ_crit(t₀), ρ_crit(t₀) = H₀² = (ȧ(t₀)/a(t₀))²
    Ω = ρ t₀ / (deriv a t₀ / a t₀) ^ 2

/-- Sanity check: Einstein–de Sitter `a(t) = t^(2/3)` at `t₀ = 1` has `Ω = 1`
(with `ρ_m(t) = 4/(9 t²)`, `Λ = 0`). -/
theorem einsteinDeSitter : FriedmannLCDM 1 (fun t => t ^ ((2:ℝ)/3)) 1 := by
  have hder : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun t : ℝ => t ^ ((2:ℝ)/3)) ((2/3) * t ^ ((2:ℝ)/3 - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  refine ⟨fun t => 4 / 9 / t ^ 2, 0, ?_, ?_, ?_⟩
  · filter_upwards [Ioi_mem_nhds one_pos] with t ht
    have ht : (0:ℝ) < t := ht
    have hpos : 0 < t ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos ht _
    have hcube : (t ^ ((2:ℝ)/3)) ^ 3 = t ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_natCast]
      norm_num
    refine ⟨hpos, (hder t ht).differentiableAt, ?_, ?_⟩
    · rw [hcube]
      field_simp
      norm_num
    · rw [(hder t ht).deriv, Real.rpow_sub ht, Real.rpow_one]
      field_simp
      ring
  · rw [(hder 1 one_pos).deriv]
    norm_num
  · rw [(hder 1 one_pos).deriv]
    norm_num

end Work.Fidelity.FriedmannBlind
