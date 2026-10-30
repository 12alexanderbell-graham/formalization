import Checked.Cosmography.Lookback

/-!
# Lookback time to second order with an `O(z³)` remainder (target 1, milestone 1b)

Same conventions and definitions as `Checked.Cosmography.lookback_second_order`. This is the
blind restater's reading of the source's "+ …" (run 2026-10-30T0028Z): with three derivatives
of `a`, the error is `O(z³)`. Source: as for milestone 1 (Physlib Distances.lean TODO;
Visser, arXiv:gr-qc/0411131, Eq. (11)).
-/

namespace Work.Cosmography

open Filter Asymptotics Topology Checked.Cosmography

/-- **Milestone 1b (FROZEN statement).** If `a` is `C³` near `t₀`, the lookback time satisfies
`t₀ - t = H₀⁻¹ (z - (1 + q₀/2) z²) + O(z³)` as `t → t₀`. -/
theorem lookback_second_order_bigO (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ContDiffAt ℝ 3 a t₀) (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =O[𝓝 t₀] (fun t => redshift a t₀ t ^ 3) := by
  sorry

end Work.Cosmography
