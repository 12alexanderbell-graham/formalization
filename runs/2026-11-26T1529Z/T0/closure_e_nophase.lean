import Readings.T0

/-! Target 0(a), assumption check: without the chosen annihilation phase (the plain connected
two-point function of the quadratic insertions) the radial sum is still finite: `2 Σ_k (Δq_k)⁴ =
π²/(12 s²)`. So finiteness at fixed `s > 0` comes from `(Δq_k)⁴ ∝ 1/k²`, not from the phase; the
phase matters only for the expansion in `G_N` (Eq. 4.34). -/
namespace ExternalT0
open T0

theorem no_phase (s : ℝ) (hs : 0 < s) :
    HasSum (fun k : ℕ => 2 * (variance s (k + 1)) ^ 2) (Real.pi ^ 2 / (12 * s ^ 2)) := by
  have h := hasSum_zeta_two
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero] at h1
  have h2 := h1.mul_left (1 / (2 * s ^ 2))
  convert h2 using 1
  · funext k; unfold variance; push_cast; field_simp
  · field_simp; ring

end ExternalT0
#print axioms ExternalT0.no_phase
