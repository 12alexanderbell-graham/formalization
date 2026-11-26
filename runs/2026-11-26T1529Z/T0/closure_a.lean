import Readings.T0

open Complex Filter Topology Finset Asymptotics
namespace ExternalT0
open T0

lemma sum_Icc_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, f k = ∑ k ∈ Finset.range N, f (k + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N (c := 1)]
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc]

theorem harmonic_log' : type_of% @T0.harmonic_log := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hH : (∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / k) = (harmonic N : ℝ) := by
    simp [harmonic_eq_sum_Icc, one_div]
  rw [hH]
  have h1 := log_add_one_le_harmonic N
  have h2 := harmonic_le_one_add_log N
  have h3 : Real.log N ≤ Real.log ↑(N + 1) :=
    Real.log_le_log (by exact_mod_cast hN) (by push_cast; linarith)
  rw [Real.norm_eq_abs, abs_le]; norm_num; constructor <;> linarith

lemma norm_pairPhase (s : ℝ) (k : ℕ) : ‖pairPhase s k‖ = 1 := by
  unfold pairPhase
  rw [Complex.norm_exp]
  have : (-(2 * Complex.I * (k : ℂ) / (s : ℂ))).re = 0 := by
    simp [Complex.div_re, Complex.mul_re]
  rw [this, Real.exp_zero]

lemma pairPhase_pow (s : ℝ) (k : ℕ) :
    pairPhase s k = Complex.exp (-(2 * Complex.I / s)) ^ k := by
  unfold pairPhase; rw [← Complex.exp_nat_mul]; congr 1; ring

theorem eq_4_33' : type_of% @T0.eq_4_33 := by
  intro s hs
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  set z := Complex.exp (-(2 * Complex.I / s)) with hz
  have hzn : ‖z‖ = 1 := by
    have := norm_pairPhase s 1; rw [pairPhase_pow, pow_one] at this; exact this
  have hterm : ∀ k : ℕ, (2 * ((variance s (k + 1)) ^ 2 : ℝ) * pairPhase s (k + 1) : ℂ)
      = z ^ (k + 1) / ((k : ℂ) + 1) ^ 2 / (2 * (s : ℂ) ^ 2) := by
    intro k
    rw [pairPhase_pow, ← hz]; unfold variance; push_cast
    have : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
  have hsum1 : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
    simpa using this
  have hg : Summable (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ 2) := by
    refine Summable.of_norm_bounded hsum1 (fun k => ?_)
    rw [norm_div, norm_pow, hzn, one_pow, norm_pow]
    have : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
      have := Complex.norm_natCast (k + 1); push_cast at this; exact this
    rw [this]; exact le_of_eq (one_div _)
  refine ⟨?_, ?_, ?_⟩
  · have : (fun k : ℕ => ‖(2 * ((variance s (k + 1)) ^ 2 : ℝ) * pairPhase s (k + 1) : ℂ)‖)
        = fun k : ℕ => ‖z ^ (k + 1) / ((k : ℂ) + 1) ^ 2‖ / (2 * s ^ 2) := by
      funext k; rw [hterm, norm_div]; congr 1
      rw [norm_mul, norm_pow]; simp [abs_of_pos hs]
    rw [this]; exact hg.norm.div_const _
  · intro N
    apply Finset.sum_congr rfl; intro j hj
    simp only [connValue]; rw [Finset.sum_ite_eq]; simp [hj]
  · have hL : HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1) ^ 2 / (2 * (s : ℂ) ^ 2))
        (Li2 z / (2 * (s : ℂ) ^ 2)) := hg.hasSum.div_const _
    have := hL.tendsto_sum_nat
    refine this.congr (fun N => ?_)
    rw [sum_Icc_shift (fun k => (2 * ((variance s k) ^ 2 : ℝ) * pairPhase s k : ℂ))]
    apply Finset.sum_congr rfl; intro k _
    rw [hterm]

end ExternalT0
#print axioms ExternalT0.harmonic_log'
#print axioms ExternalT0.eq_4_33'
