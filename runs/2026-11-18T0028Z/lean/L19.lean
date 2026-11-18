import Checked.Trust.NecessityAQ
import Checked.Cosmography.B1L19

namespace Checked.Trust.NCAQ

open Set Filter Topology MeasureTheory Real
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1L19

theorem sqrt2_bd : (1.41421 : ℝ) ≤ √2 ∧ √2 ≤ (1.41422 : ℝ) := by
  constructor
  · rw [show (1.41421 : ℝ) = √(1.41421 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [show (1.41422 : ℝ) = √(1.41422 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)

/-- `v₃ = √(1/(2√2))`, `v₅ = √(1/(4√2))`. -/
theorem v3_bd : (0.5946 : ℝ) ≤ √(1 / (2 * √2)) ∧ √(1 / (2 * √2)) ≤ (0.5947 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  have hp : 0 < 2 * √2 := by positivity
  constructor
  · rw [show (0.5946 : ℝ) = √(0.5946 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; rw [le_div_iff₀ hp]; nlinarith
  · rw [show (0.5947 : ℝ) = √(0.5947 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; rw [div_le_iff₀ hp]; nlinarith

theorem v5_bd : (0.4204 : ℝ) ≤ √(1 / (4 * √2)) ∧ √(1 / (4 * √2)) ≤ (0.4205 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  have hp : 0 < 4 * √2 := by positivity
  constructor
  · rw [show (0.4204 : ℝ) = √(0.4204 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; rw [le_div_iff₀ hp]; nlinarith
  · rw [show (0.4205 : ℝ) = √(0.4205 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt; rw [div_le_iff₀ hp]; nlinarith

/-- At `Ω = 10`: `J₅ ≤ 1.3954 J₃` with `J_Z = ∫_{1/√Z}^1 g` (two-step lower bound of `J₃`). -/
theorem J53 :
    let J3 := ∫ v in √(1 / (2 * √2))..1, 2 / √(10 + (1 - 10) * v ^ 6)
    let J5 := ∫ v in √(1 / (4 * √2))..1, 2 / √(10 + (1 - 10) * v ^ 6)
    0 < J3 ∧ J5 ≤ 1.3954 * J3 := by
  intro J3 J5
  obtain ⟨a3, b3⟩ := v3_bd
  obtain ⟨a5, b5⟩ := v5_bd
  obtain ⟨s1, s2⟩ := sqrt2_bd
  set v3 := √(1 / (2 * √2))
  set v5 := √(1 / (4 * √2))
  have hΩ : (1:ℝ) ≤ 10 := by norm_num
  have hs5 := int_split 10 v5 v3 hΩ (by linarith) (by linarith) (by linarith)
  have hs3 := int_split 10 v3 (9 / 10) hΩ (by linarith) (by linarith) (by norm_num)
  obtain ⟨-, hK⟩ := int_piece 10 v5 v3 hΩ (by linarith) (by linarith) (by linarith)
  obtain ⟨hA, -⟩ := int_piece 10 v3 (9 / 10) hΩ (by linarith) (by linarith) (by norm_num)
  obtain ⟨hB, -⟩ := int_piece 10 (9 / 10) 1 hΩ (by norm_num) (by norm_num) le_rfl
  set G3 := 2 / √(10 + (1 - 10) * v3 ^ 6)
  set G9 := 2 / √(10 + (1 - 10) * (9 / 10 : ℝ) ^ 6)
  -- v₃⁶ = 1/(16√2)
  have hv3sq : v3 ^ 2 = 1 / (2 * √2) := Real.sq_sqrt (by positivity)
  have hv36 : v3 ^ 6 = 1 / (2 * √2) ^ 3 := by
    rw [show v3 ^ 6 = (v3 ^ 2) ^ 3 by ring, hv3sq, div_pow, one_pow]
  have hr3 : (9.6022 : ℝ) ≤ 10 + (1 - 10) * v3 ^ 6 := by
    rw [hv36]
    have h8 : (2 * √2) ^ 3 = 16 * √2 := by
      have : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith
    rw [h8]
    have : 1 / (16 * √2) ≤ (1 / 22.62736 : ℝ) := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    nlinarith
  have hr3' : 10 + (1 - 10) * v3 ^ 6 ≤ 10 := by
    have : 0 ≤ v3 ^ 6 := by positivity
    nlinarith
  have hG3p : 0 < G3 := by
    have : 0 < 10 + (1 - 10) * v3 ^ 6 := by linarith
    positivity
  have hG9 : 1.356 * G3 ≤ G9 := by
    simp only [G3, G9]
    have hr9 : (10 + (1 - 10) * (9 / 10 : ℝ) ^ 6) = 5.217031 := by norm_num
    rw [hr9]
    have hq3 : 0 < √(10 + (1 - 10) * v3 ^ 6) := Real.sqrt_pos.2 (by linarith)
    have hq9 : 0 < √(5.217031 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    rw [mul_div_assoc', div_le_div_iff₀ hq3 hq9]
    have : 1.356 * √(5.217031 : ℝ) ≤ √(10 + (1 - 10) * v3 ^ 6) := by
      rw [show (1.356 : ℝ) * √5.217031 = √(1.356 ^ 2 * 5.217031) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    nlinarith
  have hJ3 : J3 ≥ (9 / 10 - v3) * G3 + (1 - 9 / 10) * G9 := by
    show _ ≤ ∫ v in v3..1, 2 / √(10 + (1 - 10) * v ^ 6)
    rw [hs3]; linarith
  refine ⟨by nlinarith, ?_⟩
  show ∫ v in v5..1, 2 / √(10 + (1 - 10) * v ^ 6) ≤ 1.3954 * ∫ v in v3..1, 2 / √(10 + (1 - 10) * v ^ 6)
  rw [hs5]
  change _ + J3 ≤ 1.3954 * J3
  have hK' : ∫ v in v5..v3, 2 / √(10 + (1 - 10) * v ^ 6) ≤ 0.1743 * G3 := by
    refine le_trans hK ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hG3p.le
  nlinarith


theorem log_2s2 : Real.log (1 + (2 * √2 - 1)) = 3 / 2 * Real.log 2 := by
  rw [show 1 + (2 * √2 - 1) = 2 * √2 by ring, Real.log_mul (by norm_num) (by positivity),
    Real.log_sqrt (by norm_num)]; ring

theorem log_4s2 : Real.log (1 + (4 * √2 - 1)) = 5 / 2 * Real.log 2 := by
  rw [show 1 + (4 * √2 - 1) = 2 ^ 2 * √2 by ring, Real.log_mul (by norm_num) (by positivity),
    Real.log_sqrt (by norm_num), Real.log_pow]; push_cast; ring

theorem log10_bd : (2.30249 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ (2.30268 : ℝ) := by
  have h1 : 3 * Real.log 10 = 10 * Real.log 2 + Real.log (1000 / 1024) := by
    rw [Real.log_div (by norm_num) (by norm_num), show (1000:ℝ) = 10 ^ 3 by norm_num,
      show (1024:ℝ) = 2 ^ 10 by norm_num, Real.log_pow, Real.log_pow]; push_cast; ring
  have hu := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1000 / 1024 by norm_num)
  have hd := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1000 / 1024 by norm_num)
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  norm_num at hu hd
  constructor <;> linarith

/-- `λ = log₁₀ 2`. -/
theorem lam_bd : (0.30101 : ℝ) ≤ Real.log 2 / Real.log 10 ∧ Real.log 2 / Real.log 10 ≤ (0.30105 : ℝ) := by
  obtain ⟨a, b⟩ := log10_bd
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  constructor
  · rw [le_div_iff₀ (by linarith)]; nlinarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-- The bracket of the quartic log-polynomial. -/
noncomputable def Bq (a₂ a₃ a₄ x : ℝ) : ℝ := x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4

theorem poly4_eq (a₂ a₃ a₄ : ℝ) (k : ℝ) (z : ℝ) (hz : Real.log (1 + z) = k * Real.log 2) :
    logPolyDL4 a₂ a₃ a₄ 1 z = Real.log 10 * Bq a₂ a₃ a₄ (k * (Real.log 2 / Real.log 10)) := by
  unfold logPolyDL4 Bq Real.logb; rw [hz]; ring

/-- The `Ω = 10` model with sources at `1 + z = 2√2` and `4√2`. -/
theorem data_10 :
    0 ≤ (10:ℝ) ∧ tS 10 (4 * √2) ≤ tS 10 (2 * √2) ∧ tS 10 (2 * √2) ≤ tO 10 ∧
      (∀ s ∈ Set.Icc (tS 10 (4 * √2)) (tO 10), 0 < sa s) ∧
      (∀ s ∈ Set.Icc (tS 10 (4 * √2)) (tO 10), DifferentiableAt ℝ sa s) ∧ 0 < hubble sa (tO 10) ∧
      (∀ s ∈ Set.Icc (tS 10 (4 * √2)) (tO 10),
        hubble sa s = hubble sa (tO 10) * √(10 * (1 + redshift sa (tO 10) s) ^ 3 + 1 - 10)) ∧
      redshift sa (tO 10) (tS 10 (2 * √2)) = 2 * √2 - 1 ∧
      redshift sa (tO 10) (tS 10 (4 * √2)) = 4 * √2 - 1 := by
  have hΩ : (1:ℝ) < 10 := by norm_num
  obtain ⟨s1, -⟩ := sqrt2_bd
  obtain ⟨h0, h1, hc⟩ := tO_props 10 hΩ
  obtain ⟨ht5, -, hz5⟩ := tS_props 10 (4 * √2) hΩ (by linarith)
  obtain ⟨-, h3O, hz3⟩ := tS_props 10 (2 * √2) hΩ (by linarith)
  obtain ⟨hp, hd, hH₀, hH⟩ := sa_hyps 10 (tO 10) (tS 10 (4 * √2)) h0 h1 hc ht5
  exact ⟨by norm_num, tS_anti 10 _ _ hΩ (by linarith) (by linarith), h3O, hp, hd, hH₀, hH, hz3, hz5⟩

/-- At `Ω = 10`, with any quartic coefficients whose brackets are positive, the ratio of the two
distance ratios is `2 (J₅/J₃)(B₃/B₅)`, at most `2 · 1.3954 · B₃/B₅`. -/
theorem ratio_10 (a₂ a₃ a₄ : ℝ)
    (hB3 : 0 < Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10)))
    (hB5 : 0 < Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10))) :
    let x5 := lumDistFlat sa (tO 10) (tS 10 (4 * √2)) /
      logPolyDL4 a₂ a₃ a₄ 1 (redshift sa (tO 10) (tS 10 (4 * √2)))
    let x3 := lumDistFlat sa (tO 10) (tS 10 (2 * √2)) /
      logPolyDL4 a₂ a₃ a₄ 1 (redshift sa (tO 10) (tS 10 (2 * √2)))
    0 < x5 ∧ 0 < x3 ∧ x5 / x3 ≤ 2 * 1.3954 * Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10)) /
      Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10)) := by
  intro x5 x3
  obtain ⟨-, -, -, -, -, hH₀, -, hz3, hz5⟩ := data_10
  obtain ⟨s1, -⟩ := sqrt2_bd
  have hΩ : (1:ℝ) < 10 := by norm_num
  obtain ⟨hJ3, hJ53⟩ := J53
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have e5 : x5 = 4 * √2 / hubble sa (tO 10) *
      (∫ v in √(1 / (4 * √2))..1, 2 / √(10 + (1 - 10) * v ^ 6)) /
      (Real.log 10 * Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10))) := by
    simp only [x5]; rw [hz5, poly4_eq _ _ _ _ _ log_4s2, sa_dL 10 _ hΩ (by linarith)]
  have e3 : x3 = 2 * √2 / hubble sa (tO 10) *
      (∫ v in √(1 / (2 * √2))..1, 2 / √(10 + (1 - 10) * v ^ 6)) /
      (Real.log 10 * Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10))) := by
    simp only [x3]; rw [hz3, poly4_eq _ _ _ _ _ log_2s2, sa_dL 10 _ hΩ (by linarith)]
  have hJ5 : 0 < ∫ v in √(1 / (4 * √2))..1, 2 / √(10 + (1 - 10) * v ^ 6) := by
    obtain ⟨a5, b5⟩ := v5_bd
    obtain ⟨a3, b3⟩ := v3_bd
    have hs5 := int_split 10 (√(1 / (4 * √2))) (√(1 / (2 * √2))) (by norm_num) (by linarith)
      (by linarith) (by linarith)
    obtain ⟨hK, -⟩ := int_piece 10 (√(1 / (4 * √2))) (√(1 / (2 * √2))) (by norm_num) (by linarith)
      (by linarith) (by linarith)
    have hg := g_ge 10 (√(1 / (4 * √2))) (by norm_num) (by linarith) (by linarith)
    have : 0 < 2 / √(10:ℝ) := by positivity
    have hm : 0 ≤ (√(1 / (2 * √2)) - √(1 / (4 * √2))) * (2 / √(10 + (1 - 10) * √(1 / (4 * √2)) ^ 6)) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hs5]; linarith
  set J3 := ∫ v in √(1 / (2 * √2))..1, 2 / √(10 + (1 - 10) * v ^ 6)
  set J5 := ∫ v in √(1 / (4 * √2))..1, 2 / √(10 + (1 - 10) * v ^ 6)
  set B3 := Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10))
  set B5 := Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10))
  set H := hubble sa (tO 10)
  have hs : 0 < √2 := by positivity
  have hx5 : 0 < x5 := by rw [e5]; positivity
  have hx3 : 0 < x3 := by rw [e3]; positivity
  refine ⟨hx5, hx3, ?_⟩
  have hy : x5 / x3 = 2 * J5 * B3 / (J3 * B5) := by
    rw [e5, e3]; field_simp; ring
  rw [hy, div_le_div_iff₀ (by positivity) hB5]
  have : 2 * J5 * B3 * B5 ≤ 2 * (1.3954 * J3) * B3 * B5 := by gcongr
  nlinarith

theorem logb_le_of_pow (y : ℝ) (k n : ℕ) (hy : 0 < y) (h : y ^ n ≤ 10 ^ k) (hn : 0 < n) :
    Real.logb 10 y ≤ k / n := by
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have h1 := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [Real.logb, div_le_div_iff₀ hl10 (by exact_mod_cast hn)]
  nlinarith

/-- Without `Ω ≤ 1`: at `Ω = 10` the residual of the central fit grows by at most 7/20 mag
between `1 + z = 2√2` and `4√2`. -/
theorem l19_sq_central_h2 : necessity% Checked.Cosmography.B1L19.l19_sq_central 2 := by
  obtain ⟨h0, h53, h3O, hp, hd, hH₀, hH, hz3, hz5⟩ := data_10
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  have q4 := pow_le_pow_left₀ (by norm_num) l1 4
  have q4' := pow_le_pow_left₀ (by linarith) l2 4
  have hB3 : 0 < Bq 3.075 4.466 (-3.716) (3 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hB5 : 0 < Bq 3.075 4.466 (-3.716) (5 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  obtain ⟨hx5, hx3, hr⟩ := ratio_10 3.075 4.466 (-3.716) hB3 hB5
  refine ⟨10, h0, sa, _, _, tO 10, h53, h3O, hp, hd, hH₀, hH, hz3, hz5, 1, one_pos, ?_⟩
  rw [not_lt, logb_div' _ _ hx5 hx3]
  have hb : 2 * 1.3954 * Bq 3.075 4.466 (-3.716) (3 / 2 * lam) / Bq 3.075 4.466 (-3.716) (5 / 2 * lam)
      ≤ 1.174 := by
    rw [div_le_iff₀ hB5]; unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hy := le_trans hr hb
  have hpow : (_ : ℝ) ^ 100 ≤ (10:ℝ) ^ 7 :=
    le_trans (pow_le_pow_left₀ (div_pos hx5 hx3).le hy 100) (by norm_num)
  have := logb_le_of_pow _ 7 100 (div_pos hx5 hx3) hpow (by norm_num)
  norm_num at this ⊢; linarith

/-- Without `Ω ≤ 1`: the same for the SNe + GRB + quasar central fit and its 3/10 mag. -/
theorem l19_sqg_central_h2 : necessity% Checked.Cosmography.B1L19.l19_sqg_central 2 := by
  obtain ⟨h0, h53, h3O, hp, hd, hH₀, hH, hz3, hz5⟩ := data_10
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  have q4 := pow_le_pow_left₀ (by norm_num) l1 4
  have q4' := pow_le_pow_left₀ (by linarith) l2 4
  have hB3 : 0 < Bq 3.205 3.564 (-2.510) (3 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hB5 : 0 < Bq 3.205 3.564 (-2.510) (5 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  obtain ⟨hx5, hx3, hr⟩ := ratio_10 3.205 3.564 (-2.510) hB3 hB5
  refine ⟨10, h0, sa, _, _, tO 10, h53, h3O, hp, hd, hH₀, hH, hz3, hz5, 1, one_pos, ?_⟩
  rw [not_lt, logb_div' _ _ hx5 hx3]
  have hb : 2 * 1.3954 * Bq 3.205 3.564 (-2.510) (3 / 2 * lam) / Bq 3.205 3.564 (-2.510) (5 / 2 * lam)
      ≤ 1.148 := by
    rw [div_le_iff₀ hB5]; unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hy := le_trans hr hb
  have hpow : (_ : ℝ) ^ 100 ≤ (10:ℝ) ^ 6 :=
    le_trans (pow_le_pow_left₀ (div_pos hx5 hx3).le hy 100) (by norm_num)
  have := logb_le_of_pow _ 6 100 (div_pos hx5 hx3) hpow (by norm_num)
  norm_num at this ⊢; linarith

theorem box_core (a₂ a₃ a₄ : ℝ)
    (hB3 : 0 < Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10)))
    (hB5 : 0 < Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10)))
    (hb : 2 * 1.3954 * Bq a₂ a₃ a₄ (3 / 2 * (Real.log 2 / Real.log 10)) ≤
      Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10))) :
    5 * Real.logb 10 (lumDistFlat sa (tO 10) (tS 10 (4 * √2)) /
        logPolyDL4 a₂ a₃ a₄ 1 (redshift sa (tO 10) (tS 10 (4 * √2)))) ≤
      5 * Real.logb 10 (lumDistFlat sa (tO 10) (tS 10 (2 * √2)) /
        logPolyDL4 a₂ a₃ a₄ 1 (redshift sa (tO 10) (tS 10 (2 * √2)))) := by
  obtain ⟨hx5, hx3, hr⟩ := ratio_10 a₂ a₃ a₄ hB3 hB5
  have h1 : (_ : ℝ) / _ ≤ 1 := le_trans hr ((div_le_one hB5).2 hb)
  have h2 := (div_le_one hx3).1 h1
  have := Real.logb_le_logb_of_le (b := 10) (by norm_num) hx5 h2
  linarith

theorem pos5_of (a₂ a₃ a₄ : ℝ) (h : 0 < Bq a₂ a₃ a₄ (5 / 2 * (Real.log 2 / Real.log 10))) :
    0 < logPolyDL4 a₂ a₃ a₄ 1 (4 * √2 - 1) := by
  rw [poly4_eq _ _ _ _ _ log_4s2]; exact mul_pos (Real.log_pos (by norm_num)) h

/-- Without `Ω ≤ 1`: at `Ω = 10` the corner `a₂ = 2.906`, `a₃ = 5.479`, `a₄ = −1.794` of the
1σ region has residual at `4√2` at most the residual at `2√2`. -/
theorem l19_sq_box_h2 : necessity% Checked.Cosmography.B1L19.l19_sq_box 2 := by
  obtain ⟨h0, h53, h3O, hp, hd, hH₀, hH, hz3, hz5⟩ := data_10
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  have q4 := pow_le_pow_left₀ (by norm_num) l1 4
  have q4' := pow_le_pow_left₀ (by linarith) l2 4
  have hB3 : 0 < Bq 2.906 5.479 (-1.794) (3 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hB5 : 0 < Bq 2.906 5.479 (-1.794) (5 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hb : 2 * 1.3954 * Bq 2.906 5.479 (-1.794) (3 / 2 * lam) ≤ Bq 2.906 5.479 (-1.794) (5 / 2 * lam) := by
    unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  refine ⟨10, h0, sa, _, _, tO 10, h53, h3O, hp, hd, hH₀, hH, hz3, hz5, 2.906, 5.479, -1.794, 1,
    one_pos, le_rfl, le_rfl, le_rfl, by rw [hz5]; exact pos5_of _ _ _ hB5, ?_⟩
  rw [not_lt]; exact box_core _ _ _ hB3 hB5 hb

/-- Without `Ω ≤ 1`: the same for the SNe + GRB + quasar 1σ region, corner `3.043, 4.480, −0.915`. -/
theorem l19_sqg_box_h2 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 2 := by
  obtain ⟨h0, h53, h3O, hp, hd, hH₀, hH, hz3, hz5⟩ := data_10
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  have q4 := pow_le_pow_left₀ (by norm_num) l1 4
  have q4' := pow_le_pow_left₀ (by linarith) l2 4
  have hB3 : 0 < Bq 3.043 4.480 (-0.915) (3 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hB5 : 0 < Bq 3.043 4.480 (-0.915) (5 / 2 * lam) := by unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  have hb : 2 * 1.3954 * Bq 3.043 4.480 (-0.915) (3 / 2 * lam) ≤ Bq 3.043 4.480 (-0.915) (5 / 2 * lam) := by
    unfold Bq; ring_nf; ring_nf at q2 q2' q3 q3' q4 q4'; linarith
  refine ⟨10, h0, sa, _, _, tO 10, h53, h3O, hp, hd, hH₀, hH, hz3, hz5, 3.043, 4.480, -0.915, 1,
    one_pos, le_rfl, le_rfl, le_rfl, by rw [hz5]; exact pos5_of _ _ _ hB5, ?_⟩
  rw [not_lt]; exact box_core _ _ _ hB3 hB5 hb

end Checked.Trust.NCAQ
