import Checked.Trust.NecessityBQ

/-!
# Hypothesis necessity, the RL19 box: the expansion law (trust track T2b)

Run 2026-11-25T0028Z. Without its expansion law, `B1FitRL19.rl19_box_unmatched` is false: the scale factor `cs`
coasts (`a = t`) after the time where it is five ninths of its present value and grows like a square root before
it (the two pieces have the same value and slope there, so `cs` is differentiable); its comoving distances are a
logarithm after that time and a square root before it, in closed form (`cs_d1`, `cs_d3`, `cs_d5`). A cubic inside
the box (second coefficient three and forty-eight hundredths, third one and sixty-nine hundredths) matches its
three distance moduli within a twentieth of a magnitude (each ratio within two percent of one, `resid_band`); the
logarithm of nine fifths is enclosed by the series of the logarithm of nine tenths (`log95_bd`).

Shape found by a float scan of two-piece power laws (`runs/2026-11-25T0028Z/scripts/scan_r9.py`); numbers checked
in exact rationals there; Lean checks every one.
-/

namespace Checked.Trust.NCBR

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Set
open Checked.Trust.NCAQ Checked.Trust.NCAR

/-- Coasting (`a = t`) from `t = 5/9` on, a square root `√(10t/9 − 25/81)` before it: the two pieces have the
same value and the same slope at `5/9`. -/
noncomputable def cs (t : ℝ) : ℝ := if 5 / 9 ≤ t then t else √(10 / 9 * t - 25 / 81)

theorem cs_hi (t : ℝ) (h : 5 / 9 ≤ t) : cs t = t := by simp [cs, h]

theorem cs_lo (t : ℝ) (h : t < 5 / 9) : cs t = √(10 / 9 * t - 25 / 81) := by simp [cs, not_le.2 h]

theorem cs_sq59 : √(10 / 9 * (5 / 9) - 25 / 81 : ℝ) = 5 / 9 := by
  rw [show (10 / 9 * (5 / 9) - 25 / 81 : ℝ) = (5 / 9) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem cs_le (t : ℝ) (h : t ≤ 5 / 9) : cs t = √(10 / 9 * t - 25 / 81) := by
  rcases lt_or_eq_of_le h with h | h
  · exact cs_lo t h
  · rw [h, cs_hi _ le_rfl, cs_sq59]

theorem cs_root_deriv (t : ℝ) (ht : 5 / 18 < t) :
    HasDerivAt (fun s => √(10 / 9 * s - 25 / 81)) (5 / 9 / √(10 / 9 * t - 25 / 81)) t := by
  have h1 : HasDerivAt (fun s : ℝ => 10 / 9 * s - 25 / 81) (10 / 9) t := by
    simpa using ((hasDerivAt_id t).const_mul (10 / 9 : ℝ)).sub_const (25 / 81 : ℝ)
  have hp : 0 < 10 / 9 * t - 25 / 81 := by linarith
  have h2 := h1.sqrt hp.ne'
  convert h2 using 1
  have : 0 < √(10 / 9 * t - 25 / 81) := Real.sqrt_pos.2 hp
  field_simp
  ring

theorem cs_deriv_hi (t : ℝ) (ht : 5 / 9 < t) : HasDerivAt cs 1 t := by
  apply (hasDerivAt_id t).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact cs_hi s (le_of_lt hs)

theorem cs_deriv_lo (t : ℝ) (ht : 5 / 18 < t) (ht' : t < 5 / 9) :
    HasDerivAt cs (5 / 9 / √(10 / 9 * t - 25 / 81)) t := by
  apply (cs_root_deriv t ht).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht'] with s hs
  exact cs_lo s hs

theorem cs_deriv_mid : HasDerivAt cs 1 (5 / 9) := by
  have hR : HasDerivWithinAt cs 1 (Ici (5 / 9)) (5 / 9) :=
    (hasDerivAt_id (5 / 9 : ℝ)).hasDerivWithinAt.congr (fun s hs => cs_hi s hs) (cs_hi _ le_rfl)
  have hL0 := (cs_root_deriv (5 / 9) (by norm_num)).hasDerivWithinAt (s := Iic (5 / 9))
  rw [cs_sq59, show (5 / 9 : ℝ) / (5 / 9) = 1 by norm_num] at hL0
  have hL : HasDerivWithinAt cs 1 (Iic (5 / 9)) (5 / 9) :=
    hL0.congr (fun s hs => cs_le s hs) (cs_le _ le_rfl)
  have := hL.union hR
  rw [Iic_union_Ici] at this
  exact hasDerivWithinAt_univ.mp this

theorem cs_diff (t : ℝ) (ht : 5 / 18 < t) : DifferentiableAt ℝ cs t := by
  rcases lt_trichotomy t (5 / 9) with h | h | h
  · exact (cs_deriv_lo t ht h).differentiableAt
  · rw [h]; exact cs_deriv_mid.differentiableAt
  · exact (cs_deriv_hi t h).differentiableAt

theorem cs_pos (t : ℝ) (ht : 5 / 18 < t) : 0 < cs t := by
  rcases le_or_gt (5 / 9) t with h | h
  · rw [cs_hi t h]; linarith
  · rw [cs_lo t h]; exact Real.sqrt_pos.2 (by linarith)

theorem cs_one : cs 1 = 1 := cs_hi 1 (by norm_num)

theorem cs_H0 : hubble cs 1 = 1 := by
  unfold hubble; rw [(cs_deriv_hi 1 (by norm_num)).deriv, cs_one]; norm_num

/-- The three source times. -/
theorem s2_half : (5 / 9 : ℝ) ≤ √2 / 2 := by
  obtain ⟨a, -⟩ := sqrt2_bd; linarith

theorem sq8 : √(1 / 8 : ℝ) = √2 / 4 := by
  rw [show (1 / 8 : ℝ) = (√2 / 4) ^ 2 by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
  exact Real.sqrt_sq (by positivity)

theorem sq32 : √(1 / 32 : ℝ) = √2 / 8 := by
  rw [show (1 / 32 : ℝ) = (√2 / 8) ^ 2 by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num]
  exact Real.sqrt_sq (by positivity)

theorem cs_t1 : cs (√2 / 2) = √2 / 2 := cs_hi _ s2_half

theorem cs_t3 : cs (281 / 720) = √2 / 4 := by
  rw [cs_lo _ (by norm_num), show (10 / 9 * (281 / 720) - 25 / 81 : ℝ) = 1 / 8 by norm_num, sq8]

theorem cs_t5 : cs (881 / 2880) = √2 / 8 := by
  rw [cs_lo _ (by norm_num), show (10 / 9 * (881 / 2880) - 25 / 81 : ℝ) = 1 / 32 by norm_num, sq32]

theorem cs_z1 : redshift cs 1 (√2 / 2) = √2 - 1 := by
  have hq : 0 < √2 := by positivity
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold redshift; rw [cs_one, cs_t1]; field_simp; nlinarith [h2]

theorem cs_z3 : redshift cs 1 (281 / 720) = 2 * √2 - 1 := by
  have hq : 0 < √2 := by positivity
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold redshift; rw [cs_one, cs_t3]; field_simp; nlinarith [h2]

theorem cs_z5 : redshift cs 1 (881 / 2880) = 4 * √2 - 1 := by
  have hq : 0 < √2 := by positivity
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold redshift; rw [cs_one, cs_t5]; field_simp; nlinarith [h2]

/-- The coasting piece of the comoving integral. -/
theorem int_hi (t : ℝ) (ht : 5 / 9 ≤ t) (ht1 : t ≤ 1) :
    ∫ s in t..1, 1 / cs s = Real.log (1 / t) := by
  have ht0 : 0 < t := by linarith
  rw [intervalIntegral.integral_congr (g := fun s => 1 / s)]
  · exact integral_one_div_of_pos ht0 one_pos
  · intro s hs
    rw [uIcc_of_le ht1] at hs
    show 1 / cs s = 1 / s
    rw [cs_hi s (le_trans ht hs.1)]

/-- The square-root piece. -/
theorem int_lo (t : ℝ) (ht : 5 / 18 < t) (ht' : t ≤ 5 / 9) :
    ∫ s in t..5 / 9, 1 / cs s = 1 - 9 / 5 * √(10 / 9 * t - 25 / 81) := by
  rw [intervalIntegral.integral_congr (g := fun s => 5 / 9 / √(10 / 9 * s - 25 / 81) * (9 / 5))]
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => 9 / 5 * √(10 / 9 * s - 25 / 81))]
    · show 9 / 5 * √(10 / 9 * (5 / 9) - 25 / 81) - 9 / 5 * √(10 / 9 * t - 25 / 81) = _
      rw [cs_sq59]; ring
    · intro s hs
      rw [uIcc_of_le ht'] at hs
      have := (cs_root_deriv s (by linarith [hs.1])).const_mul (9 / 5 : ℝ)
      convert this using 1; ring
    · apply ContinuousOn.intervalIntegrable
      intro s hs
      rw [uIcc_of_le ht'] at hs
      have hp : 0 < 10 / 9 * s - 25 / 81 := by linarith [hs.1]
      have hc : ContinuousAt (fun x => √(10 / 9 * x - 25 / 81)) s :=
        (cs_root_deriv s (by linarith [hs.1])).continuousAt
      exact ((continuousAt_const.div hc (Real.sqrt_pos.2 hp).ne').mul continuousAt_const).continuousWithinAt
  · intro s hs
    rw [uIcc_of_le ht'] at hs
    have hp : 0 < 10 / 9 * s - 25 / 81 := by linarith [hs.1]
    simp only [cs_le s hs.2]
    field_simp

theorem cs_intble (t u : ℝ) (ht : 5 / 18 < t) (htu : t ≤ u) :
    IntervalIntegrable (fun s => 1 / cs s) MeasureTheory.volume t u := by
  apply ContinuousOn.intervalIntegrable_of_Icc htu
  intro x hx
  have hx0 : 5 / 18 < x := lt_of_lt_of_le ht hx.1
  exact (continuousAt_const.div (cs_diff x hx0).continuousAt (cs_pos x hx0).ne').continuousWithinAt

theorem int_split (t : ℝ) (ht : 5 / 18 < t) (ht' : t ≤ 5 / 9) :
    ∫ s in t..1, 1 / cs s = 1 - 9 / 5 * √(10 / 9 * t - 25 / 81) + Real.log (9 / 5) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (cs_intble t (5 / 9) ht ht')
    (cs_intble (5 / 9) 1 (by norm_num) (by norm_num)), int_lo t ht ht', int_hi _ le_rfl (by norm_num)]
  norm_num

theorem cs_d1 : lumDistFlat cs 1 (√2 / 2) = √2 * (Real.log 2 / 2) := by
  unfold lumDistFlat comoving
  rw [cs_z1, cs_one, int_hi _ s2_half (by obtain ⟨-, b⟩ := sqrt2_bd; linarith)]
  have hq : 0 < √2 := by positivity
  rw [show (1 : ℝ) / (√2 / 2) = √2 by field_simp; rw [Real.sq_sqrt (by norm_num)], Real.log_sqrt (by norm_num)]
  ring

theorem cs_d3 : lumDistFlat cs 1 (281 / 720) = 2 * √2 * (1 + Real.log (9 / 5)) - 9 / 5 := by
  unfold lumDistFlat comoving
  rw [cs_z3, cs_one, int_split _ (by norm_num) (by norm_num),
    show (10 / 9 * (281 / 720) - 25 / 81 : ℝ) = 1 / 8 by norm_num, sq8]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (-(9:ℝ) / 10) * h2

theorem cs_d5 : lumDistFlat cs 1 (881 / 2880) = 4 * √2 * (1 + Real.log (9 / 5)) - 9 / 5 := by
  unfold lumDistFlat comoving
  rw [cs_z5, cs_one, int_split _ (by norm_num) (by norm_num),
    show (10 / 9 * (881 / 2880) - 25 / 81 : ℝ) = 1 / 32 by norm_num, sq32]
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (-(9:ℝ) / 10) * h2

theorem log95_bd : (0.58778656 : ℝ) ≤ Real.log (9 / 5) ∧ Real.log (9 / 5) ≤ (0.5877868 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 10 : ℝ)| < 1 by norm_num [abs_lt]) 6
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have e : Real.log (9 / 5) = Real.log 2 + Real.log (1 - 1 / 10) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have a := Real.log_two_gt_d9
  have b := Real.log_two_lt_d9
  rw [e]
  norm_num at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem cd1_bd : (0.490127 : ℝ) ≤ √2 * (Real.log 2 / 2) ∧ √2 * (Real.log 2 / 2) ≤ (0.490132 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  have c := Real.log_two_gt_d9
  have d := Real.log_two_lt_d9
  constructor <;> nlinarith

theorem cd3_bd : (2.690927 : ℝ) ≤ 2 * √2 * (1 + Real.log (9 / 5)) - 9 / 5 ∧
    2 * √2 * (1 + Real.log (9 / 5)) - 9 / 5 ≤ (2.69096 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  obtain ⟨c, d⟩ := log95_bd
  constructor <;> nlinarith

theorem cd5_bd : (7.181854 : ℝ) ≤ 4 * √2 * (1 + Real.log (9 / 5)) - 9 / 5 ∧
    4 * √2 * (1 + Real.log (9 / 5)) - 9 / 5 ≤ (7.18192 : ℝ) := by
  obtain ⟨a, b⟩ := sqrt2_bd
  obtain ⟨c, d⟩ := log95_bd
  constructor <;> nlinarith

theorem B_r9_1 : (0.235094 : ℝ) ≤ Bc (87 / 25 : ℝ) (169 / 100 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (87 / 25 : ℝ) (169 / 100 : ℝ) (1 / 2 * (Real.log 2 / Real.log 10)) ≤ (0.235138 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_r9_3 : (1.316529 : ℝ) ≤ Bc (87 / 25 : ℝ) (169 / 100 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (87 / 25 : ℝ) (169 / 100 : ℝ) (3 / 2 * (Real.log 2 / Real.log 10)) ≤ (1.316841 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

theorem B_r9_5 : (3.443421 : ℝ) ≤ Bc (87 / 25 : ℝ) (169 / 100 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ∧
    Bc (87 / 25 : ℝ) (169 / 100 : ℝ) (5 / 2 * (Real.log 2 / Real.log 10)) ≤ (3.444333 : ℝ) := by
  obtain ⟨l1, l2⟩ := lam_bd
  set lam := Real.log 2 / Real.log 10
  have q2 := pow_le_pow_left₀ (by norm_num) l1 2
  have q2' := pow_le_pow_left₀ (by linarith) l2 2
  have q3 := pow_le_pow_left₀ (by norm_num) l1 3
  have q3' := pow_le_pow_left₀ (by linarith) l2 3
  unfold Bc; constructor <;> (ring_nf; ring_nf at q2 q2' q3 q3'; linarith)

/-- Without the expansion law: the coasting scale factor with a square-root past (`cs`); the box cubic
`a₂ = 87/25`, `a₃ = 169/100` matches all three distance moduli (the law's density read as one). -/
theorem rl19_box_unmatched_h9 : necessity% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 9 := by
  obtain ⟨l1, l2⟩ := log10_bd
  obtain ⟨q1, q2⟩ := sqrt2_bd
  have hS : ∀ s ∈ Set.Icc (881 / 2880 : ℝ) 1, 5 / 18 < s := fun s hs => by linarith [hs.1]
  refine ⟨1, by norm_num, le_rfl, cs, 881 / 2880, 281 / 720, √2 / 2, 1, by norm_num, by linarith,
    by linarith, fun s hs => cs_pos s (hS s hs), fun s hs => cs_diff s (hS s hs), by rw [cs_H0]; norm_num,
    cs_z1, cs_z3, cs_z5, (87 / 25 : ℝ), (169 / 100 : ℝ), 1.1153, 0, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [cs_z1, poly3_eq _ _ _ (1 / 2) _ log_s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_r9_1.1 (by norm_num) (by norm_num)
  · rw [cs_z3, poly3_eq _ _ _ (3 / 2) _ log_2s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_r9_3.1 (by norm_num) (by norm_num)
  · rw [cs_z5, poly3_eq _ _ _ (5 / 2) _ log_4s2]
    exact pos_of _ _ _ _ _ (by norm_num) l1 B_r9_5.1 (by norm_num) (by norm_num)
  · refine ⟨?_, ?_, ?_⟩
    · rw [cs_d1, cs_z1, poly3_eq _ _ _ (1 / 2) _ log_s2]
      exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_r9_1.1 B_r9_1.2 cd1_bd.1 cd1_bd.2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · rw [cs_d3, cs_z3, poly3_eq _ _ _ (3 / 2) _ log_2s2]
      exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_r9_3.1 B_r9_3.2 cd3_bd.1 cd3_bd.2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · rw [cs_d5, cs_z5, poly3_eq _ _ _ (5 / 2) _ log_4s2]
      exact resid_band _ _ _ _ _ _ _ _ _ _ (by norm_num) l1 l2 B_r9_5.1 B_r9_5.2 cd5_bd.1 cd5_bd.2
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Checked.Trust.NCBR
