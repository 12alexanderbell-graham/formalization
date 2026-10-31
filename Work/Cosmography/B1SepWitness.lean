import Work.Cosmography.B1Separation

/-!
# Non-vacuity of `cubic_separation` / `cubic_direction` (run 2026-10-31T0828Z)

All hypotheses hold at once: the exact flat ΛCDM model `a = sinh(3t/2)^{2/3}` with `Ω = 1/5`
(`Checked.Cosmography.B1.exists_flatLCDM_on`) and the cubic `a₂ = 0`, `a₃ = 147/25`, `H = 1`, with
the offset `c` midway between the two misses. Needs an upper bound on `J₇(1/5)` (secant
certificate, `runs/2026-10-31T0828Z/scripts/emit_j7up.py`).
-/

namespace Work.Cosmography.B1SepWitness

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1
  Work.Cosmography.B1Sep

def pJ7 : List ℕ := [44895, 44920, 44949, 44980, 45015, 45054, 45097, 45144, 45196, 45254, 45317, 45386, 45462, 45545, 45635, 45733, 45840, 45955, 46080, 46216, 46362, 46519, 46689, 46871, 47067, 47277, 47501, 47742, 47998, 48271, 48562, 48872, 49201, 49549, 49919, 50310, 50724, 51160, 51621, 52106, 52616, 53153, 53716, 54306, 54925, 55573, 56249, 56956, 57694, 58463, 59263, 60096, 60962, 61860, 62793, 63760, 64762, 65798, 66870, 67978, 69122, 70302, 71520, 72774, 74066, 75395, 76762, 78167, 79611, 81093, 82614, 84174, 85773, 87412, 89090, 90808, 92566, 94364, 96202, 98080]
def qJ7 : List ℕ := [44896, 44921, 44950, 44981, 45016, 45055, 45098, 45145, 45197, 45255, 45318, 45387, 45463, 45546, 45636, 45734, 45841, 45956, 46081, 46217, 46363, 46520, 46690, 46872, 47068, 47278, 47502, 47743, 47999, 48272, 48563, 48873, 49202, 49550, 49920, 50311, 50725, 51161, 51622, 52107, 52617, 53154, 53717, 54307, 54926, 55574, 56250, 56957, 57695, 58464, 59264, 60097, 60963, 61861, 62794, 63761, 64763, 65799, 66871, 67979, 69123, 70303, 71521, 72775, 74067, 75396, 76763, 78168, 79612, 81094, 82615, 84175, 85774, 87413, 89091, 90809, 92567, 94365, 96203, 98081]

set_option maxHeartbeats 8000000 in
lemma J7_upper_fifth : ∫ v in (3535/10000:ℝ)..1, gL (1/5) v ≤ 233 / 100 := by
  have hp1 : ∀ i : ℕ, i < 80 → ((pJ7.getD i 0 : ℝ) / 100000) ^ 2 ≤
      (1/5 : ℝ) + (1 - 1/5) * (3535/10000 + (i:ℝ) * (1293/160000)) ^ 6 := by
    intro i hi; interval_cases i <;> norm_num [pJ7]
  have hq1 : ∀ i : ℕ, i < 80 → (1/5 : ℝ) + (1 - 1/5) * (3535/10000 + (i:ℝ) * (1293/160000)) ^ 6 ≤
      ((qJ7.getD i 0 : ℝ) / 100000) ^ 2 := by
    intro i hi; interval_cases i <;> norm_num [qJ7]
  have hpp : ∀ i : ℕ, i < 80 → (0:ℝ) < (pJ7.getD i 0 : ℝ) / 100000 := by
    intro i hi; interval_cases i <;> norm_num [pJ7]
  have hqp : ∀ i : ℕ, i < 80 → (0:ℝ) < (qJ7.getD i 0 : ℝ) / 100000 := by
    intro i hi; interval_cases i <;> norm_num [qJ7]
  have key := J_upper (1/5) (by norm_num) (by norm_num) (3535/10000) (1293/160000) (by norm_num)
    (by norm_num) 80 (fun i => (pJ7.getD i 0 : ℝ) / 100000) (fun i => (qJ7.getD i 0 : ℝ) / 100000)
    hpp hqp hp1 hq1
  have e : (3535/10000:ℝ) + ((80:ℕ):ℝ) * (1293/160000) = 1 := by norm_num
  rw [e] at key
  refine le_trans key ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pJ7, qJ7]
  norm_num

/-- Numerical core: `0.96 ≤ Y ≤ 1.04` for `Y = 2 J₇ P₃ /(J₃ P₇)` given the enclosures. -/
lemma ratio_bounds (J3 J7 t : ℝ)
    (hJ3l : (1588549 / 800000 : ℝ) - (173265881 / 100000000 : ℝ) * (1/5) ≤ J3)
    (hJ3u : J3 ≤ (203715349 / 100000000 : ℝ) + (-91364007 / 50000000 : ℝ) * (1/5))
    (hJ7l : (141929311 / 50000000 : ℝ) - (284250829 / 100000000 : ℝ) * (1/5) ≤ J7)
    (hJ7u : J7 ≤ 233 / 100) (htl : (899 / 10000 : ℝ) ≤ t) (htu : t ≤ 9063 / 100000) :
    96 / 100 * J3 * (3 + 27 * (147 / 25) * t) ≤ 2 * J7 * (2 + 8 * (147 / 25) * t) ∧
      2 * J7 * (2 + 8 * (147 / 25) * t) ≤ 104 / 100 * J3 * (3 + 27 * (147 / 25) * t) := by
  have hN : 0 ≤ 3 + 27 * (147 / 25 : ℝ) * t := by nlinarith
  have hD : 0 ≤ 2 + 8 * (147 / 25 : ℝ) * t := by nlinarith
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hJ3u) hN, mul_nonneg (sub_nonneg.2 hJ7l) hD]
  · nlinarith [mul_nonneg (sub_nonneg.2 hJ3l) hN, mul_nonneg (sub_nonneg.2 hJ7u) hD]

lemma small_div (L l : ℝ) (hu : L ≤ 4 / 100) (hlo : -(1 / 24) ≤ L) (hl : 23 / 10 ≤ l) :
    5 * L / l ≤ 1 / 10 ∧ -(1 / 10) ≤ 5 * L / l := by
  have hl0 : 0 < l := by linarith
  constructor
  · rw [div_le_iff₀ hl0]; nlinarith
  · rw [le_div_iff₀ hl0]; nlinarith

lemma mid_abs (d3 d7 : ℝ) (h1 : d7 - d3 ≤ 1 / 10) (h2 : -(1 / 10) ≤ d7 - d3) :
    |d3 - (d3 + d7) / 2| ≤ 1 / 20 ∧ |d7 - (d3 + d7) / 2| ≤ 1 / 20 := by
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- **Non-vacuity of `cubic_separation` and `cubic_direction`:** every hypothesis holds at once. -/
theorem hyps_satisfiable : ∃ (Ω : ℝ) (a : ℝ → ℝ) (t₇ t₃ t₀ a₂ a₃ H c : ℝ),
    1 / 5 ≤ Ω ∧ Ω ≤ 2 / 5 ∧ t₇ ≤ t₃ ∧ t₃ ≤ t₀ ∧
    (∀ s ∈ Set.Icc t₇ t₀, 0 < a s) ∧ (∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s) ∧
    0 < hubble a t₀ ∧
    (∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) ∧
    redshift a t₀ t₃ = 3 ∧ redshift a t₀ t₇ = 7 ∧ 0 < H ∧
    0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃) ∧ 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₇) ∧
    |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20 ∧
    |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₇)) - c|
      ≤ 1 / 20 := by
  obtain ⟨a, t₇, t₃, t₀, h₇₃, h₃₀, hpos, hdiff, hH₀, hH, hz₃, hz₇⟩ := exists_flatLCDM_on
  have hsub : Set.Icc t₃ t₀ ⊆ Set.Icc t₇ t₀ := Set.Icc_subset_Icc_left h₇₃
  have hbr3 := lumDistFlat_flatLCDM (1/5) (by norm_num) (by norm_num) a t₃ t₀ h₃₀
    (fun s hs => hpos s (hsub hs)) (fun s hs => hdiff s (hsub hs)) hH₀ (fun s hs => hH s (hsub hs))
  have hbr7 := lumDistFlat_flatLCDM (1/5) (by norm_num) (by norm_num) a t₇ t₀ (le_trans h₇₃ h₃₀)
    hpos hdiff hH₀ hH
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h₇₃, h₃₀⟩
  have ha7 : 0 < a t₇ := hpos t₇ ⟨le_rfl, le_trans h₇₃ h₃₀⟩
  have hw : √(1 / (1 + 3) : ℝ) = 1 / 2 := by
    rw [show (1 / (1 + 3) : ℝ) = (1 / 2) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [ratio_of_z a t₃ t₀ 3 ha3 (hpos t₀ ⟨le_trans h₇₃ h₃₀, le_rfl⟩) hz₃, hw] at hbr3
  rw [ratio_of_z a t₇ t₀ 7 ha7 (hpos t₀ ⟨le_trans h₇₃ h₃₀, le_rfl⟩) hz₇] at hbr7
  change lumDistFlat a t₀ t₃ = (1 + redshift a t₀ t₃) / hubble a t₀ * ∫ v in (1/2:ℝ)..1, gL (1/5) v
    at hbr3
  change lumDistFlat a t₀ t₇ = (1 + redshift a t₀ t₇) / hubble a t₀ *
    ∫ v in √(1 / (1 + 7) : ℝ)..1, gL (1/5) v at hbr7
  rw [hz₃] at hbr3
  rw [hz₇] at hbr7
  set J3 := ∫ v in (1/2:ℝ)..1, gL (1/5) v with hJ3def
  set J7 := ∫ v in √(1 / (1 + 7) : ℝ)..1, gL (1/5) v with hJ7def
  set H₀ := hubble a t₀ with hH₀def
  have hJ3l := (J3_lower (1/5) (by norm_num) (by norm_num)).1 (by norm_num)
  have hJ3u := J3_upper0 (1/5) (by norm_num) (by norm_num)
  have hJ7l := (J7_lower (1/5) (by norm_num) (by norm_num)).1 (by norm_num)
  have hJ7u : J7 ≤ 233 / 100 := by
    have hs : (3535 / 10000 : ℝ) ≤ √(1 / (1 + 7) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hs1 : √(1 / (1 + 7) : ℝ) ≤ 1 := by
      rw [Real.sqrt_le_one]; norm_num
    exact le_trans (J_shift (1/5) (by norm_num) (by norm_num) _ _ (by norm_num) hs hs1)
      J7_upper_fifth
  have hJ3p : 0 < J3 := by linarith
  have hJ7p : 0 < J7 := by linarith
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  have hlu : l < 10 / 3 * 0.6931471808 := log_ten_lt
  have hll : (10 * 0.6931471803 - 24 / 1000) / 3 ≤ l := log_ten_ge
  have hℓl : (0.6931471803 : ℝ) < ℓ := Real.log_two_gt_d9
  have hℓu : ℓ < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  set t := ℓ ^ 2 / l ^ 2 with ht
  have htl : (899 / 10000 : ℝ) ≤ t := by
    rw [ht, le_div_iff₀ (by positivity)]
    have : l ^ 2 ≤ (10 / 3 * 0.6931471808) ^ 2 := pow_le_pow_left₀ hl0.le hlu.le 2
    have : (0.6931471803 : ℝ) ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by norm_num) hℓl.le 2
    nlinarith
  have htu : t ≤ 9063 / 100000 := by
    rw [ht, div_le_iff₀ (by positivity)]
    have : ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ (by norm_num) hll 2
    have : ℓ ^ 2 ≤ (0.6931471808 : ℝ) ^ 2 := pow_le_pow_left₀ hℓ0.le hℓu.le 2
    nlinarith
  obtain ⟨hlo, hhi⟩ := ratio_bounds J3 J7 t hJ3l hJ3u hJ7l hJ7u htl htu
  -- the polynomial values
  have hP3 : logPolyDL3 0 (147 / 25) 1 3 = ℓ * (2 + 8 * (147 / 25) * t) := by
    rw [poly_gen 0 (147 / 25) 1 3 one_ne_zero, show (1:ℝ) + 3 = 2 ^ 2 by norm_num, Real.log_pow,
      ht]
    field_simp; ring
  have hP7 : logPolyDL3 0 (147 / 25) 1 7 = ℓ * (3 + 27 * (147 / 25) * t) := by
    rw [poly_gen 0 (147 / 25) 1 7 one_ne_zero, show (1:ℝ) + 7 = 2 ^ 3 by norm_num, Real.log_pow,
      ht]
    field_simp; ring
  have hD3 : 0 < 2 + 8 * (147 / 25 : ℝ) * t := by nlinarith
  have hD7 : 0 < 3 + 27 * (147 / 25 : ℝ) * t := by nlinarith
  set X3 := (1 + 3) / H₀ * J3 / (ℓ * (2 + 8 * (147 / 25) * t)) with hX3
  set X7 := (1 + 7) / H₀ * J7 / (ℓ * (3 + 27 * (147 / 25) * t)) with hX7
  have hX3p : 0 < X3 := by positivity
  have hX7p : 0 < X7 := by positivity
  set Y := X7 / X3 with hY
  have hYe : Y = 2 * J7 * (2 + 8 * (147 / 25) * t) / (J3 * (3 + 27 * (147 / 25) * t)) := by
    rw [hY, hX7, hX3]; field_simp; ring
  have hYp : 0 < Y := by positivity
  have hYl : 96 / 100 ≤ Y := by rw [hYe, le_div_iff₀ (by positivity)]; linarith
  have hYu : Y ≤ 104 / 100 := by rw [hYe, div_le_iff₀ (by positivity)]; linarith
  have hlogu : Real.log Y ≤ 4 / 100 := by linarith [Real.log_le_sub_one_of_pos hYp]
  have hlogl : -(1 / 24) ≤ Real.log Y := by
    have h1 := Real.one_sub_inv_le_log_of_pos hYp
    have h2 : Y⁻¹ ≤ (96 / 100)⁻¹ := inv_anti₀ (by norm_num) hYl
    norm_num at h2; linarith
  have hdiffY : 5 * Real.logb 10 X7 - 5 * Real.logb 10 X3 = 5 * Real.log Y / l := by
    rw [hY, Real.log_div hX7p.ne' hX3p.ne']; unfold Real.logb; ring
  have hl2 : (23 / 10 : ℝ) ≤ l := by linarith
  obtain ⟨hb1, hb2⟩ := small_div (Real.log Y) l hlogu hlogl hl2
  rw [← hdiffY] at hb1 hb2
  obtain ⟨hm3, hm7⟩ := mid_abs _ _ hb1 hb2
  refine ⟨1 / 5, a, t₇, t₃, t₀, 0, 147 / 25, 1,
    (5 * Real.logb 10 X3 + 5 * Real.logb 10 X7) / 2, by norm_num, by norm_num, h₇₃, h₃₀, hpos,
    hdiff, hH₀, hH, hz₃, hz₇, one_pos, ?_, ?_, ?_, ?_⟩
  · rw [hz₃, hP3]; positivity
  · rw [hz₇, hP7]; positivity
  · rw [hbr3, hz₃, hP3]; exact hm3
  · rw [hbr7, hz₇, hP7]; exact hm7

end Work.Cosmography.B1SepWitness
