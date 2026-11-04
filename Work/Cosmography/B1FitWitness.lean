import Work.Cosmography.B1Fit

/-!
# Non-vacuity of `fit_direction` (run 2026-11-04T0228Z)

All hypotheses hold at once: the exact flat ΛCDM model `a = sinh(3t/2)^{2/3}` with `Ω = 1/5`
(sources placed at `1 + z = √2, 2√2, 4√2` by `t = (2/3) arsinh(2/(1+z)^{3/2})`) and the cubic
`a₂ = 7/4`, `a₃ = 25/4`, `H = 1`, offset `c` = the residual at the middle redshift. Enclosures of
`J₁, J₃, J₅` at `Ω = 1/5` (certificates `runs/2026-11-04T0228Z/scripts/emit_witness.py`).
-/

namespace Work.Cosmography.B1FitWitness

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Work.Cosmography.B1Fit

def cWL1 : List ℕ := [1419204, 1379566, 1340275, 1301439, 1263149, 1225490, 1188531, 1152335, 1116950, 1082417, 1048768, 1016026]

lemma WL1 (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    (102547569 / 250000000 : ℝ) - (124103907 / 1000000000 : ℝ) * Ω ≤ ∫ v in (840897 / 1000000 : ℝ)..1, gL Ω v := by
  have key := sum_lower Ω h0 h1 (840897 / 1000000 : ℝ) (159103 / 12000000 : ℝ) (by norm_num) (by norm_num)
    (fun i => (cWL1.getD i 0 : ℝ) / 1000000) (fun i => by positivity) 12
  have e : (840897 / 1000000 : ℝ) + ((12:ℕ):ℝ) * (159103 / 12000000 : ℝ) = 1 := by norm_num
  rw [e] at key
  refine le_trans ?_ key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cWL1]
  norm_num
  linarith

def pWU1 : List ℕ := [694868, 714616, 735362, 757118, 779895, 803704, 828554, 854455, 881414, 909441, 938542, 968726]
def qWU1 : List ℕ := [714617, 735363, 757119, 779896, 803705, 828555, 854456, 881415, 909442, 938543, 968727, 1000000]

lemma WU1 (Ω : ℝ) (ha : (1 / 5 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 5 : ℝ)) :
    ∫ v in (13139 / 15625 : ℝ)..1, gL Ω v ≤ (205159379 / 500000000 : ℝ) + (-4962847 / 40000000 : ℝ) * Ω := by
  have key := sum_upper Ω (by linarith) (by linarith) (13139 / 15625 : ℝ) (1243 / 93750 : ℝ) (by norm_num) (by norm_num)
    (fun i => (pWU1.getD i 0 : ℝ) / 1000000) (fun i => (qWU1.getD i 0 : ℝ) / 1000000) 12
    (fun i hi => by interval_cases i <;> norm_num [pWU1])
    (fun i hi => by interval_cases i <;> norm_num [qWU1])
    (fun i hi => by interval_cases i <;> norm_num [pWU1] <;> linarith)
    (fun i hi => by interval_cases i <;> norm_num [qWU1] <;> linarith)
  have e : (13139 / 15625 : ℝ) + ((12:ℕ):ℝ) * (1243 / 93750 : ℝ) = 1 := by norm_num
  rw [e] at key
  refine le_trans key ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pWU1, qWU1]
  norm_num
  linarith

def cWL3 : List ℕ := [2033518, 1969691, 1895104, 1810808, 1718567, 1620659, 1519599, 1417854, 1317612, 1220645, 1128253, 1041289]

lemma WL3 (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    (1536440451 / 1000000000 : ℝ) - (137012981 / 100000000 : ℝ) * Ω ≤ ∫ v in (148651 / 250000 : ℝ)..1, gL Ω v := by
  have key := sum_lower Ω h0 h1 (148651 / 250000 : ℝ) (33783 / 1000000 : ℝ) (by norm_num) (by norm_num)
    (fun i => (cWL3.getD i 0 : ℝ) / 1000000) (fun i => by positivity) 12
  have e : (148651 / 250000 : ℝ) + ((12:ℕ):ℝ) * (33783 / 1000000 : ℝ) = 1 := by norm_num
  rw [e] at key
  refine le_trans ?_ key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cWL3]
  norm_num
  linarith

def pWU3 : List ℕ := [485134, 499254, 517143, 539351, 566395, 598741, 636793, 680888, 731301, 788253, 851923, 922461]
def qWU3 : List ℕ := [499255, 517144, 539352, 566396, 598742, 636794, 680889, 731302, 788254, 851924, 922462, 1000000]

lemma WU3 (Ω : ℝ) (ha : (1 / 5 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 5 : ℝ)) :
    ∫ v in (594603 / 1000000 : ℝ)..1, gL Ω v ≤ (768705827 / 500000000 : ℝ) + (-341651851 / 250000000 : ℝ) * Ω := by
  have key := sum_upper Ω (by linarith) (by linarith) (594603 / 1000000 : ℝ) (405397 / 12000000 : ℝ) (by norm_num) (by norm_num)
    (fun i => (pWU3.getD i 0 : ℝ) / 1000000) (fun i => (qWU3.getD i 0 : ℝ) / 1000000) 12
    (fun i hi => by interval_cases i <;> norm_num [pWU3])
    (fun i hi => by interval_cases i <;> norm_num [qWU3])
    (fun i hi => by interval_cases i <;> norm_num [pWU3] <;> linarith)
    (fun i hi => by interval_cases i <;> norm_num [qWU3] <;> linarith)
  have e : (594603 / 1000000 : ℝ) + ((12:ℕ):ℝ) * (405397 / 12000000 : ℝ) = 1 := by norm_num
  rw [e] at key
  refine le_trans key ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pWU3, qWU3]
  norm_num
  linarith

def cWL5 : List ℕ := [2202308, 2174575, 2131525, 2069156, 1984808, 1878350, 1752811, 1613975, 1469031, 1324935, 1187212, 1059482]

lemma WL5 (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    (2628211367 / 1000000000 : ℝ) - (192509947 / 62500000 : ℝ) * Ω ≤ ∫ v in (420449 / 1000000 : ℝ)..1, gL Ω v := by
  have key := sum_lower Ω h0 h1 (420449 / 1000000 : ℝ) (579551 / 12000000 : ℝ) (by norm_num) (by norm_num)
    (fun i => (cWL5.getD i 0 : ℝ) / 1000000) (fun i => by positivity) 12
  have e : (420449 / 1000000 : ℝ) + ((12:ℕ):ℝ) * (579551 / 12000000 : ℝ) = 1 := by norm_num
  rw [e] at key
  refine le_trans ?_ key
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cWL5]
  norm_num
  linarith

def pWU5 : List ℕ := [452127, 456602, 463986, 475518, 492656, 517001, 550158, 593605, 648588, 716081, 796808, 891308]
def qWU5 : List ℕ := [456603, 463987, 475519, 492657, 517002, 550159, 593606, 648589, 716082, 796809, 891309, 1000000]

lemma WU5 (Ω : ℝ) (ha : (1 / 5 : ℝ) ≤ Ω) (hb : Ω ≤ (1 / 5 : ℝ)) :
    ∫ v in (13139 / 31250 : ℝ)..1, gL Ω v ≤ (2629281523 / 1000000000 : ℝ) + (-1533898247 / 500000000 : ℝ) * Ω := by
  have key := sum_upper Ω (by linarith) (by linarith) (13139 / 31250 : ℝ) (6037 / 125000 : ℝ) (by norm_num) (by norm_num)
    (fun i => (pWU5.getD i 0 : ℝ) / 1000000) (fun i => (qWU5.getD i 0 : ℝ) / 1000000) 12
    (fun i hi => by interval_cases i <;> norm_num [pWU5])
    (fun i hi => by interval_cases i <;> norm_num [qWU5])
    (fun i hi => by interval_cases i <;> norm_num [pWU5] <;> linarith)
    (fun i hi => by interval_cases i <;> norm_num [qWU5] <;> linarith)
  have e : (13139 / 31250 : ℝ) + ((12:ℕ):ℝ) * (6037 / 125000 : ℝ) = 1 := by norm_num
  rw [e] at key
  refine le_trans key ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pWU5, qWU5]
  norm_num
  linarith

/-- The exact flat ΛCDM solution with `Ω = 1/5` reaches the three redshifts. -/
theorem exists_model :
    ∃ (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ), t₅ ≤ t₃ ∧ t₃ ≤ t₁ ∧ t₁ ≤ t₀ ∧
      (∀ s ∈ Set.Icc t₅ t₀, 0 < a s) ∧ (∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s) ∧
      0 < hubble a t₀ ∧
      (∀ s ∈ Set.Icc t₅ t₀,
        hubble a s = hubble a t₀ * √(1 / 5 * (1 + redshift a t₀ s) ^ 3 + 1 - 1 / 5)) ∧
      redshift a t₀ t₁ = √2 - 1 ∧ redshift a t₀ t₃ = 2 * √2 - 1 ∧
      redshift a t₀ t₅ = 4 * √2 - 1 := by
  set S : ℝ → ℝ := fun s => Real.sinh (3 / 2 * s) with hS
  set a : ℝ → ℝ := fun s => S s ^ (2 / 3 : ℝ) with ha
  have hSt : ∀ y, S (2 / 3 * Real.arsinh y) = y := by
    intro y; simp only [hS]; rw [show 3 / 2 * (2 / 3 * Real.arsinh y) = Real.arsinh y by ring,
      Real.sinh_arsinh]
  set T : ℝ → ℝ := fun s => 2 / 3 * Real.arsinh (2 / s ^ (3 / 2 : ℝ)) with hT
  have hy0 : ∀ s : ℝ, 1 ≤ s → 0 < 2 / s ^ (3 / 2 : ℝ) := fun s hs =>
    div_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)
  have hTmono : ∀ s s' : ℝ, 1 ≤ s → s ≤ s' → T s' ≤ T s := by
    intro s s' hs hss
    have h1 : s ^ (3 / 2 : ℝ) ≤ s' ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hss (by norm_num)
    have h2 : 2 / s' ^ (3 / 2 : ℝ) ≤ 2 / s ^ (3 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos (by linarith) _) h1
    have := Real.arsinh_le_arsinh.2 h2
    simp only [hT]; linarith
  have hq2 : (1:ℝ) ≤ √2 := by
    rw [show (1:ℝ) = √1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt (by norm_num)
  set t₁ := T √2
  set t₃ := T (2 * √2)
  set t₅ := T (4 * √2)
  set t₀ : ℝ := 2 / 3 * Real.arsinh 2
  have h53 : t₅ ≤ t₃ := hTmono _ _ (by linarith) (by linarith)
  have h31 : t₃ ≤ t₁ := hTmono _ _ (by linarith) (by linarith)
  have h10 : t₁ ≤ t₀ := by
    have h1 : (1:ℝ) ≤ √2 ^ (3 / 2 : ℝ) := Real.one_le_rpow hq2 (by norm_num)
    have h2 : 2 / √2 ^ (3 / 2 : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have := Real.arsinh_le_arsinh.2 h2
    simp only [t₁, t₀, hT]; linarith
  have ht₅ : 0 < t₅ := by
    have := Real.arsinh_pos_iff.2 (hy0 (4 * √2) (by linarith)); simp only [t₅, hT]; positivity
  have hSpos : ∀ s, 0 < s → 0 < S s := by
    intro s hs; simp only [hS]; exact Real.sinh_pos_iff.2 (by positivity)
  have hderS : ∀ s, HasDerivAt S (Real.cosh (3 / 2 * s) * (3 / 2)) s := by
    intro s
    have h := (Real.hasDerivAt_sinh (3 / 2 * s)).comp s ((hasDerivAt_id s).const_mul (3 / 2))
    rw [mul_one] at h; exact h
  have hdera : ∀ s, 0 < s →
      HasDerivAt a (Real.cosh (3 / 2 * s) * (3 / 2) * (2 / 3) * S s ^ ((2 / 3 : ℝ) - 1)) s := by
    intro s hs
    exact (hderS s).rpow_const (Or.inl (hSpos s hs).ne')
  have hhub : ∀ s, 0 < s → hubble a s = Real.cosh (3 / 2 * s) / S s := by
    intro s hs
    have hSs := hSpos s hs
    unfold hubble
    rw [(hdera s hs).deriv]
    simp only [ha]
    rw [Real.rpow_sub hSs, Real.rpow_one]
    have : 0 < S s ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hSs _
    field_simp
  have hcube : ∀ x : ℝ, 0 < x → (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hz3 : ∀ s, 0 < s → (1 + redshift a t₀ s) ^ 3 = 4 / S s ^ 2 := by
    intro s hs
    have hSs := hSpos s hs
    unfold redshift
    simp only [ha]
    rw [hSt 2, show 1 + ((2:ℝ) ^ (2 / 3 : ℝ) / S s ^ (2 / 3 : ℝ) - 1) =
      (2:ℝ) ^ (2 / 3 : ℝ) / S s ^ (2 / 3 : ℝ) by ring, div_pow, hcube 2 (by norm_num),
      hcube _ hSs]
    norm_num
  have hcosh : ∀ s, Real.cosh (3 / 2 * s) = √(1 + S s ^ 2) := by
    intro s
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (Real.cosh_pos _).le]
    simp only [hS]; rw [← sq, Real.cosh_sq]; ring
  have hpos0 : 0 < t₀ := lt_of_lt_of_le ht₅ (le_trans h53 (le_trans h31 h10))
  have hH0 : hubble a t₀ = √5 / 2 := by
    rw [hhub t₀ hpos0, hcosh, hSt 2]; norm_num
  have hred : ∀ s : ℝ, 1 ≤ s → redshift a t₀ (T s) = s - 1 := by
    intro s hs
    have hs0 : 0 ≤ s := by linarith
    unfold redshift; simp only [ha, hT]
    rw [hSt 2, hSt, ← Real.div_rpow (by norm_num) (hy0 s hs).le,
      show (2:ℝ) / (2 / s ^ (3 / 2 : ℝ)) = s ^ (3 / 2 : ℝ) by
        field_simp [(Real.rpow_pos_of_pos (by linarith : (0:ℝ) < s) (3 / 2 : ℝ)).ne'],
      ← Real.rpow_mul hs0]
    norm_num
  refine ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, ?_, ?_, ?_, ?_, hred _ hq2, hred _ (by linarith),
    hred _ (by linarith)⟩
  · intro s hs; exact Real.rpow_pos_of_pos (hSpos s (lt_of_lt_of_le ht₅ hs.1)) _
  · intro s hs; exact (hdera s (lt_of_lt_of_le ht₅ hs.1)).differentiableAt
  · rw [hH0]; positivity
  · intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht₅ hs.1
    have hSs := hSpos s hs0
    rw [hhub s hs0, hH0, hz3 s hs0, hcosh]
    have e : 1 / 5 * (4 / S s ^ 2) + 1 - 1 / 5 = (2 * √(1 + S s ^ 2) / (√5 * S s)) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
      field_simp; ring
    rw [e, Real.sqrt_sq (by positivity)]
    have : (0:ℝ) < √5 := by positivity
    field_simp

lemma log_ten_le : Real.log 10 ≤ (10 * 0.6931471808 - 24 / 1024) / 3 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1000 / 1024 by norm_num)
  have h2 : Real.log (1000 / 1024) = 3 * Real.log 10 - 10 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (1000:ℝ) = 10 ^ 3 by norm_num, show (1024:ℝ) = 2 ^ 10 by norm_num,
      Real.log_pow, Real.log_pow]; push_cast; ring
  rw [h2] at h1
  linarith [Real.log_two_lt_d9]

/-- `log₁₀ 2 ∈ [0.30101, 0.30105]`. -/
lemma t_bounds : (30101 / 100000 : ℝ) ≤ Real.log 2 / Real.log 10 ∧
    Real.log 2 / Real.log 10 ≤ 30105 / 100000 := by
  have hl0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have h1 := log_ten_ge
  have h2 := log_ten_le
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  constructor
  · rw [le_div_iff₀ hl0]; nlinarith
  · rw [div_le_iff₀ hl0]; nlinarith

/-- Ratio enclosure: from enclosures of four positive quantities. -/
lemma ratio_encl (A B α β Al Ah Bl Bh αl αh βl βh κl κu : ℝ)
    (hAl : 0 < Al) (hBl : 0 < Bl) (hαl : 0 < αl) (hβl : 0 < βl)
    (hA : Al ≤ A ∧ A ≤ Ah) (hB : Bl ≤ B ∧ B ≤ Bh) (hα : αl ≤ α ∧ α ≤ αh) (hβ : βl ≤ β ∧ β ≤ βh)
    (hκl : 0 ≤ κl) (h1 : κl * (Bh * βh) ≤ Al * αl) (h2 : Ah * αh ≤ κu * (Bl * βl)) :
    κl * (B * β) ≤ A * α ∧ A * α ≤ κu * (B * β) := by
  have hκu : 0 ≤ κu := by
    by_contra h; rw [not_le] at h
    have : κu * (Bl * βl) < 0 := mul_neg_of_neg_of_pos h (by positivity)
    nlinarith [mul_pos hAl hαl]
  have e1 : B * β ≤ Bh * βh := mul_le_mul hB.2 hβ.2 (by linarith) (by linarith)
  have e2 : Al * αl ≤ A * α := mul_le_mul hA.1 hα.1 hαl.le (by linarith)
  have e3 : A * α ≤ Ah * αh := mul_le_mul hA.2 hα.2 (by linarith) (by linarith)
  have e4 : Bl * βl ≤ B * β := mul_le_mul hB.1 hβ.1 hβl.le (by linarith)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left e1 hκl]
  · nlinarith [mul_le_mul_of_nonneg_left e4 hκu]

lemma log_small (Y l : ℝ) (hY : 99 / 100 ≤ Y ∧ Y ≤ 101 / 100) (hl : 23 / 10 ≤ l) :
    |5 * Real.log Y / l| ≤ 1 / 20 := by
  have hYp : 0 < Y := by linarith
  have hu : Real.log Y ≤ 1 / 100 := by linarith [Real.log_le_sub_one_of_pos hYp]
  have hlo : -(2 / 196) ≤ Real.log Y := by
    have h1 := Real.one_sub_inv_le_log_of_pos hYp
    have h2 : Y⁻¹ ≤ (99 / 100)⁻¹ := inv_anti₀ (by norm_num) hY.1
    norm_num at h2; linarith
  have hl0 : 0 < l := by linarith
  rw [abs_le]; constructor
  · rw [le_div_iff₀ hl0]; nlinarith
  · rw [div_le_iff₀ hl0]; nlinarith

lemma l23 : (23 / 10 : ℝ) ≤ Real.log 10 := by
  have := log_ten_ge; norm_num at this ⊢; linarith

lemma logb_diff (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) :
    5 * Real.logb 10 X - 5 * Real.logb 10 Y = 5 * Real.log (X / Y) / Real.log 10 := by
  rw [Real.log_div hX.ne' hY.ne']; unfold Real.logb; ring

lemma pq_bounds (c0 c1 c2 t : ℝ) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (htl : 30101 / 100000 ≤ t)
    (htu : t ≤ 30105 / 100000) :
    c0 + c1 * (30101 / 100000) + c2 * (30101 / 100000) ^ 2 ≤ c0 + c1 * t + c2 * t ^ 2 ∧
      c0 + c1 * t + c2 * t ^ 2 ≤ c0 + c1 * (30105 / 100000) + c2 * (30105 / 100000) ^ 2 := by
  have e1 : (30101 / 100000 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) htl 2
  have e2 : t ^ 2 ≤ (30105 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) htu 2
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left htl h1, mul_le_mul_of_nonneg_left e1 h2]
  · nlinarith [mul_le_mul_of_nonneg_left htu h1, mul_le_mul_of_nonneg_left e2 h2]

/-- **Non-vacuity of `fit_direction`:** every hypothesis holds at once. -/
theorem hyps_satisfiable : ∃ (Ω : ℝ) (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ a₂ a₃ H c : ℝ),
    0 ≤ Ω ∧ Ω ≤ 1 ∧ t₅ ≤ t₃ ∧ t₃ ≤ t₁ ∧ t₁ ≤ t₀ ∧
    (∀ s ∈ Set.Icc t₅ t₀, 0 < a s) ∧ (∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s) ∧
    0 < hubble a t₀ ∧
    (∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) ∧
    redshift a t₀ t₁ = √2 - 1 ∧ redshift a t₀ t₃ = 2 * √2 - 1 ∧
    redshift a t₀ t₅ = 4 * √2 - 1 ∧ 0 < H ∧
    0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁) ∧ 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃) ∧
    0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅) ∧
    |5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
      ≤ 1 / 20 ∧
    |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20 ∧
    |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
      ≤ 1 / 20 := by
  obtain ⟨a, t₅, t₃, t₁, t₀, h53, h31, h10, hpos, hdiff, hH₀, hH, hz₁, hz₃, hz₅⟩ := exists_model
  have hΩ0 : (0:ℝ) ≤ 1 / 5 := by norm_num
  have hΩ1 : (1:ℝ) / 5 ≤ 1 := by norm_num
  obtain ⟨hq2l, hq2u⟩ := sqrt2_bounds
  have hq2 : 0 < √2 := by linarith
  have h₃₀ : t₃ ≤ t₀ := le_trans h31 h10
  have h₅₀ : t₅ ≤ t₀ := le_trans h53 h₃₀
  have hsub1 : Set.Icc t₁ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left (le_trans h53 h31)
  have hsub3 : Set.Icc t₃ t₀ ⊆ Set.Icc t₅ t₀ := Set.Icc_subset_Icc_left h53
  have hbr1 := lumDistFlat_flatLCDM (1/5) hΩ0 hΩ1 a t₁ t₀ h10 (fun s hs => hpos s (hsub1 hs))
    (fun s hs => hdiff s (hsub1 hs)) hH₀ (fun s hs => hH s (hsub1 hs))
  have hbr3 := lumDistFlat_flatLCDM (1/5) hΩ0 hΩ1 a t₃ t₀ h₃₀ (fun s hs => hpos s (hsub3 hs))
    (fun s hs => hdiff s (hsub3 hs)) hH₀ (fun s hs => hH s (hsub3 hs))
  have hbr5 := lumDistFlat_flatLCDM (1/5) hΩ0 hΩ1 a t₅ t₀ h₅₀ hpos hdiff hH₀ hH
  have ha₀ : 0 < a t₀ := hpos t₀ ⟨h₅₀, le_rfl⟩
  have ha1 : 0 < a t₁ := hpos t₁ ⟨le_trans h53 h31, h10⟩
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h53, h₃₀⟩
  have ha5 : 0 < a t₅ := hpos t₅ ⟨le_rfl, h₅₀⟩
  have es1 : (1:ℝ) + (√2 - 1) = √2 := by ring
  have es3 : (1:ℝ) + (2 * √2 - 1) = 2 * √2 := by ring
  have es5 : (1:ℝ) + (4 * √2 - 1) = 4 * √2 := by ring
  rw [ratio_of_z a t₁ t₀ _ ha1 ha₀ hz₁, es1, hz₁, es1] at hbr1
  rw [ratio_of_z a t₃ t₀ _ ha3 ha₀ hz₃, es3, hz₃, es3] at hbr3
  rw [ratio_of_z a t₅ t₀ _ ha5 ha₀ hz₅, es5, hz₅, es5] at hbr5
  change lumDistFlat a t₀ t₁ = √2 / hubble a t₀ * ∫ v in √(1 / √2)..1, gL (1/5) v at hbr1
  change lumDistFlat a t₀ t₃ = 2 * √2 / hubble a t₀ * ∫ v in √(1 / (2 * √2))..1, gL (1/5) v
    at hbr3
  change lumDistFlat a t₀ t₅ = 4 * √2 / hubble a t₀ * ∫ v in √(1 / (4 * √2))..1, gL (1/5) v
    at hbr5
  set J1 := ∫ v in √(1 / √2)..1, gL (1/5) v with hJ1
  set J3 := ∫ v in √(1 / (2 * √2))..1, gL (1/5) v with hJ3
  set J5 := ∫ v in √(1 / (4 * √2))..1, gL (1/5) v with hJ5
  set H₀ := hubble a t₀ with hH₀def
  -- enclosures of the three integrals at Ω = 1/5
  have hs1 : 1 < √2 := by linarith
  obtain ⟨hw1p, hw1⟩ := w_lt_one _ hs1
  obtain ⟨hw3p, hw3⟩ := w_lt_one (2 * √2) (by linarith)
  obtain ⟨hw5p, hw5⟩ := w_lt_one (4 * √2) (by linarith)
  obtain ⟨wb1u, wb1l⟩ := wb (√2) (840897 / 1000000) (13139 / 15625) hq2
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb3u, wb3l⟩ := wb (2 * √2) (148651 / 250000) (594603 / 1000000) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  obtain ⟨wb5u, wb5l⟩ := wb (4 * √2) (420449 / 1000000) (13139 / 31250) (by positivity)
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  have eJ1 : (1926847473 / 5000000000 : ℝ) ≤ J1 ∧ J1 ≤ 385504523 / 1000000000 := by
    constructor
    · have := WL1 (1/5) hΩ0 hΩ1
      have := J_shift (1/5) hΩ0 hΩ1 _ _ hw1p wb1l (by norm_num)
      norm_num at *; linarith
    · have := WU1 (1/5) le_rfl le_rfl
      have := J_shift (1/5) hΩ0 hΩ1 _ _ (by norm_num) wb1u hw1.le
      norm_num at *; linarith
  have eJ3 : (1262414489 / 1000000000 : ℝ) ≤ J3 ∧ J3 ≤ 3160225433 / 2500000000 := by
    constructor
    · have := WL3 (1/5) hΩ0 hΩ1
      have := J_shift (1/5) hΩ0 hΩ1 _ _ hw3p wb3l (by norm_num)
      norm_num at *; linarith
    · have := WU3 (1/5) le_rfl le_rfl
      have := J_shift (1/5) hΩ0 hΩ1 _ _ (by norm_num) wb3u hw3.le
      norm_num at *; linarith
  have eJ5 : (10060897683 / 5000000000 : ℝ) ≤ J5 ∧ J5 ≤ 10078611121 / 5000000000 := by
    constructor
    · have := WL5 (1/5) hΩ0 hΩ1
      have := J_shift (1/5) hΩ0 hΩ1 _ _ hw5p wb5l (by norm_num)
      norm_num at *; linarith
    · have := WU5 (1/5) le_rfl le_rfl
      have := J_shift (1/5) hΩ0 hΩ1 _ _ (by norm_num) wb5u hw5.le
      norm_num at *; linarith
  -- the cubic a₂ = 7/4, a₃ = 25/4, H = 1
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  set t := ℓ / l with ht
  obtain ⟨htl, htu⟩ := t_bounds
  have hu1 : Real.log (1 + (√2 - 1)) = 1 * ℓ / 2 := by
    rw [es1, Real.log_sqrt (by norm_num)]; ring
  have hu3 : Real.log (1 + (2 * √2 - 1)) = 3 * ℓ / 2 := by
    rw [es3, Real.log_mul (by norm_num) hq2.ne', Real.log_sqrt (by norm_num)]; ring
  have hu5 : Real.log (1 + (4 * √2 - 1)) = 5 * ℓ / 2 := by
    rw [es5, Real.log_mul (by norm_num) hq2.ne', Real.log_sqrt (by norm_num),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  set p1 := 1 / 2 + 7 / 4 * (1 / 4) * t + 25 / 4 * (1 / 8) * t ^ 2 with hp1
  set p3 := 3 / 2 + 7 / 4 * (9 / 4) * t + 25 / 4 * (27 / 8) * t ^ 2 with hp3
  set p5 := 5 / 2 + 7 / 4 * (25 / 4) * t + 25 / 4 * (125 / 8) * t ^ 2 with hp5
  have hL1 : logPolyDL3 (7/4) (25/4) 1 (redshift a t₀ t₁) = ℓ * p1 := by
    rw [hz₁, lp_eq _ _ 1 _ _ one_ne_zero hu1, hp1, ht]; field_simp; ring
  have hL3 : logPolyDL3 (7/4) (25/4) 1 (redshift a t₀ t₃) = ℓ * p3 := by
    rw [hz₃, lp_eq _ _ 1 _ _ one_ne_zero hu3, hp3, ht]; field_simp; ring
  have hL5 : logPolyDL3 (7/4) (25/4) 1 (redshift a t₀ t₅) = ℓ * p5 := by
    rw [hz₅, lp_eq _ _ 1 _ _ one_ne_zero hu5, hp5, ht]; field_simp; ring
  have ep1 := pq_bounds (1 / 2) (7 / 4 * (1 / 4)) (25 / 4 * (1 / 8)) t (by norm_num) (by norm_num)
    htl htu
  have ep3 := pq_bounds (3 / 2) (7 / 4 * (9 / 4)) (25 / 4 * (27 / 8)) t (by norm_num) (by norm_num)
    htl htu
  have ep5 := pq_bounds (5 / 2) (7 / 4 * (25 / 4)) (25 / 4 * (125 / 8)) t (by norm_num)
    (by norm_num) htl htu
  have hp1p : 0 < p1 := lt_of_lt_of_le (by norm_num) ep1.1
  have hp3p : 0 < p3 := lt_of_lt_of_le (by norm_num) ep3.1
  have hp5p : 0 < p5 := lt_of_lt_of_le (by norm_num) ep5.1
  have hJ1p : 0 < J1 := by linarith [eJ1.1]
  have hJ3p : 0 < J3 := by linarith [eJ3.1]
  have hJ5p : 0 < J5 := by linarith [eJ5.1]
  -- the three distance-to-polynomial ratios X_k
  set X1 := (√2 / H₀ * J1) / (ℓ * p1) with hX1
  set X3 := (2 * √2 / H₀ * J3) / (ℓ * p3) with hX3
  set X5 := (4 * √2 / H₀ * J5) / (ℓ * p5) with hX5
  have hX1p : 0 < X1 := by positivity
  have hX3p : 0 < X3 := by positivity
  have hX5p : 0 < X5 := by positivity
  have hY13 : X1 / X3 = (J1 * p3) / (2 * (J3 * p1)) := by
    rw [hX1, hX3]; field_simp; try ring
  have hY53 : X5 / X3 = (2 * (J5 * p3)) / (J3 * p5) := by
    rw [hX5, hX3]; field_simp; try ring
  have r13 := ratio_encl J1 J3 p3 p1 _ _ _ _ _ _ _ _ (99 / 100 * 2) (101 / 100 * 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) eJ1 eJ3 ep3 ep1 (by norm_num) (by norm_num)
    (by norm_num)
  have r53 := ratio_encl J5 J3 p3 p5 _ _ _ _ _ _ _ _ (99 / 100 / 2) (101 / 100 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) eJ5 eJ3 ep3 ep5 (by norm_num) (by norm_num)
    (by norm_num)
  have hYa : 99 / 100 ≤ X1 / X3 ∧ X1 / X3 ≤ 101 / 100 := by
    rw [hY13]; constructor
    · rw [le_div_iff₀ (by positivity)]; linarith [r13.1]
    · rw [div_le_iff₀ (by positivity)]; linarith [r13.2]
  have hYb : 99 / 100 ≤ X5 / X3 ∧ X5 / X3 ≤ 101 / 100 := by
    rw [hY53]; constructor
    · rw [le_div_iff₀ (by positivity)]; linarith [r53.1]
    · rw [div_le_iff₀ (by positivity)]; linarith [r53.2]
  have hl23 : (23 / 10 : ℝ) ≤ l := l23
  have hd1 := logb_diff X1 X3 hX1p hX3p
  have hd5 := logb_diff X5 X3 hX5p hX3p
  have hm1 := log_small _ l hYa hl23
  have hm5 := log_small _ l hYb hl23
  rw [← hd1] at hm1
  rw [← hd5] at hm5
  refine ⟨1 / 5, a, t₅, t₃, t₁, t₀, 7 / 4, 25 / 4, 1, 5 * Real.logb 10 X3, hΩ0, hΩ1, h53, h31,
    h10, hpos, hdiff, hH₀, hH, hz₁, hz₃, hz₅, one_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL1]; positivity
  · rw [hL3]; positivity
  · rw [hL5]; positivity
  · rw [hbr1, hL1]; exact hm1
  · rw [hbr3, hL3, sub_self, abs_zero]; norm_num
  · rw [hbr5, hL5]; exact hm5

end Work.Cosmography.B1FitWitness
