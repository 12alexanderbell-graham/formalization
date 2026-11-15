import Checked.Trust.NecessityL
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Hypothesis necessity, B1 family: time order and positivity of the scale factor (trust track T2b)

Run 2026-11-15T1428Z. Two kinds of hypotheses of the B1 headlines (log-polynomial luminosity-distance fits
tested against flat ΛCDM):

* **Time order** (`t ≤ t₀`, `t₇ ≤ t₃`, …) is NEEDED. Every other assumption on the scale factor is stated only
  on the closed interval from the earliest source time to the observation time; with one order reversed,
  that interval can be empty or miss a source, and the scale factor is then free where a distance is
  computed. The witness scale factor (`jb`, with the source values written in by `wa`) has a double zero half a time unit on each side of the
  observation time, so the reciprocal is not integrable across it and Lean's integral (hence the comoving
  distance, hence the luminosity distance) is zero by convention; the logarithm of zero is zero, and each
  conclusion fails. These are junk-value witnesses: they show the statement is false in Lean without the
  hypothesis, which is what `necessity%` records.
* **Positivity of the scale factor** on the interval is REDUNDANT. Where the matter density parameter is
  below one, the law makes a zero of the scale factor impossible (there Lean's division by zero makes the
  Hubble rate zero, but the law's right-hand side is positive), so the scale factor has one sign on the interval,
  and replacing `a` by `-a` changes neither the Hubble rate, the redshift nor the luminosity distance. Where the density range reaches
  one, the law allows a zero only at density one (the Einstein–de Sitter law, also the only case of the curved
  law that allows one); there the derivative, a constant over the square root of the scale factor, grows
  without bound just after the last zero, against differentiability at that zero (`no_zero_core`).
-/

namespace Checked.Trust.NCAP

open Set Filter Topology Asymptotics MeasureTheory
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1 Checked.Cosmography.B1L19
  Checked.Cosmography.BambaK Checked.Cosmography.Transverse

/-! ## The sign symmetry `a ↦ -a` -/

theorem hubble_neg (a : ℝ → ℝ) (s : ℝ) : hubble (fun x => -a x) s = hubble a s := by
  rw [hubble, hubble, show deriv (fun x => -a x) s = -deriv a s from deriv.neg, neg_div_neg_eq]

theorem redshift_neg (a : ℝ → ℝ) (t₀ s : ℝ) :
    redshift (fun x => -a x) t₀ s = redshift a t₀ s := by
  simp only [redshift, neg_div_neg_eq]

theorem comoving_neg (a : ℝ → ℝ) (t₀ t : ℝ) :
    comoving (fun x => -a x) t₀ t = -comoving a t₀ t := by
  simp only [comoving, div_neg, intervalIntegral.integral_neg]

theorem lumDistFlat_neg (a : ℝ → ℝ) (t₀ t : ℝ) :
    lumDistFlat (fun x => -a x) t₀ t = lumDistFlat a t₀ t := by
  simp only [lumDistFlat, comoving_neg, redshift_neg]; ring

/-- Under the flat law with a matter density parameter below one, the scale factor has one sign on the
interval: a zero would make the Hubble rate zero while the law's right-hand side is positive. -/
theorem sign_of_law (Ω : ℝ) (hΩ : Ω < 1) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hdiff : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s) (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    (∀ s ∈ Icc t t₀, 0 < a s) ∨ (∀ s ∈ Icc t t₀, a s < 0) := by
  have nz : ∀ s ∈ Icc t t₀, a s ≠ 0 := by
    intro s hs h0
    have e := hH s hs
    have h1 : hubble a s = 0 := by simp [hubble, h0]
    have h2 : redshift a t₀ s = -1 := by simp [redshift, h0]
    rw [h1, h2] at e
    have h3 : (0 : ℝ) < √(Ω * (1 + -1) ^ 3 + 1 - Ω) := Real.sqrt_pos.2 (by norm_num; linarith)
    nlinarith [mul_pos hH₀ h3]
  have hc : ContinuousOn a (Icc t t₀) := fun s hs => (hdiff s hs).continuousAt.continuousWithinAt
  have ht₀ : t₀ ∈ Icc t t₀ := ⟨htt, le_rfl⟩
  rcases lt_or_gt_of_ne (nz t₀ ht₀) with hneg | hpos
  · right
    intro s hs
    rcases lt_or_gt_of_ne (nz s hs) with h | h
    · exact h
    · exfalso
      have hsub : Icc s t₀ ⊆ Icc t t₀ := Icc_subset_Icc_left hs.1
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hs.2 (hc.mono hsub) ⟨hneg.le, h.le⟩
      exact nz x (hsub hx) hx0
  · left
    intro s hs
    rcases lt_or_gt_of_ne (nz s hs) with h | h
    · exfalso
      have hsub : Icc s t₀ ⊆ Icc t t₀ := Icc_subset_Icc_left hs.1
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hs.2 (hc.mono hsub) ⟨h.le, hpos.le⟩
      exact nz x (hsub hx) hx0
    · exact h

theorem law_neg (Ω : ℝ) (a : ℝ → ℝ) (t t₀ : ℝ)
    (hH : ∀ s ∈ Icc t t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    ∀ s ∈ Icc t t₀, hubble (fun x => -a x) s = hubble (fun x => -a x) t₀ *
      √(Ω * (1 + redshift (fun x => -a x) t₀ s) ^ 3 + 1 - Ω) := by
  intro s hs; simp only [hubble_neg, redshift_neg]; exact hH s hs

theorem pos_neg (a : ℝ → ℝ) (t t₀ : ℝ) (h : ∀ s ∈ Icc t t₀, a s < 0) :
    ∀ s ∈ Icc t t₀, 0 < (fun x => -a x) s := fun s hs => neg_pos.2 (h s hs)

theorem diff_neg (a : ℝ → ℝ) (t t₀ : ℝ) (h : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s) :
    ∀ s ∈ Icc t t₀, DifferentiableAt ℝ (fun x => -a x) s := fun s hs => (h s hs).neg

/-! ## The junk witness: a double zero on each side of the observation time -/

/-- Base scale factor with value one and Hubble rate two at time zero and double zeros at `±1/2`. -/
noncomputable def jb (s : ℝ) : ℝ := 16 * (s ^ 2 - 1 / 4) ^ 2 * (1 + s) ^ 2

theorem jb_zero : jb 0 = 1 := by norm_num [jb]

theorem jb_hasDerivAt : HasDerivAt jb 2 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 - 1 / 4) (2 * 0) 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).sub_const (1 / 4)
  have h2 := ((h1.pow 2).const_mul 16).mul ((hasDerivAt_id (0 : ℝ)).const_add 1 |>.pow 2)
  unfold jb
  convert h2 using 1
  · ext s; simp
  · norm_num

/-- Near a double zero `c = ±1/2` of `jb`, `1/(s − c)` is big-O of `1/jb`. -/
theorem jb_bigO (c : ℝ) (hc : c = 1 / 2 ∨ c = -1 / 2) :
    (fun s => (s - c)⁻¹) =O[𝓝[≠] c] (fun s => 1 / jb s) := by
  refine IsBigO.of_bound 20 ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 4)),
    self_mem_nhdsWithin] with s hs hne
  rw [Metric.mem_ball, Real.dist_eq] at hs
  have hd : 0 < |s - c| := abs_pos.2 (sub_ne_zero.2 hne)
  have hs' := abs_lt.1 hs
  have hjb : jb s = 16 * (s - c) ^ 2 * ((s + c) ^ 2 * (1 + s) ^ 2) := by
    rcases hc with rfl | rfl <;> (unfold jb; ring)
  have hq : 0 < (s + c) ^ 2 * (1 + s) ^ 2 := by
    have h1 : s + c ≠ 0 := by rcases hc with rfl | rfl <;> (intro h; linarith)
    have h2 : 1 + s ≠ 0 := by rcases hc with rfl | rfl <;> (intro h; linarith)
    positivity
  have hqb : (s + c) ^ 2 * (1 + s) ^ 2 ≤ 5 := by
    rcases hc with rfl | rfl
    · have a1 : (s + 1 / 2) ^ 2 ≤ (5 / 4) ^ 2 := by nlinarith
      have a2 : (1 + s) ^ 2 ≤ (7 / 4) ^ 2 := by nlinarith
      nlinarith [mul_le_mul a1 a2 (sq_nonneg _) (by norm_num)]
    · have a1 : (s + -1 / 2) ^ 2 ≤ (5 / 4) ^ 2 := by nlinarith
      have a2 : (1 + s) ^ 2 ≤ (3 / 4) ^ 2 := by nlinarith
      nlinarith [mul_le_mul a1 a2 (sq_nonneg _) (by norm_num)]
  have hjpos : 0 < jb s := by
    have := sub_ne_zero.2 hne
    rw [hjb]; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos (one_div_pos.2 hjpos), ← one_div,
    mul_one_div, div_le_div_iff₀ hd hjpos, one_mul, hjb, ← sq_abs (s - c)]
  have k1 : |s - c| * ((s + c) ^ 2 * (1 + s) ^ 2) ≤ 1 / 4 * 5 :=
    mul_le_mul hs.le hqb hq.le (by norm_num)
  nlinarith [k1, hd]

/-- A scale factor equal to `jb` near a double zero inside `[[x, y]]` has a non-integrable reciprocal. -/
theorem not_ii (a : ℝ → ℝ) (c : ℝ) (hc : c = 1 / 2 ∨ c = -1 / 2) (heq : a =ᶠ[𝓝 c] jb) {x y : ℝ}
    (hxy : x ≠ y) (hcm : c ∈ uIcc x y) : ¬IntervalIntegrable (fun s => 1 / a s) volume x y := by
  refine not_intervalIntegrable_of_sub_inv_isBigO_punctured ?_ hxy hcm
  refine (jb_bigO c hc).congr_right (fun _ => rfl) |>.trans_eventuallyEq ?_
  filter_upwards [nhdsWithin_le_nhds heq] with s hs
  rw [hs]

/-- Lean's comoving distance across such a zero is `0` (the integral of a non-integrable function). -/
theorem comoving_junk (a : ℝ → ℝ) (c : ℝ) (hc : c = 1 / 2 ∨ c = -1 / 2) (heq : a =ᶠ[𝓝 c] jb)
    {t₀ t : ℝ} (hne : t ≠ t₀) (hcm : c ∈ uIcc t t₀) : comoving a t₀ t = 0 :=
  intervalIntegral.integral_undef (not_ii a c hc heq hne hcm)

theorem lumDistFlat_junk (a : ℝ → ℝ) (c : ℝ) (hc : c = 1 / 2 ∨ c = -1 / 2) (heq : a =ᶠ[𝓝 c] jb)
    {t₀ t : ℝ} (hne : t ≠ t₀) (hcm : c ∈ uIcc t t₀) : lumDistFlat a t₀ t = 0 := by
  simp [lumDistFlat, comoving_junk a c hc heq hne hcm]

theorem upd_eq (f : ℝ → ℝ) {x y : ℝ} (v : ℝ) (h : y ≠ x) : Function.update f x v =ᶠ[𝓝 y] f := by
  filter_upwards [eventually_ne_nhds h] with s hs
  exact Function.update_of_ne hs v f

theorem hubble_of_eq (a : ℝ → ℝ) (h : a =ᶠ[𝓝 0] jb) : hubble a 0 = 2 := by
  simp only [hubble, h.deriv_eq, jb_hasDerivAt.deriv, h.eq_of_nhds, jb_zero, div_one]

theorem logb_zero_div (x : ℝ) : Real.logb 10 (0 / x) = 0 := by simp

/-! ## Positivity of the scale factor: REDUNDANT for a matter density parameter below one -/

theorem cubic_misses_z3_r4 : dropped% Checked.Cosmography.B1.cubic_misses_z3 4 := by
  intro Ω h1 h2 a t t₀ htt hdiff hH₀ hH hz
  rcases sign_of_law Ω (by linarith) a t t₀ htt hdiff hH₀ hH with hp | hn
  · exact cubic_misses_z3 Ω h1 h2 a t t₀ htt hp hdiff hH₀ hH hz
  · have h := cubic_misses_z3 Ω h1 h2 (fun x => -a x) t t₀ htt (pos_neg a t t₀ hn)
      (diff_neg a t t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t t₀ hH) (by rwa [redshift_neg])
    simpa only [hubble_neg, redshift_neg, lumDistFlat_neg] using h

theorem cubic_misses_z7_r4 : dropped% Checked.Cosmography.B1.cubic_misses_z7 4 := by
  intro Ω h1 h2 a t t₀ htt hdiff hH₀ hH hz
  rcases sign_of_law Ω (by linarith) a t t₀ htt hdiff hH₀ hH with hp | hn
  · exact cubic_misses_z7 Ω h1 h2 a t t₀ htt hp hdiff hH₀ hH hz
  · have h := cubic_misses_z7 Ω h1 h2 (fun x => -a x) t t₀ htt (pos_neg a t t₀ hn)
      (diff_neg a t t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t t₀ hH) (by rwa [redshift_neg])
    simpa only [hubble_neg, redshift_neg, lumDistFlat_neg] using h

theorem cubic_shape_miss_r5 : dropped% Checked.Cosmography.B1.cubic_shape_miss 5 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hdiff hH₀ hH hz3 hz7
  rcases sign_of_law Ω (by linarith) a t₇ t₀ (h73.trans h30) hdiff hH₀ hH with hp | hn
  · exact cubic_shape_miss Ω h1 h2 a t₇ t₃ t₀ h73 h30 hp hdiff hH₀ hH hz3 hz7
  · have h := cubic_shape_miss Ω h1 h2 (fun x => -a x) t₇ t₃ t₀ h73 h30 (pos_neg a t₇ t₀ hn)
      (diff_neg a t₇ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₇ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg])
    simpa only [hubble_neg, redshift_neg, lumDistFlat_neg] using h

theorem cubic_separation_r5 : dropped% Checked.Cosmography.B1Sep.cubic_separation 5 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hdiff hH₀ hH hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7
  rcases sign_of_law Ω (by linarith) a t₇ t₀ (h73.trans h30) hdiff hH₀ hH with hp | hn
  · exact Checked.Cosmography.B1Sep.cubic_separation Ω h1 h2 a t₇ t₃ t₀ h73 h30 hp hdiff hH₀ hH
      hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7
  · exact Checked.Cosmography.B1Sep.cubic_separation Ω h1 h2 (fun x => -a x) t₇ t₃ t₀ h73 h30
      (pos_neg a t₇ t₀ hn) (diff_neg a t₇ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₇ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) a₂ a₃ H c hHp (by rwa [redshift_neg])
      (by rwa [redshift_neg]) (by rwa [redshift_neg, lumDistFlat_neg])
      (by rwa [redshift_neg, lumDistFlat_neg])

theorem cubic_direction_r5 : dropped% Checked.Cosmography.B1Sep.cubic_direction 5 := by
  intro Ω h1 h2 a t₇ t₃ t₀ h73 h30 hdiff hH₀ hH hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7
  rcases sign_of_law Ω (by linarith) a t₇ t₀ (h73.trans h30) hdiff hH₀ hH with hp | hn
  · exact Checked.Cosmography.B1Sep.cubic_direction Ω h1 h2 a t₇ t₃ t₀ h73 h30 hp hdiff hH₀ hH
      hz3 hz7 a₂ a₃ H c hHp hp3 hp7 hm3 hm7
  · exact Checked.Cosmography.B1Sep.cubic_direction Ω h1 h2 (fun x => -a x) t₇ t₃ t₀ h73 h30
      (pos_neg a t₇ t₀ hn) (diff_neg a t₇ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₇ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) a₂ a₃ H c hHp (by rwa [redshift_neg])
      (by rwa [redshift_neg]) (by rwa [redshift_neg, lumDistFlat_neg])
      (by rwa [redshift_neg, lumDistFlat_neg])

/-! ## The witness scale factors: `jb` with prescribed values at the source times -/

/-- `jb` with the value `v` written at time `t` for each pair `(t, v)` of the list. -/
noncomputable def wa : List (ℝ × ℝ) → ℝ → ℝ
  | [] => jb
  | p :: l => Function.update (wa l) p.1 p.2

theorem wa_eq (l : List (ℝ × ℝ)) (c : ℝ) (h : ∀ p ∈ l, p.1 ≠ c) : wa l =ᶠ[𝓝 c] jb := by
  induction l with
  | nil => exact EventuallyEq.rfl
  | cons p l ih =>
    exact (upd_eq (wa l) p.2 (h p (List.mem_cons_self ..)).symm).trans
      (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem wa_zero (l : List (ℝ × ℝ)) (h : ∀ p ∈ l, p.1 ≠ 0) : wa l 0 = 1 := by
  rw [(wa_eq l 0 h).eq_of_nhds, jb_zero]

theorem wa_hubble (l : List (ℝ × ℝ)) (h : ∀ p ∈ l, p.1 ≠ 0) : hubble (wa l) 0 = 2 :=
  hubble_of_eq _ (wa_eq l 0 h)

theorem wa_redshift (l : List (ℝ × ℝ)) (h : ∀ p ∈ l, p.1 ≠ 0) (t z : ℝ)
    (ht : wa l t = 1 / (1 + z)) : redshift (wa l) 0 t = z := by
  rw [redshift, wa_zero l h, ht, one_div_one_div]; ring

/-- A source after the observation time, across the zero at `1/2`. -/
theorem wa_ld_pos (l : List (ℝ × ℝ)) (h : ∀ p ∈ l, p.1 ≠ 1 / 2) {t : ℝ} (ht : 1 / 2 ≤ t) :
    lumDistFlat (wa l) 0 t = 0 :=
  lumDistFlat_junk _ _ (Or.inl rfl) (wa_eq l _ h) (by linarith)
    (by rw [uIcc_of_ge (by linarith)]; exact ⟨by norm_num, ht⟩)

/-- A source before the observation time, across the zero at `-1/2`. -/
theorem wa_ld_neg (l : List (ℝ × ℝ)) (h : ∀ p ∈ l, p.1 ≠ -1 / 2) {t : ℝ} (ht : t ≤ -1 / 2) :
    lumDistFlat (wa l) 0 t = 0 :=
  lumDistFlat_junk _ _ (Or.inr rfl) (wa_eq l _ h) (by linarith)
    (by rw [uIcc_of_le (by linarith)]; exact ⟨ht, by norm_num⟩)

theorem wa_cm_pos (l : List (ℝ × ℝ)) (h : ∀ p ∈ l, p.1 ≠ 1 / 2) {t : ℝ} (ht : 1 / 2 ≤ t) :
    comoving (wa l) 0 t = 0 :=
  comoving_junk _ _ (Or.inl rfl) (wa_eq l _ h) (by linarith)
    (by rw [uIcc_of_ge (by linarith)]; exact ⟨by norm_num, ht⟩)

theorem wa_cm_neg (l : List (ℝ × ℝ)) (h : ∀ p ∈ l, p.1 ≠ -1 / 2) {t : ℝ} (ht : t ≤ -1 / 2) :
    comoving (wa l) 0 t = 0 :=
  comoving_junk _ _ (Or.inr rfl) (wa_eq l _ h) (by linarith)
    (by rw [uIcc_of_le (by linarith)]; exact ⟨ht, by norm_num⟩)

/-- Every statement about times in an empty interval holds. -/
theorem vac {P : ℝ → Prop} {x y : ℝ} (h : y < x) : ∀ s ∈ Icc x y, P s :=
  fun _ hs => absurd (hs.1.trans hs.2) (not_le.2 h)

theorem logPoly3_pos (a₂ a₃ H z : ℝ) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃) (hH : 0 < H) (hz : 0 < z) :
    0 < logPolyDL3 a₂ a₃ H z := by
  have hL : 0 < Real.logb 10 (1 + z) := Real.logb_pos (by norm_num) (by linarith)
  unfold logPolyDL3
  exact mul_pos (div_pos (Real.log_pos (by norm_num)) hH) (by positivity)

theorem lusA2_pos : 0 ≤ lusA2 (1 / 5) := by
  unfold lusA2; exact mul_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)

theorem lusA3_pos : 0 ≤ lusA3 (1 / 5) := by
  unfold lusA3; exact mul_nonneg (pow_nonneg (Real.log_nonneg (by norm_num)) 2) (by norm_num)

theorem sqrt2_gt : 1 < √2 := by
  rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-! ## Time order: NEEDED (junk comoving distance across a double zero of the scale factor) -/

/-- Without `t ≤ t₀`: the source after the observation time; the bridge's left side is Lean's zero
distance, its right side is positive. -/
theorem lumDistFlat_flatLCDM_h3 : necessity% Checked.Cosmography.B1.lumDistFlat_flatLCDM 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 3))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by simp [l]
  have hv : wa l 1 = 1 / (1 + 3) := by simp [l, wa]
  refine ⟨1, zero_le_one, le_rfl, wa l, 1, 0, vac (by norm_num), vac (by norm_num),
    by rw [wa_hubble l h0]; norm_num, vac (by norm_num), ?_⟩
  rw [wa_ld_pos l (by simp [l]) (by norm_num), wa_redshift l h0 1 3 hv, wa_hubble l h0, wa_zero l h0, hv]
  have e : √((1 : ℝ) / (1 + 3) / 1) = 1 / 2 := by
    rw [show (1 : ℝ) / (1 + 3) / 1 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e]
  simp
  norm_num

theorem cubic_misses_z3_h3 : necessity% Checked.Cosmography.B1.cubic_misses_z3 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 3))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by simp [l]
  refine ⟨1 / 5, le_rfl, by norm_num, wa l, 1, 0, vac (by norm_num), vac (by norm_num),
    by rw [wa_hubble l h0]; norm_num, vac (by norm_num), wa_redshift l h0 1 3 (by simp [l, wa]), ?_⟩
  rintro ⟨-, h⟩
  rw [wa_ld_pos l (by simp [l]) (by norm_num), logb_zero_div] at h
  norm_num at h

theorem cubic_misses_z7_h3 : necessity% Checked.Cosmography.B1.cubic_misses_z7 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 7))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by simp [l]
  refine ⟨1 / 5, le_rfl, by norm_num, wa l, 1, 0, vac (by norm_num), vac (by norm_num),
    by rw [wa_hubble l h0]; norm_num, vac (by norm_num), wa_redshift l h0 1 7 (by simp [l, wa]), ?_⟩
  rintro ⟨-, h⟩
  rw [wa_ld_pos l (by simp [l]) (by norm_num), logb_zero_div] at h
  norm_num at h

theorem cubic_shape_miss_h3 : necessity% Checked.Cosmography.B1.cubic_shape_miss 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 7)), (-1, 1 / (1 + 3))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by simp [l]
  refine ⟨1 / 5, le_rfl, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    wa_redshift l h0 (-1) 3 (by norm_num [l, wa, Function.update_apply]),
    wa_redshift l h0 1 7 (by norm_num [l, wa, Function.update_apply]), ?_⟩
  rw [wa_ld_pos l (by norm_num [l]) (by norm_num), wa_ld_neg l (by norm_num [l]) (by norm_num),
    logb_zero_div, logb_zero_div]
  norm_num

theorem cubic_shape_miss_h4 : necessity% Checked.Cosmography.B1.cubic_shape_miss 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 7)), (2, 1 / (1 + 3))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by simp [l]
  refine ⟨1 / 5, le_rfl, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    wa_redshift l h0 2 3 (by norm_num [l, wa, Function.update_apply]),
    wa_redshift l h0 1 7 (by norm_num [l, wa, Function.update_apply]), ?_⟩
  rw [wa_ld_pos l (by norm_num [l]) (by norm_num), wa_ld_pos l (by norm_num [l]) (by norm_num),
    logb_zero_div, logb_zero_div]
  norm_num

theorem logPoly4_pos (a₂ a₃ a₄ H z : ℝ) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃ + a₄) (h₄ : a₄ ≤ 0) (hH : 0 < H)
    (hz : 0 < z ∧ 1 + z ≤ 10) : 0 < logPolyDL4 a₂ a₃ a₄ H z := by
  have hL : 0 < Real.logb 10 (1 + z) := Real.logb_pos (by norm_num) (by linarith)
  have hL1 : Real.logb 10 (1 + z) ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)]; simpa using hz.2
  unfold logPolyDL4
  refine mul_pos (div_pos (Real.log_pos (by norm_num)) hH) ?_
  set L := Real.logb 10 (1 + z)
  have k : a₄ * L ^ 4 ≥ a₄ * L ^ 3 := by
    have : L ^ 4 ≤ L ^ 3 := by
      rw [show L ^ 4 = L ^ 3 * L by ring]; exact mul_le_of_le_one_right (by positivity) hL1
    nlinarith
  nlinarith [mul_nonneg h₃ (pow_pos hL 3).le, mul_nonneg h₂ (sq_nonneg L)]

theorem four_sqrt2_z : 0 < 4 * √2 - 1 ∧ 1 + (4 * √2 - 1) ≤ 10 := by
  have q := sqrt2_gt
  have q2 : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor <;> linarith

theorem cubic_separation_h3 : necessity% Checked.Cosmography.B1Sep.cubic_separation 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 7)), (-1, 1 / (1 + 3))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (-1) 3 (by norm_num [l, wa, Function.update_apply])
  have z7 := wa_redshift l h0 1 7 (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d7 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, le_rfl, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z7,
    lusA2 (1 / 5), lusA3 (1 / 5), 1, 0, one_pos,
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by norm_num),
    by rw [z7]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by norm_num),
    by rw [d3, logb_zero_div]; norm_num, by rw [d7, logb_zero_div]; norm_num, ?_⟩
  norm_num

theorem cubic_separation_h4 : necessity% Checked.Cosmography.B1Sep.cubic_separation 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 7)), (2, 1 / (1 + 3))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (2) 3 (by norm_num [l, wa, Function.update_apply])
  have z7 := wa_redshift l h0 1 7 (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d7 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, le_rfl, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z7,
    lusA2 (1 / 5), lusA3 (1 / 5), 1, 0, one_pos,
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by norm_num),
    by rw [z7]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by norm_num),
    by rw [d3, logb_zero_div]; norm_num, by rw [d7, logb_zero_div]; norm_num, ?_⟩
  norm_num

theorem cubic_direction_h3 : necessity% Checked.Cosmography.B1Sep.cubic_direction 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 7)), (-1, 1 / (1 + 3))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (-1) 3 (by norm_num [l, wa, Function.update_apply])
  have z7 := wa_redshift l h0 1 7 (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d7 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, le_rfl, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z7,
    lusA2 (1 / 5), lusA3 (1 / 5), 1, 0, one_pos,
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by norm_num),
    by rw [z7]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by norm_num),
    by rw [d3, logb_zero_div]; norm_num, by rw [d7, logb_zero_div]; norm_num, ?_⟩
  simp

theorem cubic_direction_h4 : necessity% Checked.Cosmography.B1Sep.cubic_direction 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + 7)), (2, 1 / (1 + 3))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (2) 3 (by norm_num [l, wa, Function.update_apply])
  have z7 := wa_redshift l h0 1 7 (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d7 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, le_rfl, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z7,
    lusA2 (1 / 5), lusA3 (1 / 5), 1, 0, one_pos,
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by norm_num),
    by rw [z7]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by norm_num),
    by rw [d3, logb_zero_div]; norm_num, by rw [d7, logb_zero_div]; norm_num, ?_⟩
  simp

theorem l19_sq_central_h3 : necessity% Checked.Cosmography.B1L19.l19_sq_central 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-1, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (-1) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z5, 1, one_pos, ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sq_central_h4 : necessity% Checked.Cosmography.B1L19.l19_sq_central 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z5, 1, one_pos, ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sqg_central_h3 : necessity% Checked.Cosmography.B1L19.l19_sqg_central 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-1, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (-1) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z5, 1, one_pos, ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sqg_central_h4 : necessity% Checked.Cosmography.B1L19.l19_sqg_central 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z5, 1, one_pos, ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sq_box_h3 : necessity% Checked.Cosmography.B1L19.l19_sq_box 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-1, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (-1) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z5,
    2.906, 5.479, (-1.794), 1, one_pos, le_rfl, le_rfl, le_rfl,
    (by rw [z5]; exact logPoly4_pos 2.906 5.479 (-1.794) 1 _ (by norm_num) (by norm_num) (by norm_num) one_pos four_sqrt2_z), ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sq_box_h4 : necessity% Checked.Cosmography.B1L19.l19_sq_box 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z5,
    2.906, 5.479, (-1.794), 1, one_pos, le_rfl, le_rfl, le_rfl,
    (by rw [z5]; exact logPoly4_pos 2.906 5.479 (-1.794) 1 _ (by norm_num) (by norm_num) (by norm_num) one_pos four_sqrt2_z), ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sqg_box_h3 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-1, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (-1) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z5,
    3.043, 4.480, (-0.915), 1, one_pos, le_rfl, le_rfl, le_rfl,
    (by rw [z5]; exact logPoly4_pos 3.043 4.480 (-0.915) 1 _ (by norm_num) (by norm_num) (by norm_num) one_pos four_sqrt2_z), ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sqg_box_h4 : necessity% Checked.Cosmography.B1L19.l19_sqg_box 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num), z3, z5,
    3.043, 4.480, (-0.915), 1, one_pos, le_rfl, le_rfl, le_rfl,
    (by rw [z5]; exact logPoly4_pos 3.043 4.480 (-0.915) 1 _ (by norm_num) (by norm_num) (by norm_num) one_pos four_sqrt2_z), ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sq_curved_h3 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-1, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (-1) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have c3 : comoving (wa l) 0 (-1) = 0 := wa_cm_neg l (by norm_num [l]) (by norm_num)
  have d3 : lumDist 0 (wa l) 0 (-1) = 0 := by simp [lumDist, c3, transverse]
  have c5 : comoving (wa l) 0 1 = 0 := wa_cm_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDist 0 (wa l) 0 1 = 0 := by simp [lumDist, c5, transverse]
  have hk : omega0 0 (wa l) 0 = 1 := by simp [omega0]
  refine ⟨1 / 5, 0, by norm_num, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, by rw [hk], by rw [hk]; norm_num,
    vac (by norm_num), z3, z5, 1, one_pos, ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sq_curved_h4 : necessity% Checked.Cosmography.B1L19Curved.l19_sq_curved 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have c3 : comoving (wa l) 0 (2) = 0 := wa_cm_pos l (by norm_num [l]) (by norm_num)
  have d3 : lumDist 0 (wa l) 0 (2) = 0 := by simp [lumDist, c3, transverse]
  have c5 : comoving (wa l) 0 1 = 0 := wa_cm_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDist 0 (wa l) 0 1 = 0 := by simp [lumDist, c5, transverse]
  have hk : omega0 0 (wa l) 0 = 1 := by simp [omega0]
  refine ⟨1 / 5, 0, by norm_num, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, by rw [hk], by rw [hk]; norm_num,
    vac (by norm_num), z3, z5, 1, one_pos, ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sqg_curved_h3 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-1, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (-1) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have c3 : comoving (wa l) 0 (-1) = 0 := wa_cm_neg l (by norm_num [l]) (by norm_num)
  have d3 : lumDist 0 (wa l) 0 (-1) = 0 := by simp [lumDist, c3, transverse]
  have c5 : comoving (wa l) 0 1 = 0 := wa_cm_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDist 0 (wa l) 0 1 = 0 := by simp [lumDist, c5, transverse]
  have hk : omega0 0 (wa l) 0 = 1 := by simp [omega0]
  refine ⟨1 / 5, 0, by norm_num, by norm_num, wa l, 1, -1, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, by rw [hk], by rw [hk]; norm_num,
    vac (by norm_num), z3, z5, 1, one_pos, ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem l19_sqg_curved_h4 : necessity% Checked.Cosmography.B1L19Curved.l19_sqg_curved 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have c3 : comoving (wa l) 0 (2) = 0 := wa_cm_pos l (by norm_num [l]) (by norm_num)
  have d3 : lumDist 0 (wa l) 0 (2) = 0 := by simp [lumDist, c3, transverse]
  have c5 : comoving (wa l) 0 1 = 0 := wa_cm_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDist 0 (wa l) 0 1 = 0 := by simp [lumDist, c5, transverse]
  have hk : omega0 0 (wa l) 0 = 1 := by simp [omega0]
  refine ⟨1 / 5, 0, by norm_num, by norm_num, wa l, 1, 2, 0, by norm_num, vac (by norm_num),
    vac (by norm_num), by rw [wa_hubble l h0]; norm_num, by rw [hk], by rw [hk]; norm_num,
    vac (by norm_num), z3, z5, 1, one_pos, ?_⟩
  rw [d3, d5, logb_zero_div, logb_zero_div]
  norm_num

theorem fit_direction_h3 : necessity% Checked.Cosmography.B1Fit.fit_direction 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-2, 1 / (1 + (2 * √2 - 1))),
    (-1, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (-1) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (-2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (-2) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, -2, -1, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, lusA2 (1 / 5), lusA3 (1 / 5), 1, 0, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num, ?_⟩
  simp

theorem fit_direction_h4 : necessity% Checked.Cosmography.B1Fit.fit_direction 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1))),
    (-1, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (-1) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, -1, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, lusA2 (1 / 5), lusA3 (1 / 5), 1, 0, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num, ?_⟩
  simp

theorem fit_direction_h5 : necessity% Checked.Cosmography.B1Fit.fit_direction 5 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1))),
    (3, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (3) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (3) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, 3, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, lusA2 (1 / 5), lusA3 (1 / 5), 1, 0, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ lusA2_pos lusA3_pos one_pos (by linarith),
    by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num, ?_⟩
  simp

theorem rl19_box_unmatched_h3 : necessity% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 3 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (-2, 1 / (1 + (2 * √2 - 1))),
    (-1, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (-1) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (-2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (-2) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, -2, -1, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, 343 / 100, 157 / 100, 1, 0, le_rfl, by norm_num, le_rfl, by norm_num, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    ?_⟩
  exact ⟨by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num⟩

theorem rl19_box_unmatched_h4 : necessity% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 4 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1))),
    (-1, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (-1) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (-1) = 0 := wa_ld_neg l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, -1, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, 343 / 100, 157 / 100, 1, 0, le_rfl, by norm_num, le_rfl, by norm_num, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    ?_⟩
  exact ⟨by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num⟩

theorem rl19_box_unmatched_h5 : necessity% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 5 := by
  set l : List (ℝ × ℝ) := [(1, 1 / (1 + (4 * √2 - 1))), (2, 1 / (1 + (2 * √2 - 1))),
    (3, 1 / (1 + (√2 - 1)))]
  have h0 : ∀ p ∈ l, p.1 ≠ 0 := by norm_num [l]
  have z1 := wa_redshift l h0 (3) (√2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z3 := wa_redshift l h0 (2) (2 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have z5 := wa_redshift l h0 1 (4 * √2 - 1) (by norm_num [l, wa, Function.update_apply])
  have d1 : lumDistFlat (wa l) 0 (3) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d3 : lumDistFlat (wa l) 0 (2) = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have d5 : lumDistFlat (wa l) 0 1 = 0 := wa_ld_pos l (by norm_num [l]) (by norm_num)
  have q := sqrt2_gt
  refine ⟨1 / 5, by norm_num, by norm_num, wa l, 1, 2, 3, 0, by norm_num, by norm_num,
    vac (by norm_num), vac (by norm_num), by rw [wa_hubble l h0]; norm_num, vac (by norm_num),
    z1, z3, z5, 343 / 100, 157 / 100, 1, 0, le_rfl, by norm_num, le_rfl, by norm_num, one_pos,
    by rw [z1]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    by rw [z3]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    by rw [z5]; exact logPoly3_pos _ _ _ _ (by norm_num) (by norm_num) one_pos (by linarith),
    ?_⟩
  exact ⟨by rw [d1, logb_zero_div]; norm_num, by rw [d3, logb_zero_div]; norm_num,
    by rw [d5, logb_zero_div]; norm_num⟩

/-! ## Positivity of the scale factor when the density range reaches one -/

/-- A scale factor positive at the observation time, differentiable on the interval, with
`deriv a · √a ≥ c > 0` wherever it is positive, has no zero on the interval: just after its last zero the
derivative would grow without bound (`deriv a = c/√a`), against differentiability at that zero. -/
theorem no_zero_core (a : ℝ → ℝ) (t t₀ c : ℝ) (hc : 0 < c)
    (hdiff : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s) (ha₀ : 0 < a t₀)
    (hd : ∀ s ∈ Icc t t₀, 0 < a s → c ≤ deriv a s * √(a s)) : ∀ s ∈ Icc t t₀, 0 < a s := by
  have hcont : ContinuousOn a (Icc t t₀) := fun s hs => (hdiff s hs).continuousAt.continuousWithinAt
  by_contra hneg
  push Not at hneg
  obtain ⟨s, hs, hs0⟩ := hneg
  -- the set of zeros in [s, t₀]
  set Z := {x ∈ Icc s t₀ | a x = 0} with hZ
  have hsub : Icc s t₀ ⊆ Icc t t₀ := Icc_subset_Icc_left hs.1
  have hZne : Z.Nonempty := by
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hs.2 (hcont.mono hsub) ⟨hs0, ha₀.le⟩
    exact ⟨x, hx, hx0⟩
  have hZc : IsClosed Z := (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc
    isClosed_singleton
  have hZb : BddAbove Z := ⟨t₀, fun x hx => hx.1.2⟩
  have hZcpt : IsCompact Z := Metric.isCompact_of_isClosed_isBounded hZc
    (Metric.isBounded_Icc s t₀ |>.subset (fun x hx => hx.1))
  set s₁ := sSup Z with hs₁
  have hs₁Z : s₁ ∈ Z := hZcpt.sSup_mem hZne
  have hs₁0 : a s₁ = 0 := hs₁Z.2
  have hs₁t : s₁ ∈ Icc t t₀ := hsub hs₁Z.1
  have hlt : s₁ < t₀ := lt_of_le_of_ne hs₁Z.1.2 (fun h => by rw [h] at hs₁0; linarith)
  -- positivity after s₁
  have hposR : ∀ x ∈ Ioc s₁ t₀, 0 < a x := by
    intro x hx
    by_contra hx0
    push Not at hx0
    have hsx : Icc x t₀ ⊆ Icc t t₀ := Icc_subset_Icc_left (le_trans hs₁t.1 hx.1.le)
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hx.2 (hcont.mono hsx) ⟨hx0, ha₀.le⟩
    have hyZ : y ∈ Z := ⟨⟨le_trans hs₁Z.1.1 (hx.1.le.trans hy.1), hy.2⟩, hy0⟩
    have := le_csSup hZb hyZ
    linarith [hx.1, hy.1]
  -- the derivative estimate at s₁
  obtain ⟨D, hD⟩ : ∃ D, HasDerivAt a D s₁ := ⟨_, (hdiff s₁ hs₁t).hasDerivAt⟩
  have hlo := hD.isLittleO
  have hev := hlo.def (by norm_num : (0 : ℝ) < 1)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set M := max (D + 1) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hup : ∀ x, s₁ < x → x < s₁ + δ → a x ≤ M * (x - s₁) := by
    intro x h1 h2
    have hx := hball (show dist x s₁ < δ by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    rw [hs₁0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_of_pos (by linarith : 0 < x - s₁)] at hx
    have := (abs_le.1 hx).2
    have : D + 1 ≤ M := le_max_left _ _
    nlinarith
  -- pick y small
  set y := min (δ / 2) (min ((t₀ - s₁) / 2) (c ^ 2 / (2 * M ^ 3))) with hy
  have hy0 : 0 < y := lt_min (by linarith) (lt_min (by linarith) (by positivity))
  have hyδ : y < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hyt : s₁ + y ≤ t₀ := by
    have : y ≤ (t₀ - s₁) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hyc : y < c ^ 2 / M ^ 3 := by
    have h1 : y ≤ c ^ 2 / (2 * M ^ 3) := le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : c ^ 2 / (2 * M ^ 3) < c ^ 2 / M ^ 3 :=
      div_lt_div_of_pos_left (by positivity) (by positivity) (by nlinarith [pow_pos (by linarith : (0:ℝ) < M) 3])
    linarith
  -- mean value theorem on [s₁, s₁ + y]
  set x := s₁ + y
  have hxt : Icc s₁ x ⊆ Icc t t₀ := fun z hz => ⟨le_trans hs₁t.1 hz.1, le_trans hz.2 hyt⟩
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope a (deriv a) (by linarith : s₁ < x)
    (hcont.mono hxt) (fun z hz => (hdiff z (hxt (Ioo_subset_Icc_self hz))).hasDerivAt)
  have hξpos : 0 < a ξ := hposR ξ ⟨hξ.1, le_trans hξ.2.le hyt⟩
  have hxpos : 0 < a x := hposR x ⟨by linarith, hyt⟩
  have hξup : a ξ ≤ M * (ξ - s₁) := hup ξ hξ.1 (by linarith [hξ.2])
  have hxup : a x ≤ M * (x - s₁) := hup x (by linarith) (by linarith)
  have hdξ := hd ξ (hxt (Ioo_subset_Icc_self hξ)) hξpos
  rw [hξd, hs₁0, sub_zero] at hdξ
  have hxs : x - s₁ = y := by ring
  rw [hxs] at hdξ hxup
  -- c ≤ (a x / y) √(a ξ) ≤ M √(a ξ), so c² ≤ M² a ξ ≤ M³ y
  have hsq : √(a ξ) ^ 2 = a ξ := Real.sq_sqrt hξpos.le
  have hsn : 0 ≤ √(a ξ) := Real.sqrt_nonneg _
  have h1 : a x / y ≤ M := by rw [div_le_iff₀ hy0]; linarith
  have h2 : c ≤ M * √(a ξ) := le_trans hdξ (mul_le_mul_of_nonneg_right h1 hsn)
  have h3 : c ^ 2 ≤ M ^ 2 * a ξ := by nlinarith
  have h4 : a ξ ≤ M * y := le_trans hξup (by nlinarith [hξ.2])
  have h5 : c ^ 2 ≤ M ^ 3 * y := by nlinarith
  have h6 : M ^ 3 * y < c ^ 2 := by
    rw [lt_div_iff₀ (by positivity)] at hyc; linarith
  linarith


theorem sign_of_nz (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hdiff : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s) (nz : ∀ s ∈ Icc t t₀, a s ≠ 0) :
    (∀ s ∈ Icc t t₀, 0 < a s) ∨ (∀ s ∈ Icc t t₀, a s < 0) := by
  have hc : ContinuousOn a (Icc t t₀) := fun s hs => (hdiff s hs).continuousAt.continuousWithinAt
  have ht₀ : t₀ ∈ Icc t t₀ := ⟨htt, le_rfl⟩
  rcases lt_or_gt_of_ne (nz t₀ ht₀) with hneg | hpos
  · right
    intro s hs
    rcases lt_or_gt_of_ne (nz s hs) with h | h
    · exact h
    · exfalso
      have hsub : Icc s t₀ ⊆ Icc t t₀ := Icc_subset_Icc_left hs.1
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hs.2 (hc.mono hsub) ⟨hneg.le, h.le⟩
      exact nz x (hsub hx) hx0
  · left
    intro s hs
    rcases lt_or_gt_of_ne (nz s hs) with h | h
    · exfalso
      have hsub : Icc s t₀ ⊆ Icc t t₀ := Icc_subset_Icc_left hs.1
      obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hs.2 (hc.mono hsub) ⟨h.le, hpos.le⟩
      exact nz x (hsub hx) hx0
    · exact h

/-- Einstein–de Sitter law (density parameter one): `deriv a · √a = H₀ √(a₀³)` where `a > 0`. -/
theorem eds_deriv (a : ℝ → ℝ) (t t₀ : ℝ) (ha₀ : 0 < a t₀)
    (hH : ∀ s ∈ Icc t t₀, hubble a s = hubble a t₀ * √((1 + redshift a t₀ s) ^ 3)) :
    ∀ s ∈ Icc t t₀, 0 < a s → hubble a t₀ * √(a t₀ ^ 3) ≤ deriv a s * √(a s) := by
  intro s hs has
  have e := hH s hs
  simp only [hubble, redshift] at e
  rw [show 1 + (a t₀ / a s - 1) = a t₀ / a s by ring, div_pow, Real.sqrt_div' _ (by positivity)] at e
  have h3 : √(a s ^ 3) = a s * √(a s) := by
    rw [show a s ^ 3 = a s ^ 2 * a s by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq has.le]
  rw [h3] at e
  have hsq : 0 < √(a s) := Real.sqrt_pos.2 has
  rw [div_eq_iff has.ne'] at e
  rw [e]
  apply le_of_eq
  simp only [hubble]
  field_simp

theorem hubble_ne (a : ℝ → ℝ) (t₀ : ℝ) (hH₀ : 0 < hubble a t₀) : a t₀ ≠ 0 := by
  intro h; simp [hubble, h] at hH₀

/-- Under the Einstein–de Sitter law the scale factor has one sign on the interval. -/
theorem sign_eds (a : ℝ → ℝ) (t t₀ : ℝ)
    (hdiff : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s) (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t t₀, hubble a s = hubble a t₀ * √((1 + redshift a t₀ s) ^ 3)) :
    (∀ s ∈ Icc t t₀, 0 < a s) ∨ (∀ s ∈ Icc t t₀, a s < 0) := by
  rcases lt_or_gt_of_ne (hubble_ne a t₀ hH₀) with hn | hp
  · right
    have hH' : ∀ s ∈ Icc t t₀, hubble (fun x => -a x) s = hubble (fun x => -a x) t₀ *
        √((1 + redshift (fun x => -a x) t₀ s) ^ 3) := by
      intro s hs; simp only [hubble_neg, redshift_neg]; exact hH s hs
    have k := no_zero_core (fun x => -a x) t t₀ _ (by rw [hubble_neg]; exact mul_pos hH₀ (Real.sqrt_pos.2 (pow_pos (neg_pos.2 hn) 3)))
      (diff_neg a t t₀ hdiff) (neg_pos.2 hn) (eds_deriv _ t t₀ (neg_pos.2 hn) hH')
    exact fun s hs => neg_pos.1 (k s hs)
  · left
    exact no_zero_core a t t₀ _ (mul_pos hH₀ (Real.sqrt_pos.2 (pow_pos hp 3))) hdiff hp (eds_deriv a t t₀ hp hH)

/-- Flat law with `0 ≤ Ω ≤ 1`: the scale factor has one sign on the interval. -/
theorem sign_flat (Ω : ℝ) (hΩ : Ω ≤ 1) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hdiff : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s) (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Icc t t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)) :
    (∀ s ∈ Icc t t₀, 0 < a s) ∨ (∀ s ∈ Icc t t₀, a s < 0) := by
  rcases lt_or_eq_of_le hΩ with hlt | rfl
  · exact sign_of_law Ω hlt a t t₀ htt hdiff hH₀ hH
  · exact sign_eds a t t₀ hdiff hH₀ fun s hs => by rw [hH s hs]; ring_nf

theorem lumDistFlat_flatLCDM_r4 : dropped% Checked.Cosmography.B1.lumDistFlat_flatLCDM 4 := by
  intro Ω h0 h1 a t t₀ htt hdiff hH₀ hH
  rcases sign_flat Ω h1 a t t₀ htt hdiff hH₀ hH with hp | hn
  · exact lumDistFlat_flatLCDM Ω h0 h1 a t t₀ htt hp hdiff hH₀ hH
  · have h := lumDistFlat_flatLCDM Ω h0 h1 (fun x => -a x) t t₀ htt (pos_neg a t t₀ hn)
      (diff_neg a t t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t t₀ hH)
    simpa only [hubble_neg, redshift_neg, lumDistFlat_neg, neg_div_neg_eq] using h

theorem l19_sq_central_r5 : dropped% Checked.Cosmography.B1L19.l19_sq_central 5 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hdiff hH₀ hH hz3 hz5 H hHp
  rcases sign_flat Ω h1 a t₅ t₀ (h53.trans h30) hdiff hH₀ hH with hp | hn
  · exact l19_sq_central Ω h0 h1 a t₅ t₃ t₀ h53 h30 hp hdiff hH₀ hH hz3 hz5 H hHp
  · have h := l19_sq_central Ω h0 h1 (fun x => -a x) t₅ t₃ t₀ h53 h30 (pos_neg a t₅ t₀ hn)
      (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₅ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) H hHp
    simpa only [hubble_neg, redshift_neg, lumDistFlat_neg] using h

theorem l19_sqg_central_r5 : dropped% Checked.Cosmography.B1L19.l19_sqg_central 5 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hdiff hH₀ hH hz3 hz5 H hHp
  rcases sign_flat Ω h1 a t₅ t₀ (h53.trans h30) hdiff hH₀ hH with hp | hn
  · exact l19_sqg_central Ω h0 h1 a t₅ t₃ t₀ h53 h30 hp hdiff hH₀ hH hz3 hz5 H hHp
  · have h := l19_sqg_central Ω h0 h1 (fun x => -a x) t₅ t₃ t₀ h53 h30 (pos_neg a t₅ t₀ hn)
      (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₅ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) H hHp
    simpa only [hubble_neg, redshift_neg, lumDistFlat_neg] using h

theorem l19_sq_box_r5 : dropped% Checked.Cosmography.B1L19.l19_sq_box 5 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hdiff hH₀ hH hz3 hz5 a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄ hp5
  rcases sign_flat Ω h1 a t₅ t₀ (h53.trans h30) hdiff hH₀ hH with hp | hn
  · exact l19_sq_box Ω h0 h1 a t₅ t₃ t₀ h53 h30 hp hdiff hH₀ hH hz3 hz5 a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄ hp5
  · have h := l19_sq_box Ω h0 h1 (fun x => -a x) t₅ t₃ t₀ h53 h30 (pos_neg a t₅ t₀ hn)
      (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₅ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄
      (by rwa [redshift_neg])
    simpa only [hubble_neg, redshift_neg, lumDistFlat_neg] using h

theorem l19_sqg_box_r5 : dropped% Checked.Cosmography.B1L19.l19_sqg_box 5 := by
  intro Ω h0 h1 a t₅ t₃ t₀ h53 h30 hdiff hH₀ hH hz3 hz5 a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄ hp5
  rcases sign_flat Ω h1 a t₅ t₀ (h53.trans h30) hdiff hH₀ hH with hp | hn
  · exact l19_sqg_box Ω h0 h1 a t₅ t₃ t₀ h53 h30 hp hdiff hH₀ hH hz3 hz5 a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄ hp5
  · have h := l19_sqg_box Ω h0 h1 (fun x => -a x) t₅ t₃ t₀ h53 h30 (pos_neg a t₅ t₀ hn)
      (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₅ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) a₂ a₃ a₄ H hHp ha₂ ha₃ ha₄
      (by rwa [redshift_neg])
    simpa only [hubble_neg, redshift_neg, lumDistFlat_neg] using h

theorem fit_direction_r6 : dropped% Checked.Cosmography.B1Fit.fit_direction 6 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5
    hm1 hm3 hm5
  rcases sign_flat Ω h1 a t₅ t₀ (h53.trans (h31.trans h10)) hdiff hH₀ hH with hp | hn
  · exact Checked.Cosmography.B1Fit.fit_direction Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hp hdiff hH₀ hH
      hz1 hz3 hz5 a₂ a₃ H c hHp hp1 hp3 hp5 hm1 hm3 hm5
  · exact Checked.Cosmography.B1Fit.fit_direction Ω h0 h1 (fun x => -a x) t₅ t₃ t₁ t₀ h53 h31 h10
      (pos_neg a t₅ t₀ hn) (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (law_neg Ω a t₅ t₀ hH)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) (by rwa [redshift_neg]) a₂ a₃ H c hHp
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) (by rwa [redshift_neg])
      (by rwa [redshift_neg, lumDistFlat_neg]) (by rwa [redshift_neg, lumDistFlat_neg])
      (by rwa [redshift_neg, lumDistFlat_neg])

theorem rl19_box_unmatched_r6 : dropped% Checked.Cosmography.B1FitRL19.rl19_box_unmatched 6 := by
  intro Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp
    hp1 hp3 hp5
  rcases sign_flat Ω h1 a t₅ t₀ (h53.trans (h31.trans h10)) hdiff hH₀ hH with hp | hn
  · exact Checked.Cosmography.B1FitRL19.rl19_box_unmatched Ω h0 h1 a t₅ t₃ t₁ t₀ h53 h31 h10 hp
      hdiff hH₀ hH hz1 hz3 hz5 a₂ a₃ H c h2l h2u h3l h3u hHp hp1 hp3 hp5
  · have h := Checked.Cosmography.B1FitRL19.rl19_box_unmatched Ω h0 h1 (fun x => -a x) t₅ t₃ t₁ t₀
      h53 h31 h10 (pos_neg a t₅ t₀ hn) (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg])
      (law_neg Ω a t₅ t₀ hH) (by rwa [redshift_neg]) (by rwa [redshift_neg])
      (by rwa [redshift_neg]) a₂ a₃ H c h2l h2u h3l h3u hHp (by rwa [redshift_neg])
      (by rwa [redshift_neg]) (by rwa [redshift_neg])
    simpa only [redshift_neg, lumDistFlat_neg] using h

theorem transverse_neg (K χ : ℝ) : transverse K (-χ) = -transverse K χ := by
  unfold transverse
  split_ifs <;> simp [mul_neg, Real.sin_neg, Real.sinh_neg, neg_div]

theorem lumDist_neg (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) :
    lumDist K (fun x => -a x) t₀ t = lumDist K a t₀ t := by
  simp only [lumDist, comoving_neg, redshift_neg, transverse_neg]; ring

theorem omega0_neg (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : omega0 K (fun x => -a x) t₀ = omega0 K a t₀ := by
  simp only [omega0, hubble_neg, neg_sq]

/-- Curved law with `Ω ≤ 1 ≤ Ω₀`: the scale factor has one sign on the interval (a zero forces
`Ω = Ω₀ = 1`, the Einstein–de Sitter law). -/
theorem sign_curved (Ω K : ℝ) (hΩ : Ω ≤ 1) (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hdiff : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s) (hH₀ : 0 < hubble a t₀)
    (hK : 1 ≤ omega0 K a t₀)
    (hH : ∀ s ∈ Icc t t₀, hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω)) :
    (∀ s ∈ Icc t t₀, 0 < a s) ∨ (∀ s ∈ Icc t t₀, a s < 0) := by
  by_cases he : Ω = 1 ∧ omega0 K a t₀ = 1
  · obtain ⟨h1, h2⟩ := he
    exact sign_eds a t t₀ hdiff hH₀ fun s hs => by rw [hH s hs, h1, h2]; ring_nf
  · refine sign_of_nz a t t₀ htt hdiff fun s hs h0 => ?_
    have e := hH s hs
    have h1 : hubble a s = 0 := by simp [hubble, h0]
    have h2 : redshift a t₀ s = -1 := by simp [redshift, h0]
    rw [h1, h2] at e
    have hpos : 0 < omega0 K a t₀ - Ω := by
      rcases lt_or_eq_of_le hΩ with h | h
      · linarith
      · rcases lt_or_eq_of_le hK with k | k
        · linarith
        · exact absurd ⟨h, k.symm⟩ he
    have h3 : (0 : ℝ) < √(Ω * (1 + -1) ^ 3 + (1 - omega0 K a t₀) * (1 + -1) ^ 2 + omega0 K a t₀ - Ω) :=
      Real.sqrt_pos.2 (by norm_num; linarith)
    nlinarith [mul_pos hH₀ h3]

theorem l19_sq_curved_r5 : dropped% Checked.Cosmography.B1L19Curved.l19_sq_curved 5 := by
  intro Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hdiff hH₀ hK0 hK1 hH hz3 hz5 H hHp
  rcases sign_curved Ω K h1 a t₅ t₀ (h53.trans h30) hdiff hH₀ hK0 hH with hp | hn
  · exact Checked.Cosmography.B1L19Curved.l19_sq_curved Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hp hdiff hH₀ hK0 hK1
      hH hz3 hz5 H hHp
  · have h := Checked.Cosmography.B1L19Curved.l19_sq_curved Ω K h0 h1 (fun x => -a x) t₅ t₃ t₀ h53 h30
      (pos_neg a t₅ t₀ hn) (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (by rwa [omega0_neg])
      (by rwa [omega0_neg]) (fun s hs => by rw [hubble_neg, hubble_neg, redshift_neg, omega0_neg]; exact hH s hs)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) H hHp
    simpa only [redshift_neg, lumDist_neg] using h

theorem l19_sqg_curved_r5 : dropped% Checked.Cosmography.B1L19Curved.l19_sqg_curved 5 := by
  intro Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hdiff hH₀ hK0 hK1 hH hz3 hz5 H hHp
  rcases sign_curved Ω K h1 a t₅ t₀ (h53.trans h30) hdiff hH₀ hK0 hH with hp | hn
  · exact Checked.Cosmography.B1L19Curved.l19_sqg_curved Ω K h0 h1 a t₅ t₃ t₀ h53 h30 hp hdiff hH₀ hK0 hK1
      hH hz3 hz5 H hHp
  · have h := Checked.Cosmography.B1L19Curved.l19_sqg_curved Ω K h0 h1 (fun x => -a x) t₅ t₃ t₀ h53 h30
      (pos_neg a t₅ t₀ hn) (diff_neg a t₅ t₀ hdiff) (by rwa [hubble_neg]) (by rwa [omega0_neg])
      (by rwa [omega0_neg]) (fun s hs => by rw [hubble_neg, hubble_neg, redshift_neg, omega0_neg]; exact hH s hs)
      (by rwa [redshift_neg]) (by rwa [redshift_neg]) H hHp
    simpa only [redshift_neg, lumDist_neg] using h

end Checked.Trust.NCAP
