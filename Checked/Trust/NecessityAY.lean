import Checked.Cosmography.FRCosmo
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Checked.Trust.NonVacuity

/-! Hypothesis necessity for the two refutations `printedF0Mul_false_at` and `printedF0_false_at` of
`Checked.Cosmography.FRCosmo` (run 2026-11-19T1228Z). A model of the metric F(R) setting that is not a
flat model with matter and a cosmological constant: the scale factor is the square of the time, so the
deceleration is minus one half and the jerk, snap and lerk are zero, and F is built along the curvature of
that scale factor from the master equation. The derivative of F at the curvature of time t is a
combination of the minus fourth power, the minus first power and the fourth power of t (the matter term
and the two solutions of the homogeneous equation), with coefficients fixed by Newton's constant today and
by the vanishing fourth derivative of F; away from the curvatures of the model F is continued by a smooth
cutoff. The model exists for every matter density, and the printed relation of the review fails in it
unless six times the density plus twenty five is zero. So the upper density bound of both refutations and
the condition on the printed curvature quantity of the division form are REDUNDANT (each alone). -/

namespace Checked.Trust.NecessityAY
open Real Set Filter Topology Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.FRCosmo

/-! ## The scale factor `t ↦ t²` -/

/-- Scale factor of the model: the square of the time. -/
noncomputable def plA : ℝ → ℝ := fun t => t ^ 2

lemma plA_deriv : deriv plA = fun t => 2 * t := by
  funext t
  unfold plA
  simp

lemma plA_deriv2 : deriv (deriv plA) = fun _ => 2 := by
  rw [plA_deriv]
  funext t
  simp

lemma plA_iter3 : deriv^[3] plA = fun _ => 0 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  rw [plA_deriv, show (fun t : ℝ => 2 * t) = fun t => 2 * t from rfl]
  have h2 : deriv (fun t : ℝ => 2 * t) = fun _ => 2 := by funext t; simp
  rw [h2]
  funext t
  simp

lemma plA_iter (n : ℕ) : deriv^[n + 3] plA = fun _ => 0 := by
  induction n with
  | zero => exact plA_iter3
  | succ n ih =>
    rw [show n + 1 + 3 = (n + 3) + 1 by ring, Function.iterate_succ_apply', ih]
    funext t; simp

lemma plA_hubble {t : ℝ} (ht : t ≠ 0) : hubble plA t = 2 / t := by
  unfold hubble
  rw [plA_deriv]
  unfold plA
  field_simp

lemma plA_dhubble {t : ℝ} (ht : 0 < t) : deriv (hubble plA) t = -2 / t ^ 2 := by
  have heq : hubble plA =ᶠ[𝓝 t] fun u => 2 * u⁻¹ := by
    filter_upwards [lt_mem_nhds ht] with u hu
    rw [plA_hubble hu.ne']; ring
  rw [heq.deriv_eq, ((hasDerivAt_inv ht.ne').const_mul (2 : ℝ)).deriv]
  field_simp

lemma plA_curv {t : ℝ} (ht : 0 < t) : curv plA t = -36 / t ^ 2 := by
  unfold curv
  rw [plA_dhubble ht, plA_hubble ht.ne']
  field_simp
  ring

lemma plA_dcurv {t : ℝ} (ht : 0 < t) : deriv (curv plA) t = 72 / t ^ 3 := by
  have heq : curv plA =ᶠ[𝓝 t] fun u => -36 * (u ^ 2)⁻¹ := by
    filter_upwards [lt_mem_nhds ht] with u hu
    rw [plA_curv hu]; ring
  rw [heq.deriv_eq]
  have h := (((hasDerivAt_pow 2 t).inv (by positivity)).const_mul (-36 : ℝ))
  rw [show deriv (fun u : ℝ => -36 * (u ^ 2)⁻¹) t = _ from h.deriv]
  field_simp
  ring

lemma plA_d2curv {t : ℝ} (ht : 0 < t) : deriv^[2] (curv plA) t = -216 / t ^ 4 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  have heq : deriv (curv plA) =ᶠ[𝓝 t] fun u => 72 * (u ^ 3)⁻¹ := by
    filter_upwards [lt_mem_nhds ht] with u hu
    rw [plA_dcurv hu]; ring
  rw [heq.deriv_eq]
  have h := (((hasDerivAt_pow 3 t).inv (by positivity)).const_mul (72 : ℝ))
  rw [show deriv (fun u : ℝ => 72 * (u ^ 3)⁻¹) t = _ from h.deriv]
  field_simp
  ring

lemma plA_decel : decel plA 1 = -1 / 2 := by
  unfold decel
  rw [plA_deriv2, plA_deriv]
  unfold plA
  norm_num

lemma plA_coeff (n : ℕ) : cosmoCoeff (n + 3) plA 1 = 0 := by
  unfold cosmoCoeff
  rw [iteratedDeriv_eq_iterate, plA_iter n]
  simp

/-! ## The function F -/

/-- A smooth positive function equal to `y` for `y ≥ 1/2`. -/
noncomputable def gy (y : ℝ) : ℝ :=
  smoothTransition (4 * y - 1) * y + (1 - smoothTransition (4 * y - 1))

lemma gy_pos (y : ℝ) : 0 < gy y := by
  unfold gy
  have h0 := smoothTransition.nonneg (4 * y - 1)
  have h1 := smoothTransition.le_one (4 * y - 1)
  rcases le_or_gt y (1 / 4) with hy | hy
  · rw [smoothTransition.zero_of_nonpos (by linarith)]; norm_num
  · rcases le_or_gt y 1 with hy1 | hy1
    · nlinarith
    · nlinarith

lemma gy_eq {y : ℝ} (hy : 1 / 2 ≤ y) : gy y = y := by
  unfold gy
  rw [smoothTransition.one_of_one_le (by linarith)]
  ring

lemma gy_contDiff : ContDiff ℝ 4 gy := by
  unfold gy
  have hs : ContDiff ℝ 4 fun y : ℝ => smoothTransition (4 * y - 1) :=
    smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact (hs.mul contDiff_id).add (contDiff_const.sub hs)

/-- The square root of the curvature over minus thirty six, continued smoothly. -/
noncomputable def uR (R : ℝ) : ℝ := √(gy (-R / 36))

lemma uR_pos (R : ℝ) : 0 < uR R := Real.sqrt_pos.2 (gy_pos _)

lemma uR_contDiff : ContDiff ℝ 4 uR :=
  (gy_contDiff.comp ((contDiff_id.neg).div_const 36)).sqrt fun _ => (gy_pos _).ne'

/-- Coefficients of the homogeneous solutions (Newton's constant today and a vanishing fourth
derivative of F). -/
noncomputable def cA (Ω : ℝ) : ℝ := (32 * Ω + 64) / 65
noncomputable def cB (Ω : ℝ) : ℝ := (Ω + 2) / 130

/-- `F` at today's curvature (from the expansion-rate equation). -/
noncomputable def cF (Ω : ℝ) : ℝ := -12 * (6 * Ω + 25) / 13

/-- The constant term of F. -/
noncomputable def cC (Ω : ℝ) : ℝ := cF Ω - (6 * Ω - 24 * cA Ω + 36 * cB Ω)

/-- F of the model. -/
noncomputable def plF (Ω : ℝ) (R : ℝ) : ℝ :=
  cC Ω + 6 * Ω * uR R ^ 6 - 24 * cA Ω * uR R ^ 3 + 36 * cB Ω * (uR R ^ 2)⁻¹

lemma plF_contDiff (Ω : ℝ) : ContDiff ℝ 4 (plF Ω) := by
  unfold plF
  have h2 : ContDiff ℝ 4 fun R => (uR R ^ 2)⁻¹ :=
    (uR_contDiff.pow 2).inv fun R => (pow_pos (uR_pos R) 2).ne'
  exact (((contDiff_const.add (contDiff_const.mul (uR_contDiff.pow 6))).sub
    (contDiff_const.mul (uR_contDiff.pow 3))).add (contDiff_const.mul h2))

/-! ## Derivatives of F at the curvatures of the model -/

/-- The local square root. -/
noncomputable def uL (R : ℝ) : ℝ := √(-R / 36)

lemma uL_pos {R : ℝ} (hR : R < 0) : 0 < uL R := Real.sqrt_pos.2 (by linarith)

lemma uL_sq {R : ℝ} (hR : R < 0) : uL R ^ 2 = -R / 36 := Real.sq_sqrt (by linarith)

lemma uL_hasDeriv {R : ℝ} (hR : R < 0) : HasDerivAt uL (-(1 / 72) / uL R) R := by
  have hne : -R / 36 ≠ 0 := by intro h; linarith
  have h1 : HasDerivAt (fun x : ℝ => -x / 36) (-1 / 36) R := by
    simpa using ((hasDerivAt_id' R).neg.div_const 36)
  have h := h1.sqrt hne
  have h' : HasDerivAt uL _ R := h
  refine h'.congr_deriv ?_
  unfold uL
  field_simp
  ring

lemma uR_eq {R : ℝ} (hR : R < -18) : uR R = uL R := by
  unfold uR uL
  rw [gy_eq (by linarith)]

noncomputable def L0 (Ω : ℝ) (R : ℝ) : ℝ :=
  cC Ω + 6 * Ω * uL R ^ 6 - 24 * cA Ω * uL R ^ 3 + 36 * cB Ω * (uL R ^ 2)⁻¹
noncomputable def L1 (Ω : ℝ) (R : ℝ) : ℝ :=
  -(Ω / 2) * uL R ^ 4 + cA Ω * uL R + cB Ω * (uL R ^ 4)⁻¹
noncomputable def L2 (Ω : ℝ) (R : ℝ) : ℝ :=
  Ω / 36 * uL R ^ 2 - cA Ω / 72 * (uL R)⁻¹ + cB Ω / 18 * (uL R ^ 6)⁻¹
noncomputable def L3 (Ω : ℝ) (R : ℝ) : ℝ :=
  -(Ω / 1296) - cA Ω / 5184 * (uL R ^ 3)⁻¹ + cB Ω / 216 * (uL R ^ 8)⁻¹
noncomputable def L4 (Ω : ℝ) (R : ℝ) : ℝ :=
  -(cA Ω / 124416) * (uL R ^ 5)⁻¹ + cB Ω / 1944 * (uL R ^ 10)⁻¹

lemma pow_hd {R : ℝ} (hR : R < 0) (n : ℕ) :
    HasDerivAt (fun x => uL x ^ (n + 2)) (-((n + 2 : ℝ) / 72) * uL R ^ n) R := by
  have hu := uL_pos hR
  have h := (uL_hasDeriv hR).pow (n + 2)
  convert h using 1
  push_cast
  rw [pow_succ]
  field_simp

lemma inv_hd {R : ℝ} (hR : R < 0) (n : ℕ) :
    HasDerivAt (fun x => (uL x ^ n)⁻¹) ((n : ℝ) / 72 * (uL R ^ (n + 2))⁻¹) R := by
  have hu := uL_pos hR
  have h := ((uL_hasDeriv hR).pow n).inv (pow_pos hu n).ne'
  convert h using 1
  rcases n with _ | n
  · simp
  · push_cast
    simp only [Pi.pow_apply]
    field_simp
    ring

lemma uL_hd {R : ℝ} (hR : R < 0) : HasDerivAt uL (-((1 : ℝ) / 72) * (uL R ^ 1)⁻¹) R := by
  convert uL_hasDeriv hR using 1
  simp; ring

lemma L0_hd (Ω : ℝ) {R : ℝ} (hR : R < 0) : HasDerivAt (L0 Ω) (L1 Ω R) R := by
  have hu := uL_pos hR
  have h := ((((hasDerivAt_const R (cC Ω)).add ((pow_hd hR 4).const_mul (6 * Ω))).sub
    ((pow_hd hR 1).const_mul (24 * cA Ω))).add ((inv_hd hR 2).const_mul (36 * cB Ω)))
  have h' : HasDerivAt (L0 Ω) _ R := h
  refine h'.congr_deriv ?_
  unfold L1
  push_cast
  field_simp
  ring

lemma L1_hd (Ω : ℝ) {R : ℝ} (hR : R < 0) : HasDerivAt (L1 Ω) (L2 Ω R) R := by
  have hu := uL_pos hR
  have h := ((((pow_hd hR 2).const_mul (-(Ω / 2))).add ((uL_hd hR).const_mul (cA Ω))).add
    ((inv_hd hR 4).const_mul (cB Ω)))
  have h' : HasDerivAt (L1 Ω) _ R := h
  refine h'.congr_deriv ?_
  unfold L2
  push_cast
  field_simp
  ring

lemma L2_hd (Ω : ℝ) {R : ℝ} (hR : R < 0) : HasDerivAt (L2 Ω) (L3 Ω R) R := by
  have hu := uL_pos hR
  have e : L2 Ω = fun x => Ω / 36 * uL x ^ (0 + 2) - cA Ω / 72 * (uL x ^ 1)⁻¹
      + cB Ω / 18 * (uL x ^ 6)⁻¹ := by
    funext x; unfold L2; simp
  rw [e]
  have h1 := ((((pow_hd hR 0).const_mul (Ω / 36)).sub ((inv_hd hR 1).const_mul (cA Ω / 72))).add
    ((inv_hd hR 6).const_mul (cB Ω / 18)))
  have h' : HasDerivAt (fun x => Ω / 36 * uL x ^ (0 + 2) - cA Ω / 72 * (uL x ^ 1)⁻¹
      + cB Ω / 18 * (uL x ^ 6)⁻¹) _ R := h1
  refine h'.congr_deriv ?_
  unfold L3
  push_cast
  field_simp
  ring

lemma L3_hd (Ω : ℝ) {R : ℝ} (hR : R < 0) : HasDerivAt (L3 Ω) (L4 Ω R) R := by
  have hu := uL_pos hR
  have h := (((hasDerivAt_const R (-(Ω / 1296))).sub ((inv_hd hR 3).const_mul (cA Ω / 5184))).add
    ((inv_hd hR 8).const_mul (cB Ω / 216)))
  have h' : HasDerivAt (L3 Ω) _ R := h
  refine h'.congr_deriv ?_
  unfold L4
  push_cast
  field_simp
  ring

lemma plF_eqOn (Ω : ℝ) : EqOn (plF Ω) (L0 Ω) (Iio (-18)) := by
  intro R hR
  unfold plF L0
  rw [uR_eq hR]

lemma eqOn_deriv_of {f g g' : ℝ → ℝ} (hfg : EqOn f g (Iio (-18)))
    (hg : ∀ R ∈ Iio (-18 : ℝ), HasDerivAt g (g' R) R) : EqOn (deriv f) g' (Iio (-18)) := by
  intro R hR
  rw [hfg.deriv isOpen_Iio hR, (hg R hR).deriv]

lemma plF_d1 (Ω : ℝ) : EqOn (deriv (plF Ω)) (L1 Ω) (Iio (-18)) :=
  eqOn_deriv_of (plF_eqOn Ω) fun R hR => L0_hd Ω (by simp at hR; linarith)

lemma plF_d2 (Ω : ℝ) : EqOn (deriv^[2] (plF Ω)) (L2 Ω) (Iio (-18)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  exact eqOn_deriv_of (plF_d1 Ω) fun R hR => L1_hd Ω (by simp at hR; linarith)

lemma plF_d3 (Ω : ℝ) : EqOn (deriv^[3] (plF Ω)) (L3 Ω) (Iio (-18)) := by
  rw [Function.iterate_succ_apply']
  exact eqOn_deriv_of (plF_d2 Ω) fun R hR => L2_hd Ω (by simp at hR; linarith)

lemma plF_d4 (Ω : ℝ) : EqOn (deriv^[4] (plF Ω)) (L4 Ω) (Iio (-18)) := by
  rw [Function.iterate_succ_apply']
  exact eqOn_deriv_of (plF_d3 Ω) fun R hR => L3_hd Ω (by simp at hR; linarith)

/-! ## The model -/

lemma uL_curv {t : ℝ} (ht : 0 < t) : uL (-36 / t ^ 2) = 1 / t := by
  unfold uL
  rw [show -(-36 / t ^ 2) / 36 = (1 / t) ^ 2 by field_simp]
  exact Real.sqrt_sq (by positivity)

lemma curv_lt {t : ℝ} (ht : 0 < t) (ht' : t < 4 / 3) : -36 / t ^ 2 < -18 := by
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

lemma curv_one : curv plA 1 = -36 := by rw [plA_curv one_pos]; norm_num

theorem pl_model (Ω : ℝ) : IsFRCosmo Ω plA (plF Ω) 1 := by
  have hc1 : curv plA 1 ∈ Iio (-18 : ℝ) := by rw [curv_one]; norm_num
  have hu1 : uL (curv plA 1) = 1 := by rw [curv_one]; unfold uL; norm_num
  refine ⟨by unfold plA; norm_num, by rw [plA_hubble one_ne_zero]; norm_num,
    (by unfold plA; fun_prop : ContDiff ℝ 5 plA).contDiffAt, plF_contDiff Ω, ?_, ?_, ?_, ?_⟩
  · unfold FriedmannEq rhoM
    rw [plF_d1 Ω hc1, plF_d2 Ω hc1, plF_eqOn Ω hc1, plA_hubble one_ne_zero, plA_dcurv one_pos]
    unfold L0 L1 L2
    rw [hu1, curv_one]
    unfold cC cF cA cB plA
    norm_num
    ring
  · filter_upwards [Ioo_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) < 4 / 3 by norm_num)] with t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hc : curv plA t ∈ Iio (-18 : ℝ) := by
      rw [plA_curv ht0]; exact curv_lt ht0 ht.2
    unfold MasterEq rhoM
    rw [plF_d1 Ω hc, plF_d2 Ω hc, plF_d3 Ω hc, plA_dhubble ht0, plA_hubble ht0.ne',
      plA_hubble one_ne_zero, plA_dcurv ht0, plA_d2curv ht0]
    unfold L1 L2 L3
    rw [plA_curv ht0, uL_curv ht0]
    unfold plA cA cB
    field_simp
    ring
  · rw [plF_d1 Ω hc1]
    unfold L1
    rw [hu1]
    unfold cA cB
    ring
  · rw [plF_d4 Ω hc1]
    unfold L4
    rw [hu1]
    unfold cA cB
    ring

theorem pl_facts (Ω : ℝ) :
    decel plA 1 = -1 / 2 ∧ cosmoCoeff 3 plA 1 = 0 ∧ cosmoCoeff 4 plA 1 = 0 ∧
      cosmoCoeff 5 plA 1 = 0 ∧ hubble plA 1 = 2 ∧ plF Ω (curv plA 1) = cF Ω := by
  refine ⟨plA_decel, plA_coeff 0, plA_coeff 1, plA_coeff 2,
    by rw [plA_hubble one_ne_zero]; norm_num, ?_⟩
  have hc1 : curv plA 1 ∈ Iio (-18 : ℝ) := by rw [curv_one]; norm_num
  rw [plF_eqOn Ω hc1]
  unfold L0
  rw [show uL (curv plA 1) = 1 by rw [curv_one]; unfold uL; norm_num]
  unfold cC
  ring

/-- In the model, the multiplied-out printed relation holds only at density minus twenty five sixths. -/
theorem pl_mul_false (Ω : ℝ) (hΩ : 6 * Ω + 25 ≠ 0) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
          * F (curv a t₀) =
        -6 * hubble a t₀ ^ 2 *
          (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) := by
  intro h
  have e := h plA (plF Ω) 1 (pl_model Ω)
  obtain ⟨hq, hj, hs, hl, hH, hF⟩ := pl_facts Ω
  rw [hq, hj, hs, hl, hH, hF] at e
  unfold printedR P0 Q0 cF at e
  apply hΩ
  linear_combination (-(13 : ℝ) / 540) * e

/-- In the model, the division form of the printed relation holds only at density minus twenty five sixths. -/
theorem pl_div_false (Ω : ℝ) (hΩ : 6 * Ω + 25 ≠ 0) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 →
      F (curv a t₀) / (6 * hubble a t₀ ^ 2) =
        -(P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
          / printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) := by
  intro h
  obtain ⟨hq, hj, hs, hl, hH, hF⟩ := pl_facts Ω
  have hne : printedR (decel plA 1) (cosmoCoeff 3 plA 1) (cosmoCoeff 4 plA 1)
      (cosmoCoeff 5 plA 1) ≠ 0 := by
    rw [hq, hj, hs, hl]; unfold printedR; norm_num
  have e := h plA (plF Ω) 1 (pl_model Ω) hne
  rw [hq, hj, hs, hl, hH, hF] at e
  unfold printedR P0 Q0 cF at e
  apply hΩ
  field_simp at e
  linear_combination (-(1 : ℝ) / 8640) * e

theorem printedF0Mul_false_at_r2 :
    dropped% Checked.Cosmography.FRCosmo.printedF0Mul_false_at 2 := by
  intro Ω h0
  exact pl_mul_false Ω (by linarith)

theorem printedF0_false_at_r2 :
    dropped% Checked.Cosmography.FRCosmo.printedF0_false_at 2 := by
  intro Ω h0 _
  exact pl_div_false Ω (by linarith)

theorem printedF0_false_at_r3 :
    dropped% Checked.Cosmography.FRCosmo.printedF0_false_at 3 := by
  intro Ω h0 _
  exact pl_div_false Ω (by linarith)

end Checked.Trust.NecessityAY
