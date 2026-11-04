import Mathlib
import Work.Data.FR13
import Work.Data.FR13Blind
import Work.Data.FR13GapCerts

/-!
# Audit of `Work.Data.FR13`: the blind restatement closed in Lean

`Work.Data.FR13Blind` (namespace `Blind.FR13`, copied verbatim) is the blind restater's own
reading of the Farooq & Ratra 2013 claim. Differences from the program's frozen definitions:
* the blind likelihood `LH` integrates over H₀ ∈ (0, ∞) (Eq. 16 of Farooq, Mania & Ratra,
  arXiv:1211.4253, cited by the paper), the program's `margChiSq` over all real H₀;
* "best fit" is a maximiser of the likelihood on [0, 1] (`IsMaxOn`), not a minimiser of −2 log;
* the transition redshift is the closed form `zda Ω = (2(1−Ω)/Ω)^(1/3) − 1` (real power).

Closed here (prior 68 ± 2.8, the prior the blind restater chose):
* `blind_integrand`: the blind integrand equals the program's pointwise.
* `tail_bound`: on Ω ∈ [0, 1] the part of the integral over H₀ ≤ 0 is at most 10⁻²⁰ of the
  whole (Gaussian tail: (H − μ)² ≥ μ² for H ≤ 0 ≤ μ, and B²/(4A) ≥ 200).
* `blind_exists` (blind `exists_bestFit`): a maximiser exists (dominated continuity).
* `blind_tight`, `blind_rounds` (blind `bestFit_rounds_to_029`): every blind best fit lies in
  (0.2875, 0.2881), hence in [0.285, 0.295). Uses a gap version of the program's certificates
  (`Work.Data.FR13GapCerts`, η = 10⁻¹²) since the two likelihoods differ by a factor within
  10⁻²⁰ of 1.
* `blind_zda_range` (blind `bestFit_zda_range`).
* `blind_chi2min_false`: the blind's literal reading of the printed χ²_min = 18.24 is false
  (the value at a best fit is below 18.235).
* `blind_zda0698_false`: the blind's literal reading of the printed z_da = 0.698 is false.
* `blind_zda029` (blind `zda_029`): 0.698 is z_da at the rounded Ω = 0.29.
* `blind_zda_spec` (blind `zda_spec`): zda is positive, q vanishes there, q < 0 on [0, zda), q > 0 above.
-/

namespace Work.Data.FR13Audit
open MeasureTheory Real Set Work.Data.FR13Tools Work.Data.FR13Certs

/-- The program's integrand at prior 68 ± 2.8. -/
noncomputable def f (Ω H : ℝ) : ℝ :=
  Real.exp (-chiSq tbl H Ω / 2) * (Real.exp (-(H - 68) ^ 2 / (2 * 2.8 ^ 2)) / √(2 * π * 2.8 ^ 2))

theorem blind_table : Blind.FR13.table = tbl := rfl

theorem blind_integrand (Ω H : ℝ) :
    Real.exp (-Blind.FR13.chi2H H Ω / 2) * Blind.FR13.prior H = f Ω H := by
  have hc : Blind.FR13.chi2H H Ω = chiSq tbl H Ω := by
    unfold Blind.FR13.chi2H chiSq Blind.FR13.Hth Blind.FR13.E Blind.FR13.zObs Blind.FR13.HObs
      Blind.FR13.σObs
    rw [blind_table]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow]
  rw [hc]
  unfold f Blind.FR13.prior Blind.FR13.H0bar Blind.FR13.σH0
  ring

theorem LH_eq (Ω : ℝ) : Blind.FR13.LH Ω = ∫ H in Ioi (0 : ℝ), f Ω H := by
  unfold Blind.FR13.LH
  exact setIntegral_congr_fun measurableSet_Ioi fun H _ => blind_integrand Ω H

theorem margChi_eq (Ω : ℝ) : margChi tbl 68 2.8 Ω = -2 * Real.log (∫ H, f Ω H) := rfl

/-! ### Gaussian form -/

noncomputable def A (Ω : ℝ) : ℝ := S2 tbl Ω + 1 / 2.8 ^ 2
noncomputable def B (Ω : ℝ) : ℝ := S1 tbl Ω + 68 / 2.8 ^ 2
noncomputable def C : ℝ := S0 tbl + 68 ^ 2 / 2.8 ^ 2
noncomputable def κ (Ω : ℝ) : ℝ := Real.exp (-(C - B Ω ^ 2 / A Ω) / 2) / √(2 * π * 2.8 ^ 2)

theorem A_pos (Ω : ℝ) : 0 < A Ω := by
  have : 0 ≤ S2 tbl Ω := Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  unfold A; positivity

theorem κ_pos (Ω : ℝ) : 0 < κ Ω := by
  unfold κ
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.2 (by positivity))

theorem f_eq (Ω H : ℝ) :
    f Ω H = κ Ω * Real.exp (-(A Ω / 2) * (H - B Ω / A Ω) ^ 2) := by
  have hA := (A_pos Ω).ne'
  unfold f κ
  rw [mul_div_assoc', ← Real.exp_add, chiSq_expand, div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  have key : A Ω / 2 * (H - B Ω / A Ω) ^ 2 = (A Ω * H ^ 2 - 2 * B Ω * H + B Ω ^ 2 / A Ω) / 2 := by
    field_simp; ring
  rw [neg_mul, key]
  unfold A B C
  ring

theorem g_int (a μ : ℝ) (ha : 0 < a) :
    Integrable (fun H : ℝ => Real.exp (-a * (H - μ) ^ 2)) :=
  (integrable_exp_neg_mul_sq ha).comp_sub_right μ

theorem g_integral (a μ : ℝ) (ha : 0 < a) :
    ∫ H : ℝ, Real.exp (-a * (H - μ) ^ 2) = √(π / a) := by
  rw [integral_sub_right_eq_self (fun x => Real.exp (-a * x ^ 2)) μ, integral_gaussian]

theorem f_int (Ω : ℝ) : Integrable (f Ω) := by
  have : f Ω = fun H => κ Ω * Real.exp (-(A Ω / 2) * (H - B Ω / A Ω) ^ 2) := funext (f_eq Ω)
  rw [this]
  exact (g_int _ _ (by have := A_pos Ω; positivity)).const_mul _

theorem f_nonneg (Ω H : ℝ) : 0 ≤ f Ω H := by
  unfold f; positivity

theorem I_eq (Ω : ℝ) : ∫ H, f Ω H = κ Ω * √(π / (A Ω / 2)) := by
  simp_rw [f_eq Ω]
  rw [integral_const_mul, g_integral _ _ (by have := A_pos Ω; positivity)]

theorem I_pos (Ω : ℝ) : 0 < ∫ H, f Ω H := by
  rw [I_eq]
  exact mul_pos (κ_pos Ω) (Real.sqrt_pos.2 (by have := A_pos Ω; positivity))

/-! ### Crude bounds on A and B over [0, 1] -/

theorem esq_ge_one {Ω : ℝ} (h0 : 0 ≤ Ω) (i : Fin 28) : 1 ≤ esq tbl Ω i := by
  unfold esq
  have : 1 ≤ (1 + (tbl i).1) ^ 3 := one_le_pow₀ (by linarith [hz i])
  nlinarith

theorem Q_val : ∑ i : Fin 28, (tbl i).2.1 / (tbl i).2.2 ^ 2 ≥ (28.5 : ℝ) := by
  unfold tbl
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

theorem B_ge {Ω : ℝ} (h0 : 0 ≤ Ω) : 37 ≤ B Ω := by
  have hS : ∑ i : Fin 28, (tbl i).2.1 / (tbl i).2.2 ^ 2 ≤ S1 tbl Ω := by
    unfold S1
    refine Finset.sum_le_sum fun i _ => ?_
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    have h1 : 1 ≤ √(esq tbl Ω i) := Real.one_le_sqrt.2 (esq_ge_one h0 i)
    nlinarith [hh i]
  have := Q_val
  unfold B; norm_num at *; linarith

theorem A_le {Ω : ℝ} (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) : A Ω ≤ 1.67 := by
  unfold A
  rw [S2_lin tbl hz h0 h1, hP0, hP1]
  have hp1 : (0 : ℝ) ≤ 29609639690396511539014892212396471451 / 24121729710826871279187049200000000000 := by
    norm_num
  nlinarith

theorem exp200 : (11 : ℝ) ^ 20 ≤ Real.exp 200 := by
  have h := Real.add_one_le_exp (10 : ℝ)
  have e : Real.exp 200 = Real.exp 10 ^ 20 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  exact pow_le_pow_left₀ (by norm_num) (by linarith) 20

/-! ### The tail over H₀ ≤ 0 -/

theorem tail_bound {Ω : ℝ} (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    ∫ H in (Ioi (0 : ℝ))ᶜ, f Ω H ≤ 1 / 10 ^ 20 * ∫ H, f Ω H := by
  set a := A Ω with ha
  set μ := B Ω / A Ω with hμ
  have hapos : 0 < a := A_pos Ω
  have hμpos : 0 < μ := div_pos (by linarith [B_ge h0]) hapos
  set e := Real.exp (-(a * μ ^ 2) / 4) with he
  -- pointwise bound on the complement
  have hpt : ∀ H ∈ (Ioi (0 : ℝ))ᶜ, f Ω H ≤ κ Ω * (e * Real.exp (-(a / 4) * (H - μ) ^ 2)) := by
    intro H hH
    simp only [mem_compl_iff, mem_Ioi, not_lt] at hH
    rw [f_eq Ω]
    refine mul_le_mul_of_nonneg_left ?_ (κ_pos Ω).le
    rw [he, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : μ ^ 2 ≤ (H - μ) ^ 2 := by nlinarith
    nlinarith
  have hint2 : Integrable (fun H => κ Ω * (e * Real.exp (-(a / 4) * (H - μ) ^ 2))) :=
    ((g_int _ _ (by positivity)).const_mul e).const_mul _
  have s1 : ∫ H in (Ioi (0 : ℝ))ᶜ, f Ω H
      ≤ ∫ H in (Ioi (0 : ℝ))ᶜ, κ Ω * (e * Real.exp (-(a / 4) * (H - μ) ^ 2)) :=
    setIntegral_mono_on (f_int Ω).integrableOn hint2.integrableOn
      measurableSet_Ioi.compl hpt
  have s2 : ∫ H in (Ioi (0 : ℝ))ᶜ, κ Ω * (e * Real.exp (-(a / 4) * (H - μ) ^ 2))
      ≤ ∫ H, κ Ω * (e * Real.exp (-(a / 4) * (H - μ) ^ 2)) :=
    setIntegral_le_integral hint2 (Filter.Eventually.of_forall fun H => by
      have := κ_pos Ω; positivity)
  have s3 : ∫ H, κ Ω * (e * Real.exp (-(a / 4) * (H - μ) ^ 2)) = κ Ω * (e * √(π / (a / 4))) := by
    rw [integral_const_mul, integral_const_mul, g_integral _ _ (by positivity)]
  -- √(π/(a/4)) = 2 √(π/(a/2))
  have s4 : √(π / (a / 4)) ≤ 2 * √(π / (a / 2)) := by
    have h : π / (a / 4) ≤ 2 ^ 2 * (π / (a / 2)) := by
      rw [div_le_iff₀ (by positivity)]; field_simp; nlinarith [Real.pi_pos]
    calc √(π / (a / 4)) ≤ √(2 ^ 2 * (π / (a / 2))) := Real.sqrt_le_sqrt h
      _ = 2 * √(π / (a / 2)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  -- e is tiny
  have hBA : a * μ ^ 2 / 4 ≥ 200 := by
    have hB := B_ge h0
    have hA := A_le h0 h1
    have : a * μ ^ 2 = B Ω ^ 2 / a := by rw [hμ, ← ha]; field_simp
    rw [this]
    rw [ge_iff_le, le_div_iff₀ (by norm_num), le_div_iff₀ hapos]
    nlinarith
  have he2 : e ≤ 1 / 11 ^ 20 := by
    rw [he]
    have h2 : Real.exp (-(a * μ ^ 2) / 4) ≤ Real.exp (-200) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-200) ≤ 1 / 11 ^ 20 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) exp200
    linarith
  rw [I_eq, ← ha]
  have hsq : 0 < √(π / (a / 2)) := Real.sqrt_pos.2 (by positivity)
  have hκ := κ_pos Ω
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  calc ∫ H in (Ioi (0 : ℝ))ᶜ, f Ω H ≤ κ Ω * (e * (2 * √(π / (a / 2)))) := by
        refine (s1.trans s2).trans ?_
        rw [s3]; gcongr
    _ ≤ κ Ω * ((1 / 11 ^ 20) * (2 * √(π / (a / 2)))) := by gcongr
    _ ≤ 1 / 10 ^ 20 * (κ Ω * √(π / (a / 2))) := by
        have : (1 : ℝ) / 11 ^ 20 * 2 ≤ 1 / 10 ^ 20 := by norm_num
        nlinarith [mul_pos hκ hsq]

/-- The blind likelihood is the program's integral up to a factor in [1 − 10⁻²⁰, 1]. -/
theorem LH_bounds {Ω : ℝ} (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1) :
    (1 - 1 / 10 ^ 20) * ∫ H, f Ω H ≤ Blind.FR13.LH Ω ∧ Blind.FR13.LH Ω ≤ ∫ H, f Ω H := by
  have hsplit := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) (f_int Ω)
  have ht := tail_bound h0 h1
  have htn : 0 ≤ ∫ H in (Ioi (0 : ℝ))ᶜ, f Ω H :=
    setIntegral_nonneg measurableSet_Ioi.compl fun H _ => f_nonneg Ω H
  rw [LH_eq]
  constructor <;> nlinarith

/-! ### Existence of a blind best fit -/

theorem chiSq_nonneg (H Ω : ℝ) : 0 ≤ chiSq tbl H Ω :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem LH_cont : ContinuousOn Blind.FR13.LH (Icc 0 1) := by
  have he : Blind.FR13.LH = fun Ω => ∫ H in Ioi (0 : ℝ), f Ω H := funext LH_eq
  rw [he]
  let bound : ℝ → ℝ := fun H =>
    Real.exp (-(1 / (2 * 2.8 ^ 2)) * (H - 68) ^ 2) / √(2 * π * 2.8 ^ 2)
  have hbi : Integrable bound := (g_int _ _ (by norm_num)).div_const _
  refine continuousOn_of_dominated (bound := bound) ?_ ?_ hbi.integrableOn ?_
  · intro Ω _
    refine Continuous.aestronglyMeasurable ?_
    unfold f chiSq; fun_prop
  · intro Ω _
    refine Filter.Eventually.of_forall fun H => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (f_nonneg Ω H)]
    unfold f
    have h1 : Real.exp (-chiSq tbl H Ω / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := chiSq_nonneg H Ω; linarith)
    have h2 : Real.exp (-(H - 68) ^ 2 / (2 * 2.8 ^ 2)) / √(2 * π * 2.8 ^ 2) = bound H := by
      simp only [bound]; congr 2; ring
    rw [h2]
    have : 0 ≤ bound H := by simp only [bound]; positivity
    nlinarith
  · refine Filter.Eventually.of_forall fun H => ?_
    refine Continuous.continuousOn ?_
    unfold f chiSq; fun_prop

theorem blind_exists : ∃ Ωm, Blind.FR13.IsBestFit Ωm := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one) LH_cont
  exact ⟨x, hmax, hx⟩

/-! ### Location of every blind best fit -/

theorem exp_eta : Real.exp (-(1 / 10 ^ 12) / 2) ≤ 1 - 1 / 10 ^ 20 := by
  have h := Real.add_one_le_exp ((1 / 10 ^ 12) / 2 : ℝ)
  rw [neg_div, Real.exp_neg, inv_eq_one_div]
  calc 1 / Real.exp ((1 / 10 ^ 12) / 2) ≤ 1 / ((1 / 10 ^ 12) / 2 + 1) :=
        one_div_le_one_div_of_le (by norm_num) h
    _ ≤ 1 - 1 / 10 ^ 20 := by norm_num

theorem not_best_of_gap (Ω : ℝ) (h0 : 0 ≤ Ω) (h1 : Ω ≤ 1)
    (hg : margChi tbl 68 2.8 0.2878 + 1 / 10 ^ 12 < margChi tbl 68 2.8 Ω) :
    ¬ Blind.FR13.IsBestFit Ω := by
  rintro ⟨hmax, -⟩
  have hr : Blind.FR13.LH 0.2878 ≤ Blind.FR13.LH Ω :=
    hmax (show (0.2878 : ℝ) ∈ Icc 0 1 from ⟨by norm_num, by norm_num⟩)
  have hb := LH_bounds h0 h1
  have hbr := LH_bounds (Ω := 0.2878) (by norm_num) (by norm_num)
  rw [margChi_eq, margChi_eq] at hg
  have hI := I_pos Ω
  have hIr := I_pos 0.2878
  -- log I(Ω) < log I(r) − η/2
  have hlog : Real.log (∫ H, f Ω H) < Real.log (∫ H, f 0.2878 H) + (-(1 / 10 ^ 12) / 2) := by
    linarith
  have hexp := Real.exp_lt_exp.2 hlog
  rw [Real.exp_log hI, Real.exp_add, Real.exp_log hIr] at hexp
  have := exp_eta
  have : (∫ H, f Ω H) < (1 - 1 / 10 ^ 20) * ∫ H, f 0.2878 H := by nlinarith
  linarith [hb.2, hbr.1]

open Work.Data.FR13GapCerts in
theorem blind_tight (Ωm : ℝ) (h : Blind.FR13.IsBestFit Ωm) : 0.2875 < Ωm ∧ Ωm < 0.2881 := by
  obtain ⟨h0, h1⟩ := h.2
  constructor
  · by_contra hc; rw [not_lt] at hc
    exact not_best_of_gap Ωm h0 h1 (low68_gap Ωm h0 hc) h
  · by_contra hc; rw [not_lt] at hc
    exact not_best_of_gap Ωm h0 h1 (high68_gap Ωm hc h1) h

/-- The blind restater's main claim (`Blind.FR13.bestFit_rounds_to_029`). -/
theorem blind_rounds : ∀ Ωm, Blind.FR13.IsBestFit Ωm → (0.285 : ℝ) ≤ Ωm ∧ Ωm < 0.295 := by
  intro Ωm h
  obtain ⟨a, b⟩ := blind_tight Ωm h
  exact ⟨by linarith, by linarith⟩

/-! ### Transition redshift -/

theorem zda_cube {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    (1 + Blind.FR13.zda Ω) ^ 3 * Ω = 2 * (1 - Ω) ∧ 0 < 1 + Blind.FR13.zda Ω := by
  unfold Blind.FR13.zda
  have hx : 0 < 2 * (1 - Ω) / Ω := div_pos (by linarith) h0
  have hc : ((2 * (1 - Ω) / Ω) ^ ((1 : ℝ) / 3)) ^ 3 = 2 * (1 - Ω) / Ω := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  simp only [add_sub_cancel]
  refine ⟨?_, Real.rpow_pos_of_pos hx _⟩
  rw [hc]; field_simp

theorem zda_bounds {Ω lo hi : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1)
    (hlo : (1 + lo) ^ 3 * Ω < 2 * (1 - Ω)) (hhi : 2 * (1 - Ω) < (1 + hi) ^ 3 * Ω)
    (_hlo1 : 0 ≤ 1 + lo) (hhi1 : 0 ≤ 1 + hi) :
    lo < Blind.FR13.zda Ω ∧ Blind.FR13.zda Ω < hi := by
  obtain ⟨hc, hp⟩ := zda_cube h0 h1
  constructor
  · by_contra h; rw [not_lt] at h
    have : (1 + Blind.FR13.zda Ω) ^ 3 ≤ (1 + lo) ^ 3 := pow_le_pow_left₀ hp.le (by linarith) 3
    nlinarith
  · by_contra h; rw [not_lt] at h
    have : (1 + hi) ^ 3 ≤ (1 + Blind.FR13.zda Ω) ^ 3 :=
      pow_le_pow_left₀ hhi1 (by linarith) 3
    nlinarith

theorem blind_zda_tight (Ωm : ℝ) (h : Blind.FR13.IsBestFit Ωm) :
    (0.703 : ℝ) < Blind.FR13.zda Ωm ∧ Blind.FR13.zda Ωm < 0.706 := by
  obtain ⟨a, b⟩ := blind_tight Ωm h
  exact zda_bounds (by linarith) (by linarith) (by nlinarith) (by nlinarith) (by norm_num) (by norm_num)

/-- The blind restater's `bestFit_zda_range`. -/
theorem blind_zda_range :
    ∀ Ωm, Blind.FR13.IsBestFit Ωm → (0.684 : ℝ) < Blind.FR13.zda Ωm ∧ Blind.FR13.zda Ωm < 0.713 := by
  intro Ωm h
  obtain ⟨a, b⟩ := blind_zda_tight Ωm h
  exact ⟨by linarith, by linarith⟩

/-- The blind restater's literal reading of the printed z_da = 0.698 is false. -/
theorem blind_zda0698_false :
    ¬ (∀ Ωm, Blind.FR13.IsBestFit Ωm → (0.6975 : ℝ) ≤ Blind.FR13.zda Ωm ∧ Blind.FR13.zda Ωm < 0.6985) := by
  intro h
  obtain ⟨Ω, hΩ⟩ := blind_exists
  have h1 := (h Ω hΩ).2
  have h2 := (blind_zda_tight Ω hΩ).1
  linarith

/-- The blind restater's `zda_029`: the printed 0.698 is z_da at the rounded Ω = 0.29. -/
theorem blind_zda029 :
    (0.6975 : ℝ) ≤ Blind.FR13.zda 0.29 ∧ Blind.FR13.zda 0.29 < 0.6985 := by
  obtain ⟨a, b⟩ := zda_bounds (Ω := 0.29) (lo := 0.6975) (hi := 0.6985) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨a.le, b⟩

/-- The blind restater's literal reading of the printed χ²_min = 18.24 is false: at a best fit
the blind χ² is below 18.235. -/
theorem blind_chi2min_false :
    ¬ (∀ Ωm, Blind.FR13.IsBestFit Ωm →
      (18.235 : ℝ) ≤ Blind.FR13.chi2Marg Ωm ∧ Blind.FR13.chi2Marg Ωm < 18.245) := by
  intro h
  obtain ⟨Ω, hΩ⟩ := blind_exists
  have h1 := (h Ω hΩ).1
  obtain ⟨h0, h1'⟩ := hΩ.2
  have hr : Blind.FR13.LH 0.2878 ≤ Blind.FR13.LH Ω :=
    hΩ.1 (show (0.2878 : ℝ) ∈ Icc 0 1 from ⟨by norm_num, by norm_num⟩)
  have hbr := LH_bounds (Ω := 0.2878) (by norm_num) (by norm_num)
  have hIr := I_pos 0.2878
  have hm := Work.Data.FR13ValCerts.minhi68
  rw [margChi_eq] at hm
  have hpos : 0 < (1 - 1 / 10 ^ 20) * ∫ H, f 0.2878 H := mul_pos (by norm_num) hIr
  have hle : Real.log ((1 - 1 / 10 ^ 20) * ∫ H, f 0.2878 H) ≤ Real.log (Blind.FR13.LH Ω) :=
    Real.log_le_log hpos (hbr.1.trans hr)
  rw [Real.log_mul (by norm_num) hIr.ne'] at hle
  have hl1 : -(1 / 10 ^ 19 : ℝ) ≤ Real.log (1 - 1 / 10 ^ 20) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 - 1 / 10 ^ 20 by norm_num)
    have e : (1 : ℝ) - (1 - 1 / 10 ^ 20)⁻¹ ≥ -(1 / 10 ^ 19) := by norm_num
    linarith
  unfold Blind.FR13.chi2Marg at h1
  linarith

/-! ### The blind `zda_spec` (sign of the deceleration parameter) -/

theorem decel_eq {Ω z : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hz : 0 ≤ 1 + z) :
    Blind.FR13.decel Ω z = -1 + 3 * Ω * (1 + z) ^ 3 / (2 * (Ω * (1 + z) ^ 3 + 1 - Ω)) := by
  have hy : 0 < Ω * (1 + z) ^ 3 + 1 - Ω := by
    have : 0 ≤ Ω * (1 + z) ^ 3 := mul_nonneg h0.le (pow_nonneg hz 3)
    linarith
  have hg : HasDerivAt (fun w : ℝ => Ω * (1 + w) ^ 3 + 1 - Ω) (Ω * (3 * (1 + z) ^ 2)) z := by
    have h2 := (((((hasDerivAt_id' z).const_add 1).pow 3).const_mul Ω).add_const 1).sub_const Ω
    convert h2 using 1
    push_cast; ring
  have hd := hg.sqrt hy.ne'
  have hdv : deriv (Blind.FR13.Hfun Ω) z = Ω * (3 * (1 + z) ^ 2) / (2 * √(Ω * (1 + z) ^ 3 + 1 - Ω)) := by
    have : Blind.FR13.Hfun Ω = fun w => √(Ω * (1 + w) ^ 3 + 1 - Ω) := by
      funext w; rfl
    rw [this]; exact hd.deriv
  unfold Blind.FR13.decel
  rw [hdv]
  have hs : 0 < √(Ω * (1 + z) ^ 3 + 1 - Ω) := Real.sqrt_pos.2 hy
  have hss : √(Ω * (1 + z) ^ 3 + 1 - Ω) * √(Ω * (1 + z) ^ 3 + 1 - Ω) = Ω * (1 + z) ^ 3 + 1 - Ω :=
    Real.mul_self_sqrt hy.le
  show -1 + (1 + z) * (Ω * (3 * (1 + z) ^ 2) / (2 * √(Ω * (1 + z) ^ 3 + 1 - Ω)))
      / √(Ω * (1 + z) ^ 3 + 1 - Ω) = _
  have gen : ∀ r : ℝ, 0 < r → r * r = Ω * (1 + z) ^ 3 + 1 - Ω →
      -1 + (1 + z) * (Ω * (3 * (1 + z) ^ 2) / (2 * r)) / r
        = -1 + 3 * Ω * (1 + z) ^ 3 / (2 * (Ω * (1 + z) ^ 3 + 1 - Ω)) := by
    intro r hr hrr
    rw [← hrr]
    field_simp
  exact gen _ hs hss

theorem decel_sign {Ω z : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hz : 0 ≤ 1 + z) :
    (Blind.FR13.decel Ω z < 0 ↔ Ω * (1 + z) ^ 3 < 2 * (1 - Ω)) ∧
    (0 < Blind.FR13.decel Ω z ↔ 2 * (1 - Ω) < Ω * (1 + z) ^ 3) ∧
    (Blind.FR13.decel Ω z = 0 ↔ Ω * (1 + z) ^ 3 = 2 * (1 - Ω)) := by
  have hy : 0 < Ω * (1 + z) ^ 3 + 1 - Ω := by
    have : 0 ≤ Ω * (1 + z) ^ 3 := mul_nonneg h0.le (pow_nonneg hz 3)
    linarith
  rw [decel_eq h0 h1 hz]
  have key : -1 + 3 * Ω * (1 + z) ^ 3 / (2 * (Ω * (1 + z) ^ 3 + 1 - Ω))
      = (Ω * (1 + z) ^ 3 - 2 * (1 - Ω)) / (2 * (Ω * (1 + z) ^ 3 + 1 - Ω)) := by
    field_simp; ring
  rw [key]
  have hd : 0 < 2 * (Ω * (1 + z) ^ 3 + 1 - Ω) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [div_neg_iff]; constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · linarith
    · intro h; right; exact ⟨by linarith, hd⟩
  · rw [div_pos_iff]; constructor
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · linarith
      · linarith
    · intro h; left; exact ⟨by linarith, hd⟩
  · rw [div_eq_zero_iff]; constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; left; linarith

/-- The blind restater's `zda_spec`. -/
theorem blind_zda_spec (Ωm : ℝ) (h0 : 0 < Ωm) (h1 : Ωm < 2 / 3) :
    0 < Blind.FR13.zda Ωm ∧ Blind.FR13.decel Ωm (Blind.FR13.zda Ωm) = 0 ∧
    (∀ z, 0 ≤ z → z < Blind.FR13.zda Ωm → Blind.FR13.decel Ωm z < 0) ∧
    (∀ z, Blind.FR13.zda Ωm < z → 0 < Blind.FR13.decel Ωm z) := by
  have h1' : Ωm < 1 := by linarith
  obtain ⟨hc, hp⟩ := zda_cube h0 h1'
  set w := Blind.FR13.zda Ωm with hw
  have hw0 : 0 < w := by
    by_contra h; rw [not_lt] at h
    have : (1 + w) ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hp.le (by linarith) 3
    nlinarith
  refine ⟨hw0, (decel_sign h0 h1' hp.le).2.2.2 (by linarith), ?_, ?_⟩
  · intro z hz hzw
    have hz1 : 0 ≤ 1 + z := by linarith
    refine (decel_sign h0 h1' hz1).1.2 ?_
    have : (1 + z) ^ 3 < (1 + w) ^ 3 := pow_lt_pow_left₀ (by linarith) hz1 (by norm_num)
    nlinarith
  · intro z hzw
    have hz1 : 0 ≤ 1 + z := by linarith
    refine (decel_sign h0 h1' hz1).2.1.2 ?_
    have : (1 + w) ^ 3 < (1 + z) ^ 3 := pow_lt_pow_left₀ (by linarith) hp.le (by norm_num)
    nlinarith

end Work.Data.FR13Audit
