import Checked.Trust.NonVacuity
import Checked.Trust.NecessityQ
import Checked.FalknerSkan.MonotoneWindow
import Checked.FalknerSkan.NegWindow
import Checked.FalknerSkan.NegReversed
import Checked.FalknerSkan.Limit
import Checked.Hiemenz.Hiemenz

/-! Hypothesis necessity by explicit profiles in which the velocity is not the derivative of the shear: the shear solves its own linear equation by an integrating factor, so every other hypothesis holds with a wall shear outside the window (monotone-class Hiemenz and Homann windows, the adverse-gradient monotone bound); and, for the positivity theorem under a positive pressure gradient, the reversed-flow solution (a negative coefficient), the Hiemenz solution changed off the half-line (a negative height), and two profiles with zero wall shear. Module `NecessityT`. -/

namespace Checked.Trust.NCT

open Set Filter Topology intervalIntegral

/-! Profile with an overshooting velocity (positive pressure gradient). -/


noncomputable def fT (η : ℝ) : ℝ := η + 1 - (2 * η + 1) * Real.exp (-η)
noncomputable def pT (η : ℝ) : ℝ := 1 - (1 - 2 * η) * Real.exp (-η)

theorem fT_deriv (η : ℝ) : HasDerivAt fT (pT η) η := by
  have he : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-η)) η := by
    simpa using (hasDerivAt_neg η).exp
  have h := (((hasDerivAt_id η).add_const 1).sub
    ((((hasDerivAt_id η).const_mul 2).add_const 1).mul he))
  unfold fT pT
  convert h using 1
  · ext x; simp
  · simp; ring

theorem fT_cont : Continuous fT := by unfold fT; fun_prop
theorem pT_cont : Continuous pT := by unfold pT; fun_prop

theorem fT_zero : fT 0 = 0 := by simp [fT]
theorem pT_zero : pT 0 = 0 := by simp [pT]

theorem pT_lim : Tendsto pT atTop (𝓝 1) := by
  have h1 : Tendsto (fun η : ℝ => Real.exp (-η)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun η : ℝ => η * Real.exp (-η)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h3 : Tendsto (fun η : ℝ => 1 - (Real.exp (-η) - 2 * (η * Real.exp (-η)))) atTop (𝓝 (1 - (0 - 2 * 0))) :=
    tendsto_const_nhds.sub (h1.sub (h2.const_mul 2))
  simp only [mul_zero, sub_zero] at h3
  refine h3.congr (fun η => ?_)
  unfold pT; ring

theorem pT_ge_one {η : ℝ} (h : 1 / 2 ≤ η) : 1 ≤ pT η := by
  unfold pT
  have : (1 - 2 * η) * Real.exp (-η) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
  linarith

/-- G = ∫₀^η f. -/
noncomputable def GT (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, fT s

theorem GT_deriv (η : ℝ) : HasDerivAt GT (fT η) η :=
  (fT_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem GT_cont : Continuous GT := continuous_iff_continuousAt.2 fun η => (GT_deriv η).continuousAt

/-- The integrand e^{kG}(p² − 1). -/
noncomputable def rT (k s : ℝ) : ℝ := Real.exp (k * GT s) * (pT s ^ 2 - 1)

theorem rT_cont (k : ℝ) : Continuous (rT k) := by
  unfold rT; have := GT_cont; have := pT_cont; fun_prop

/-- The wall value: 2 plus ∫₀^{1/2} e^{kG}. -/
noncomputable def q0T (k : ℝ) : ℝ := 2 + ∫ s in (0 : ℝ)..(1 / 2), Real.exp (k * GT s)

noncomputable def qT (k η : ℝ) : ℝ := Real.exp (-(k * GT η)) * (q0T k + ∫ s in (0 : ℝ)..η, rT k s)

theorem qT_deriv (k η : ℝ) : HasDerivAt (qT k) (-(k * fT η * qT k η) - 1 + pT η ^ 2) η := by
  have hI : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, rT k s) (rT k η) η :=
    ((rT_cont k).integral_hasStrictDerivAt 0 η).hasDerivAt
  have hE : HasDerivAt (fun u => Real.exp (-(k * GT u))) (Real.exp (-(k * GT η)) * (-(k * fT η))) η :=
    ((GT_deriv η).const_mul k).neg.exp
  have h := hE.mul (hI.const_add (q0T k))
  unfold qT
  convert h using 1
  unfold rT
  have : Real.exp (-(k * GT η)) * Real.exp (k * GT η) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (1 - pT η ^ 2) * this

theorem expG_int (k : ℝ) (a b : ℝ) : IntervalIntegrable (fun s => Real.exp (k * GT s)) MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable; have := GT_cont; fun_prop

/-- The bracket stays at least 2. -/
theorem bracket_ge (k η : ℝ) (hη : 0 ≤ η) : 2 ≤ q0T k + ∫ s in (0 : ℝ)..η, rT k s := by
  have hlow : ∀ s, -Real.exp (k * GT s) ≤ rT k s := fun s => by
    unfold rT
    have := Real.exp_pos (k * GT s)
    nlinarith [sq_nonneg (pT s)]
  have hpos : ∀ s, 0 ≤ Real.exp (k * GT s) := fun s => (Real.exp_pos _).le
  unfold q0T
  rcases le_or_gt η (1 / 2) with h | h
  · -- ∫₀^η r ≥ −∫₀^η e^{kG} ≥ −∫₀^{1/2} e^{kG}
    have i1 : ∫ s in (0 : ℝ)..η, -Real.exp (k * GT s) ≤ ∫ s in (0 : ℝ)..η, rT k s :=
      intervalIntegral.integral_mono_on hη ((expG_int k 0 η).neg) ((rT_cont k).intervalIntegrable 0 η)
        (fun s _ => hlow s)
    have i2 : ∫ s in (0 : ℝ)..η, Real.exp (k * GT s) ≤ ∫ s in (0 : ℝ)..(1 / 2), Real.exp (k * GT s) := by
      have := intervalIntegral.integral_interval_sub_left (expG_int k 0 (1 / 2)) (expG_int k 0 η)
      have h3 : 0 ≤ ∫ s in η..(1 / 2), Real.exp (k * GT s) :=
        intervalIntegral.integral_nonneg h (fun s _ => hpos s)
      linarith
    rw [intervalIntegral.integral_neg] at i1
    linarith
  · have split := intervalIntegral.integral_add_adjacent_intervals
      ((rT_cont k).intervalIntegrable (μ := MeasureTheory.volume) 0 (1 / 2))
      ((rT_cont k).intervalIntegrable (μ := MeasureTheory.volume) (1 / 2) η)
    have i1 : ∫ s in (0 : ℝ)..(1 / 2), -Real.exp (k * GT s) ≤ ∫ s in (0 : ℝ)..(1 / 2), rT k s :=
      intervalIntegral.integral_mono_on (by norm_num) ((expG_int k 0 (1 / 2)).neg)
        ((rT_cont k).intervalIntegrable 0 (1 / 2)) (fun s _ => hlow s)
    have i2 : 0 ≤ ∫ s in (1 / 2 : ℝ)..η, rT k s := by
      apply intervalIntegral.integral_nonneg h.le
      intro s hs
      unfold rT
      have h1 := pT_ge_one hs.1
      exact mul_nonneg (hpos s) (by nlinarith)
    rw [intervalIntegral.integral_neg] at i1
    linarith

theorem qT_pos (k η : ℝ) (hη : 0 ≤ η) : 0 < qT k η := by
  unfold qT
  exact mul_pos (Real.exp_pos _) (by linarith [bracket_ge k η hη])

theorem qT_zero_ge (k : ℝ) : 2 ≤ qT k 0 := by
  have := bracket_ge k 0 le_rfl
  unfold qT; simp [GT] at this ⊢; linarith


/-! Profile with velocity 1 − e^{−η} (adverse gradient, or zero wall shear). -/


/-- Velocity 1 − e^{−η} and its stream function. -/
noncomputable def fU (η : ℝ) : ℝ := η - 1 + Real.exp (-η)
noncomputable def pU (η : ℝ) : ℝ := 1 - Real.exp (-η)

theorem fU_deriv (η : ℝ) : HasDerivAt fU (pU η) η := by
  have he : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-η)) η := by
    simpa using (hasDerivAt_neg η).exp
  have h := ((hasDerivAt_id η).sub_const 1).add he
  unfold fU pU
  convert h using 1
  · ext x; simp

theorem fU_cont : Continuous fU := by unfold fU; fun_prop
theorem pU_cont : Continuous pU := by unfold pU; fun_prop
theorem fU_zero : fU 0 = 0 := by simp [fU]
theorem pU_zero : pU 0 = 0 := by simp [pU]

theorem pU_lim : Tendsto pU atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub Real.tendsto_exp_neg_atTop_nhds_zero
  simp only [sub_zero] at h
  exact h

theorem pU_sq_le {η : ℝ} (hη : 0 ≤ η) : pU η ^ 2 ≤ 1 := by
  unfold pU
  have h1 : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : 0 < Real.exp (-η) := Real.exp_pos _
  nlinarith

/-- G = ∫₀^η f. -/
noncomputable def GU (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, fU s

theorem GU_deriv (η : ℝ) : HasDerivAt GU (fU η) η :=
  (fU_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem GU_cont : Continuous GU := continuous_iff_continuousAt.2 fun η => (GU_deriv η).continuousAt

/-- Solution of q' = −k f q + s with q(0) = q0 (integrating factor e^{kG}). -/
noncomputable def linQ (k : ℝ) (s : ℝ → ℝ) (q0 η : ℝ) : ℝ :=
  Real.exp (-(k * GU η)) * (q0 + ∫ x in (0 : ℝ)..η, Real.exp (k * GU x) * s x)

theorem linQ_deriv (k : ℝ) {s : ℝ → ℝ} (hs : Continuous s) (q0 η : ℝ) :
    HasDerivAt (linQ k s q0) (-(k * fU η * linQ k s q0 η) + s η) η := by
  have hc : Continuous (fun x => Real.exp (k * GU x) * s x) := by have := GU_cont; fun_prop
  have hI := (hc.integral_hasStrictDerivAt 0 η).hasDerivAt
  have hE : HasDerivAt (fun u => Real.exp (-(k * GU u))) (Real.exp (-(k * GU η)) * (-(k * fU η))) η :=
    ((GU_deriv η).const_mul k).neg.exp
  have h := hE.mul (hI.const_add q0)
  unfold linQ
  convert h using 1
  have : Real.exp (-(k * GU η)) * Real.exp (k * GU η) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-s η) * this

theorem linQ_zero (k : ℝ) (s : ℝ → ℝ) (q0 : ℝ) : linQ k s q0 0 = q0 := by
  simp [linQ, GU]

theorem linQ_pos (k : ℝ) {s : ℝ → ℝ} (hs0 : ∀ x, 0 ≤ x → 0 ≤ s x) {q0 : ℝ}
    (hq0 : 0 < q0) {η : ℝ} (hη : 0 ≤ η) : 0 < linQ k s q0 η := by
  unfold linQ
  apply mul_pos (Real.exp_pos _)
  have : 0 ≤ ∫ x in (0 : ℝ)..η, Real.exp (k * GU x) * s x :=
    intervalIntegral.integral_nonneg hη (fun x hx => mul_nonneg (Real.exp_pos _).le (hs0 x hx.1))
  linarith

/-- The adverse-gradient forcing (1 − p²)/10 is continuous and nonnegative on [0, ∞). -/
theorem sTenth_cont : Continuous (fun x => (1 - pU x ^ 2) / 10) := by have := pU_cont; fun_prop
theorem sTenth_nonneg : ∀ x, 0 ≤ x → 0 ≤ (1 - pU x ^ 2) / 10 := fun x hx => by
  have := pU_sq_le hx; linarith

/-- Forcing −(1 − p²). -/
theorem sOne_cont : Continuous (fun x => -(1 - pU x ^ 2)) := by have := pU_cont; fun_prop


/-- `p' = q` is needed in `hiemenz_monotone_window`. -/
theorem hiemenz_monotone_window_h2 :
    necessity% Checked.FalknerSkan.MonotoneWindow.hiemenz_monotone_window 2 := by
  refine ⟨fT, pT, qT 1, fun η _ => (fT_deriv η).hasDerivWithinAt,
    fun η _ => (qT_deriv 1 η).hasDerivWithinAt.congr_deriv (by ring), fT_zero, pT_zero, pT_lim,
    fun η hη => qT_pos 1 η hη, ?_⟩
  have := qT_zero_ge 1
  rintro ⟨-, h⟩; norm_num at h; linarith

/-- `p' = q` is needed in `homann_monotone_window`. -/
theorem homann_monotone_window_h2 :
    necessity% Checked.FalknerSkan.MonotoneWindow.homann_monotone_window 2 := by
  refine ⟨fT, pT, qT 2, fun η _ => (fT_deriv η).hasDerivWithinAt,
    fun η _ => (qT_deriv 2 η).hasDerivWithinAt.congr_deriv (by ring), fT_zero, pT_zero, pT_lim,
    fun η hη => qT_pos 2 η hη, ?_⟩
  have := qT_zero_ge 2
  rintro ⟨-, h⟩; norm_num at h; linarith

/-- `f' = p` is needed in `fs_neg_tenth_monotone_lt` (the profile of `NecessityQ`, wall shear one). -/
theorem fs_neg_tenth_monotone_lt_h1 :
    necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt 1 := by
  refine ⟨NCQ.F1 (-1 / 10), NCQ.P1 (-1 / 10), NCQ.Q1 (-1 / 10), NCQ.hp1 _, NCQ.hq1 _ (by norm_num),
    NCQ.F1_zero _, NCQ.P1_zero _, NCQ.P1_lim _ (by norm_num), NCQ.Q1_pos _ (by norm_num), ?_⟩
  rw [NCQ.Q1_zero]; norm_num

/-- `p' = q` is needed in `fs_neg_tenth_monotone_lt`. -/
theorem fs_neg_tenth_monotone_lt_h2 :
    necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt 2 := by
  refine ⟨fU, pU, linQ 1 (fun x => (1 - pU x ^ 2) / 10) 1, fun η _ => (fU_deriv η).hasDerivWithinAt,
    fun η _ => (linQ_deriv 1 sTenth_cont 1 η).hasDerivWithinAt.congr_deriv (by ring), fU_zero, pU_zero,
    pU_lim, fun η hη => linQ_pos 1 sTenth_nonneg one_pos hη, ?_⟩
  rw [linQ_zero]; norm_num

/-- The Falkner–Skan equation is needed in `fs_neg_tenth_monotone_lt` (the profile of `NecessityQ`, wall shear one half). -/
theorem fs_neg_tenth_monotone_lt_h3 :
    necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt 3 := by
  refine ⟨NCQ.F, NCQ.P, NCQ.Q, NCQ.hf_w, NCQ.hp_w, NCQ.F_zero, NCQ.P_zero, NCQ.P_lim, NCQ.Q_pos, ?_⟩
  rw [NCQ.Q_zero]; norm_num

/-- Velocity 1 − (1 + η) e^{−η}: zero wall shear. -/
noncomputable def fV (η : ℝ) : ℝ := η - 2 + (2 + η) * Real.exp (-η)
noncomputable def pV (η : ℝ) : ℝ := 1 - (1 + η) * Real.exp (-η)
noncomputable def qV (η : ℝ) : ℝ := η * Real.exp (-η)

theorem fV_deriv (η : ℝ) : HasDerivAt fV (pV η) η := by
  have he : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-η)) η := by
    simpa using (hasDerivAt_neg η).exp
  have h := ((hasDerivAt_id η).sub_const 2).add (((hasDerivAt_id η).const_add 2).mul he)
  unfold fV pV
  convert h using 1
  · ext x; simp
  · simp; ring

theorem pV_deriv (η : ℝ) : HasDerivAt pV (qV η) η := by
  have he : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-η)) η := by
    simpa using (hasDerivAt_neg η).exp
  have h := (hasDerivAt_const η (1 : ℝ)).sub (((hasDerivAt_id η).const_add 1).mul he)
  unfold pV qV
  convert h using 1
  · ext x; simp
  · simp; ring

theorem pV_lim : Tendsto pV atTop (𝓝 1) := by
  have h1 : Tendsto (fun η : ℝ => Real.exp (-η)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun η : ℝ => η * Real.exp (-η)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub (h1.add h2)
  simp only [add_zero, sub_zero] at h3
  exact h3.congr (fun η => by unfold pV; ring)

/-- The equation is needed in `fs_monotone_of_limit`: a profile with zero wall shear. -/
theorem fs_monotone_of_limit_h5 : necessity% Checked.FalknerSkan.Limit.fs_monotone_of_limit 5 := by
  refine ⟨1, fV, pV, qV, 0, by norm_num, le_rfl, fun η _ => (fV_deriv η).hasDerivWithinAt,
    fun η _ => (pV_deriv η).hasDerivWithinAt, by simp [fV], by simp [pV], pV_lim, mem_Ici.2 le_rfl, ?_⟩
  simp [qV]

/-- `p' = q` is needed in `fs_monotone_of_limit`: the shear from its linear equation with zero wall value. -/
theorem fs_monotone_of_limit_h4 : necessity% Checked.FalknerSkan.Limit.fs_monotone_of_limit 4 := by
  refine ⟨1, fU, pU, linQ 1 (fun x => -(1 - pU x ^ 2)) 0, 0, by norm_num, le_rfl,
    fun η _ => (fU_deriv η).hasDerivWithinAt,
    fun η _ => (linQ_deriv 1 sOne_cont 0 η).hasDerivWithinAt.congr_deriv (by ring), fU_zero, pU_zero,
    pU_lim, mem_Ici.2 le_rfl, ?_⟩
  rw [linQ_zero]; exact lt_irrefl 0

/-- `0 < β` is needed in `fs_monotone_of_limit`: the reversed-flow solution at β = −1/10 has negative wall shear. -/
theorem fs_monotone_of_limit_h1 : necessity% Checked.FalknerSkan.Limit.fs_monotone_of_limit 1 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hl, -, -, -, hhi⟩ := Checked.FalknerSkan.NegReversed.fs_neg_tenth_reversed
  refine ⟨-1 / 10, f, p, q, 0, by norm_num, hf, hp, hq, hf0, hp0, hl, mem_Ici.2 le_rfl, ?_⟩
  norm_num at hhi; intro h; linarith

/-- `η ∈ Ici 0` is needed in `fs_monotone_of_limit`: the Hiemenz solution with its shear set to zero at negative heights. -/
theorem fs_monotone_of_limit_h9 : necessity% Checked.FalknerSkan.Limit.fs_monotone_of_limit 9 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hl, -, -⟩ := Checked.Hiemenz.hiemenz_exists
  have e : ∀ η ∈ Ici (0 : ℝ), (if η < 0 then 0 else q η) = q η :=
    fun η hη => by simp [not_lt.mpr (mem_Ici.mp hη)]
  refine ⟨1, f, p, fun η => if η < 0 then 0 else q η, -1, by norm_num, le_rfl, hf,
    fun η hη => (hp η hη).congr_deriv (e η hη).symm,
    fun η hη => ((hq η hη).congr (fun y hy => e y hy) (e η hη)).congr_deriv (by rw [e η hη]; ring),
    hf0, hp0, hl, ?_⟩
  simp

end Checked.Trust.NCT
