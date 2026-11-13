import Mathlib

/-! Scratch (run 2026-11-13T0228Z, part 1): the linear shear equation q' = −k f q + s solved by an integrating
factor, for explicit profiles f, p (f' = p) that are not tied to q by p' = q. -/

namespace Scratch.ProfileU
open Set Filter Topology intervalIntegral

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

end Scratch.ProfileU
