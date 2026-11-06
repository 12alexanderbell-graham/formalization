import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Gelfand problem, `GFinal`: assembly: the energy p²/2 + Λ − 2 log Λ (p = 2 + s w', Λ = s² exp w) is non-increasing, so the first maximum of Λ is its maximum over the whole interval. Promoted from `Work/Math/GFinal.lean`. -/

namespace Checked.Math.GFinal
open Set

/-- f(x) − f(y) ≥ (x − y)(1 − 2/y) for f(x) = x − 2 log x, x, y > 0. -/
theorem f_sub_ge {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x - y) * (1 - 2 / y) ≤ (x - 2 * Real.log x) - (y - 2 * Real.log y) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at h
  have e : (x - y) * (1 - 2 / y) = (x - y) - 2 * (x / y - 1) := by
    field_simp
  rw [e]
  linarith

theorem derivs_at {S : ℝ} {w φ : ℝ → ℝ}
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    {s : ℝ} (hs : s ∈ Ioo 0 S) :
    HasDerivAt w (φ s) s ∧ HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s :=
  ⟨(hw s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2),
    (hφ s ⟨hs.1, hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)⟩

theorem hasDerivAt_Lam {w φ : ℝ → ℝ} {s : ℝ} (hw : HasDerivAt w (φ s) s) :
    HasDerivAt (fun t => t ^ 2 * Real.exp (w t))
      (s * Real.exp (w s) * (2 + s * φ s)) s := by
  have h := (hasDerivAt_pow 2 s).mul hw.exp
  convert h using 1
  push_cast
  ring

theorem hasDerivAt_p {w φ : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0)
    (hφ : HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s) :
    HasDerivAt (fun t => 2 + t * φ t) (-(φ s + s * Real.exp (w s))) s := by
  have h := ((hasDerivAt_id' s).mul hφ).const_add 2
  convert h using 1
  field_simp
  ring

theorem en_deriv_eq {s E P φs : ℝ} (hs : s ≠ 0) (hE : E ≠ 0) (hP : P = 2 + s * φs) :
    2 * P * (-(φs + s * E)) / 2 + s * E * P - 2 * (s * E * P / (s ^ 2 * E)) =
      -(P ^ 2 / s) := by
  subst hP
  field_simp
  ring

theorem hasDerivAt_En {w φ : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0)
    (hw : HasDerivAt w (φ s) s)
    (hφ : HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s) :
    HasDerivAt (fun t => (2 + t * φ t) ^ 2 / 2 + t ^ 2 * Real.exp (w t) -
        2 * Real.log (t ^ 2 * Real.exp (w t)))
      (-((2 + s * φ s) ^ 2 / s)) s := by
  have hL := hasDerivAt_Lam hw
  have hp := hasDerivAt_p hs hφ
  have hne : s ^ 2 * Real.exp (w s) ≠ 0 := by positivity
  have h := (((hp.pow 2).div_const 2).add hL).sub ((hL.log hne).const_mul 2)
  convert h using 1
  rw [← en_deriv_eq hs (Real.exp_pos (w s)).ne' rfl]
  push_cast
  ring

/-- Assembly of the Gelfand headline from certificate facts. -/
theorem assemble (S a b L1 L2 Pa lo hi : ℝ) (w φ : ℝ → ℝ)
    (ha0 : 0 < a) (hab : a < b) (hbS : b ≤ S)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (hpos : ∀ s ∈ Ioc (0 : ℝ) a, 0 < 2 + s * φ s)
    (hdec : ∀ s ∈ Icc a b, 0 < φ s + s * Real.exp (w s))
    (hb : 2 + b * φ b < 0)
    (hA1 : L1 ≤ a ^ 2 * Real.exp (w a)) (hA2 : a ^ 2 * Real.exp (w a) ≤ L2)
    (hpa : |2 + a * φ a| ≤ Pa)
    (h2 : 2 < L1) (hlo : lo ≤ L1) (hhi : L2 + Pa ^ 2 / (2 * (1 - 2 / L1)) ≤ hi) :
    ∃ s₁ : ℝ, a ≤ s₁ ∧ s₁ ≤ b ∧
      (∀ s ∈ Icc 0 S, s ^ 2 * Real.exp (w s) ≤ s₁ ^ 2 * Real.exp (w s₁)) ∧
      lo ≤ s₁ ^ 2 * Real.exp (w s₁) ∧ s₁ ^ 2 * Real.exp (w s₁) ≤ hi := by
  set p : ℝ → ℝ := fun t => 2 + t * φ t with hpdef
  set Λ : ℝ → ℝ := fun t => t ^ 2 * Real.exp (w t) with hΛdef
  set En : ℝ → ℝ := fun t => (2 + t * φ t) ^ 2 / 2 + t ^ 2 * Real.exp (w t) -
      2 * Real.log (t ^ 2 * Real.exp (w t)) with hEndef
  have hS0 : 0 < S := ha0.trans (hab.trans_le hbS)
  -- continuity
  have wc : ContinuousOn w (Icc 0 S) := fun x hx => (hw x hx).continuousWithinAt
  have φc : ∀ c, 0 < c → ContinuousOn φ (Icc c S) := fun c hc x hx =>
    ((hφ x ⟨hc.trans_le hx.1, hx.2⟩).continuousWithinAt).mono
      (Icc_subset_Icc hc.le le_rfl)
  have Λc : ∀ c d, 0 ≤ c → d ≤ S → ContinuousOn Λ (Icc c d) := fun c d hc hd =>
    (continuousOn_id.pow 2).mul
      ((wc.mono (Icc_subset_Icc hc hd)).rexp)
  have pc : ∀ c d, 0 < c → d ≤ S → ContinuousOn p (Icc c d) := fun c d hc hd =>
    continuousOn_const.add (continuousOn_id.mul ((φc c hc).mono (Icc_subset_Icc le_rfl hd)))
  have Λpos : ∀ t, 0 < t → 0 < Λ t := fun t ht => by simp only [hΛdef]; positivity
  -- p strictly decreasing on [a, b]
  have panti : StrictAntiOn p (Icc a b) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a b) (pc a b ha0 hbS)
      (f' := fun s => -(φ s + s * Real.exp (w s)))
    · intro x hx
      rw [interior_Icc] at hx
      have hxS : x ∈ Ioo 0 S := ⟨ha0.trans hx.1, hx.2.trans_le hbS⟩
      exact (hasDerivAt_p hxS.1.ne' (derivs_at hw hφ hxS).2).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have := hdec x ⟨hx.1.le, hx.2.le⟩
      linarith
  -- the zero s₁
  have hpa0 : 0 < p a := hpos a ⟨ha0, le_rfl⟩
  obtain ⟨s₁, hs₁, hz⟩ : ∃ s₁ ∈ Icc a b, p s₁ = 0 :=
    intermediate_value_Icc' hab.le (pc a b ha0 hbS) ⟨hb.le, hpa0.le⟩
  have hs₁0 : 0 < s₁ := ha0.trans_le hs₁.1
  have hs₁S : s₁ ≤ S := hs₁.2.trans hbS
  -- p > 0 on (0, s₁)
  have ppos : ∀ x ∈ Ioo 0 s₁, 0 < p x := by
    intro x hx
    rcases le_or_gt x a with hxa | hxa
    · exact hpos x ⟨hx.1, hxa⟩
    · have := panti ⟨hxa.le, hx.2.le.trans hs₁.2⟩ hs₁ hx.2
      rw [hz] at this
      exact this
  -- Λ monotone on [0, s₁]
  have Λmono : MonotoneOn Λ (Icc 0 s₁) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s₁) (Λc 0 s₁ le_rfl hs₁S)
      (f' := fun s => s * Real.exp (w s) * (2 + s * φ s))
    · intro x hx
      rw [interior_Icc] at hx
      have hxS : x ∈ Ioo 0 S := ⟨hx.1, hx.2.trans_le hs₁S⟩
      exact (hasDerivAt_Lam (derivs_at hw hφ hxS).1).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have := ppos x hx
      have : 0 < x * Real.exp (w x) := mul_pos hx.1 (Real.exp_pos _)
      positivity
  -- energy antitone on [a, S]
  have Enanti : AntitoneOn En (Icc a S) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a S)
      (f' := fun s => -((2 + s * φ s) ^ 2 / s))
    · have h1 : ContinuousOn Λ (Icc a S) := Λc a S ha0.le le_rfl
      have h2 : ContinuousOn (fun t => Real.log (Λ t)) (Icc a S) :=
        h1.log fun x hx => (Λpos x (ha0.trans_le hx.1)).ne'
      have h3 := ((pc a S ha0 le_rfl).pow 2).div_const 2
      exact (h3.add h1).sub (h2.const_smul (2 : ℝ))
    · intro x hx
      rw [interior_Icc] at hx
      have hxS : x ∈ Ioo 0 S := ⟨ha0.trans hx.1, hx.2⟩
      obtain ⟨d1, d2⟩ := derivs_at hw hφ hxS
      exact (hasDerivAt_En hxS.1.ne' d1 d2).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := ha0.trans hx.1
      have : 0 ≤ (2 + x * φ x) ^ 2 / x := by positivity
      linarith
  -- values
  have hEn : ∀ t, En t = p t ^ 2 / 2 + (Λ t - 2 * Real.log (Λ t)) := fun t => by
    simp only [hEndef, hpdef, hΛdef]; ring
  have hΛa1 : Λ a ≤ Λ s₁ := Λmono ⟨ha0.le, hs₁.1⟩ ⟨hs₁0.le, le_rfl⟩ hs₁.1
  have hL1a : L1 ≤ Λ a := hA1
  have hΛ1gt : 2 < Λ s₁ := by linarith
  have hfac : 0 < 1 - 2 / Λ s₁ := by
    have : 2 / Λ s₁ < 1 := (div_lt_one (by linarith)).2 hΛ1gt
    linarith
  refine ⟨s₁, hs₁.1, hs₁.2, ?_, ?_, ?_⟩
  · intro s hs
    show Λ s ≤ Λ s₁
    rcases le_or_gt s s₁ with hss | hss
    · exact Λmono ⟨hs.1, hss⟩ ⟨hs₁0.le, le_rfl⟩ hss
    · have hEs := Enanti ⟨hs₁.1, hs₁S⟩ ⟨hs₁.1.trans hss.le, hs.2⟩ hss.le
      rw [hEn, hEn, hz] at hEs
      have hfs := f_sub_ge (Λpos s (hs₁0.trans hss)) (Λpos s₁ hs₁0)
      have hsq : 0 ≤ p s ^ 2 / 2 := by positivity
      have hneg : (Λ s - Λ s₁) * (1 - 2 / Λ s₁) ≤ 0 := by
        have : (0 : ℝ) ^ 2 / 2 = 0 := by norm_num
        linarith
      by_contra hcon
      have : 0 < (Λ s - Λ s₁) * (1 - 2 / Λ s₁) := mul_pos (by linarith) hfac
      linarith
  · show lo ≤ Λ s₁
    linarith
  · show Λ s₁ ≤ hi
    have hEs := Enanti ⟨le_rfl, hab.le.trans hbS⟩
      ⟨hs₁.1, hs₁S⟩ hs₁.1
    rw [hEn, hEn, hz] at hEs
    have hΛa0 : 0 < Λ a := Λpos a ha0
    have hfs := f_sub_ge (Λpos s₁ hs₁0) hΛa0
    have hpa2 : p a ^ 2 ≤ Pa ^ 2 := by
      have := sq_le_sq' (abs_le.1 hpa).1 (abs_le.1 hpa).2
      exact this
    have hk : (Λ s₁ - Λ a) * (1 - 2 / Λ a) ≤ Pa ^ 2 / 2 := by
      have : (0 : ℝ) ^ 2 / 2 = 0 := by norm_num
      linarith
    have hL1pos : 0 < L1 := by linarith
    have hc1 : 0 < 1 - 2 / L1 := by
      have : 2 / L1 < 1 := (div_lt_one hL1pos).2 h2
      linarith
    have hc2 : 1 - 2 / L1 ≤ 1 - 2 / Λ a := by
      have : 2 / Λ a ≤ 2 / L1 := div_le_div_of_nonneg_left (by norm_num) hL1pos hL1a
      linarith
    have hd0 : 0 ≤ Λ s₁ - Λ a := by linarith
    have hk2 : (Λ s₁ - Λ a) * (1 - 2 / L1) ≤ Pa ^ 2 / 2 :=
      (mul_le_mul_of_nonneg_left hc2 hd0).trans hk
    have hk3 : Λ s₁ - Λ a ≤ Pa ^ 2 / (2 * (1 - 2 / L1)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have : Λ a ≤ L2 := hA2
    linarith

end Checked.Math.GFinal
