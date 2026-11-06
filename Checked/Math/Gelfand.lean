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
import Checked.Math.GChain
import Checked.Math.GFinal
import Checked.Math.GHelp

/-! Gelfand problem, `Gelfand`: the critical parameter of the Gelfand problem in the three-dimensional ball (radial branch): the maximum of s² exp w(s) over the solution's whole interval, attained near the first zero of 2 + s w'; bounds as printed in the statement of `gelfand_ball_critical`. Promoted from `Work/Math/Gelfand.lean`. -/

namespace Checked.Math.Gelfand
open Set

/-- Gelfand problem in the three-dimensional ball, radial branch: for every S ≥ 41/10 and every
solution w of w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with
derivative φ and φ continuous at 0, there is a point s₁ between 4.071496844 and 4.071496845 at which
s² e^{w(s)} attains its maximum over [0, S], and that maximum lies between 3.321992118 and
3.321992119. -/
theorem gelfand_ball_critical (S : ℝ) (hS : 41 / 10 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ s₁ : ℝ, 4.071496844 ≤ s₁ ∧ s₁ ≤ 4.071496845 ∧
      (∀ s ∈ Icc 0 S, s ^ 2 * Real.exp (w s) ≤ s₁ ^ 2 * Real.exp (w s₁)) ∧
      3.321992118 ≤ s₁ ^ 2 * Real.exp (w s₁) ∧ s₁ ^ 2 * Real.exp (w s₁) ≤ 3.321992119 := by
  have hsub : Icc (0 : ℝ) (41 / 10) ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hp3, hdec, hEA, hφA, hφB⟩ := Checked.Math.GCerts.chain (w := w) (φ := φ)
    (fun s hs => (hw s (hsub hs)).mono hsub) (hφ0.mono hsub)
    (fun s hs => (hφ s ⟨hs.1, hs.2.trans hS⟩).mono hsub) h0
  rw [abs_le] at hEA hφA hφB
  have hA : (0 : ℝ) < (1017874211/250000000 : ℝ) := by norm_num
  have hpa : 0 < 2 + (1017874211/250000000 : ℝ) * φ (1017874211/250000000 : ℝ) := by
    have h1 : (1017874211/250000000 : ℝ) * ((-3070123956454913517/6250000000000000000 : ℝ) - (31316544345759/10000000000000000000000000 : ℝ)) ≤ (1017874211/250000000 : ℝ) * φ (1017874211/250000000 : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith [hφA.1]) hA.le
    have n : (0 : ℝ) < 2 + (1017874211/250000000 : ℝ) * ((-3070123956454913517/6250000000000000000 : ℝ) - (31316544345759/10000000000000000000000000 : ℝ)) := by norm_num
    linarith
  have hpos := Checked.Math.GHelp.pos_extend (S := S) (c := 3) (a := (1017874211/250000000 : ℝ)) (b := (814299369/200000000 : ℝ)) (w := w)
    (φ := φ) (by norm_num) (by norm_num) (by norm_num) (by linarith) hw hφ hp3 hdec hpa
  have hb : 2 + (814299369/200000000 : ℝ) * φ (814299369/200000000 : ℝ) < 0 := by
    have h1 : (814299369/200000000 : ℝ) * φ (814299369/200000000 : ℝ) ≤ (814299369/200000000 : ℝ) * ((-24560991649594292929/50000000000000000000 : ℝ) + (156582722125403/50000000000000000000000000 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [hφB.2]) (by norm_num)
    have n : 2 + (814299369/200000000 : ℝ) * ((-24560991649594292929/50000000000000000000 : ℝ) + (156582722125403/50000000000000000000000000 : ℝ)) < (0 : ℝ) := by norm_num
    linarith
  have hA1 : (2076245073929943934651518165389984298011561/625000000000000000000000000000000000000000 : ℝ) ≤ (1017874211/250000000 : ℝ) ^ 2 * Real.exp (w (1017874211/250000000 : ℝ)) := by
    have h1 : (1017874211/250000000 : ℝ) ^ 2 * ((1001983101246205873/5000000000000000000 : ℝ) - (31316544345759/10000000000000000000000000 : ℝ)) ≤ (1017874211/250000000 : ℝ) ^ 2 * Real.exp (w (1017874211/250000000 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [hEA.1]) (by positivity)
    have n : (2076245073929943934651518165389984298011561/625000000000000000000000000000000000000000 : ℝ) = (1017874211/250000000 : ℝ) ^ 2 * ((1001983101246205873/5000000000000000000 : ℝ) - (31316544345759/10000000000000000000000000 : ℝ)) := by norm_num
    linarith
  have hA2 : (1017874211/250000000 : ℝ) ^ 2 * Real.exp (w (1017874211/250000000 : ℝ)) ≤ (2076245073994836067912586045444079033988439/625000000000000000000000000000000000000000 : ℝ) := by
    have h1 : (1017874211/250000000 : ℝ) ^ 2 * Real.exp (w (1017874211/250000000 : ℝ)) ≤ (1017874211/250000000 : ℝ) ^ 2 * ((1001983101246205873/5000000000000000000 : ℝ) + (31316544345759/10000000000000000000000000 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [hEA.2]) (by positivity)
    have n : (2076245073994836067912586045444079033988439/625000000000000000000000000000000000000000 : ℝ) = (1017874211/250000000 : ℝ) ^ 2 * ((1001983101246205873/5000000000000000000 : ℝ) + (31316544345759/10000000000000000000000000 : ℝ)) := by norm_num
    linarith
  have hpa' : |2 + (1017874211/250000000 : ℝ) * φ (1017874211/250000000 : ℝ)| ≤ (273886777763809814121149/2500000000000000000000000000000000 : ℝ) := by
    have e : 2 + (1017874211/250000000 : ℝ) * φ (1017874211/250000000 : ℝ) = (2 + (1017874211/250000000 : ℝ) * (-3070123956454913517/6250000000000000000 : ℝ)) + (1017874211/250000000 : ℝ) * (φ (1017874211/250000000 : ℝ) - (-3070123956454913517/6250000000000000000 : ℝ)) := by ring
    have h2 : |(1017874211/250000000 : ℝ) * (φ (1017874211/250000000 : ℝ) - (-3070123956454913517/6250000000000000000 : ℝ))| ≤ (1017874211/250000000 : ℝ) * (31316544345759/10000000000000000000000000 : ℝ) := by
      rw [abs_mul, abs_of_pos hA]
      exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [hφA.1], by linarith [hφA.2]⟩) hA.le
    have n : |(2 : ℝ) + (1017874211/250000000 : ℝ) * (-3070123956454913517/6250000000000000000 : ℝ)| + (1017874211/250000000 : ℝ) * (31316544345759/10000000000000000000000000 : ℝ) = (273886777763809814121149/2500000000000000000000000000000000 : ℝ) := by
      norm_num [abs_of_pos]
    rw [e]
    linarith [abs_add_le (2 + (1017874211/250000000 : ℝ) * (-3070123956454913517/6250000000000000000 : ℝ)) ((1017874211/250000000 : ℝ) * (φ (1017874211/250000000 : ℝ) - (-3070123956454913517/6250000000000000000 : ℝ)))]
  obtain ⟨s₁, h1, h2, h3, h4, h5⟩ := Checked.Math.GFinal.assemble S (1017874211/250000000 : ℝ) (814299369/200000000 : ℝ) (2076245073929943934651518165389984298011561/625000000000000000000000000000000000000000 : ℝ) (2076245073994836067912586045444079033988439/625000000000000000000000000000000000000000 : ℝ)
    (273886777763809814121149/2500000000000000000000000000000000 : ℝ) 3.321992118 3.321992119 w φ hA (by norm_num) (by linarith) hw hφ hpos
    (fun s hs => hdec s ⟨by linarith [hs.1], hs.2⟩) hb hA1 hA2 hpa' (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨s₁, by norm_num at h1 ⊢; linarith, by norm_num at h2 ⊢; linarith, h3, h4, h5⟩

end Checked.Math.Gelfand

