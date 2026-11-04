import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Checked.Sim.ODETools

/-!
# Duffing oscillator: Lipschitz box, energy, and the validated cell step

Vector field F(x, v) = (v, −x − x³) on ℝ × ℝ (sup norm). On the box |x| ≤ 101/100,
|v| ≤ 13/10 it is Lipschitz with constant 41/10 ≥ 1 + 3·(101/100)². Every solution released
from rest at x = 1 keeps the energy v²/2 + x²/2 + x⁴/4 = 3/4, hence stays in the box.
`cell`: one Grönwall step from a rational polynomial approximation with certified defect.
-/

namespace Checked.Sim.DuffingCell
open Set Checked.Sim

/-- The Duffing vector field (k = β = 1). -/
def duffF (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -p.1 - p.1 ^ 3)

/-- The box |x| ≤ 101/100, |v| ≤ 13/10. -/
def box : Set (ℝ × ℝ) := {p | |p.1| ≤ 101 / 100 ∧ |p.2| ≤ 13 / 10}

theorem lip_box : LipschitzOnWith ⟨41 / 10, by norm_num⟩ duffF box := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  obtain ⟨hp1, -⟩ := hp
  obtain ⟨hq1, -⟩ := hq
  simp only [duffF, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (41 / 10 : ℝ) * _
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hm : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := (abs_nonneg _).trans hd1
  refine max_le (by nlinarith) ?_
  have hfac : (-p.1 - p.1 ^ 3) - (-q.1 - q.1 ^ 3) = -(p.1 - q.1) * (1 + p.1 ^ 2 + p.1 * q.1 + q.1 ^ 2) := by
    ring
  have ha := abs_le.1 hp1
  have hb := abs_le.1 hq1
  have hc0 : 0 ≤ 1 + p.1 ^ 2 + p.1 * q.1 + q.1 ^ 2 := by nlinarith [sq_nonneg (p.1 + q.1)]
  have hc1 : 1 + p.1 ^ 2 + p.1 * q.1 + q.1 ^ 2 ≤ 41 / 10 := by
    nlinarith [sq_nonneg (p.1 - q.1)]
  rw [hfac, abs_mul, abs_neg, abs_of_nonneg hc0]
  calc |p.1 - q.1| * (1 + p.1 ^ 2 + p.1 * q.1 + q.1 ^ 2) ≤ |p.1 - q.1| * (41 / 10) :=
        mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
    _ ≤ 41 / 10 * max |p.1 - q.1| |p.2 - q.2| := by nlinarith [abs_nonneg (p.1 - q.1)]

/-- A derivative within [a, b] at a point of [a, b) is a right derivative. -/
theorem right_of_Icc {f : ℝ → ℝ} {f' a b t : ℝ} (h : HasDerivWithinAt f f' (Icc a b) t)
    (ht : t ∈ Ico a b) : HasDerivWithinAt f f' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- Energy conservation: a solution released from rest at x = 1 stays in the box
(derivatives within [0, T], i.e. one-sided at the endpoints). -/
theorem in_box {x v : ℝ → ℝ} {T : ℝ} (hx0 : x 0 = 1) (hv0 : v 0 = 0)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (v t) (Icc 0 T) t ∧
      HasDerivWithinAt v (-1 * x t - 1 * x t ^ 3) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, (x t, v t) ∈ box := by
  set Eg : ℝ → ℝ := fun t => v t ^ 2 / 2 + x t ^ 2 / 2 + x t ^ 4 / 4 with hEg
  have hder : ∀ t ∈ Icc 0 T, HasDerivWithinAt Eg 0 (Icc 0 T) t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hd t ht
    have := (((h2.pow 2).div_const 2).add ((h1.pow 2).div_const 2)).add ((h1.pow 4).div_const 4)
    convert this using 1
    push_cast; ring
  have hc : ∀ t ∈ Icc 0 T, Eg t = Eg 0 :=
    constant_of_has_deriv_right_zero
      (fun t ht => (hder t ht).continuousWithinAt)
      (fun t ht => right_of_Icc (hder t (Ico_subset_Icc_self ht)) ht)
  intro t ht
  have h := hc t ht
  simp only [hEg, hx0, hv0] at h
  norm_num at h
  have hx2 : x t ^ 2 ≤ 1 := by nlinarith [sq_nonneg (v t), sq_nonneg (x t ^ 2)]
  have hv2 : v t ^ 2 ≤ 3 / 2 := by nlinarith [sq_nonneg (x t), sq_nonneg (x t ^ 2)]
  refine ⟨?_, ?_⟩
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x t - 1), sq_nonneg (x t + 1)]
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (v t - 13 / 10), sq_nonneg (v t + 13 / 10)]

/-- One validated step on the cell [t₀, t₀ + h]: if the polynomial pair (px, pv) (in s = t − t₀)
stays in the box and has defect at most ε, and the true solution starts within δ of it, then
the true solution stays within B of it on the whole cell. -/
theorem cell (px pv : List ℚ) {t0 h δ ε B : ℝ} {x v : ℝ → ℝ}
    (hh : 0 < h) (hKh : 41 / 10 * h < 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hdx : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt x (v t) (Icc t0 (t0 + h)) t)
    (hdv : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt v (-1 * x t - 1 * x t ^ 3) (Icc t0 (t0 + h)) t)
    (hbox : ∀ t ∈ Icc t0 (t0 + h), (x t, v t) ∈ box)
    (hpx : ∀ s ∈ Icc 0 h, |evalQ px s| ≤ 101 / 100)
    (hpv : ∀ s ∈ Icc 0 h, |evalQ pv s| ≤ 13 / 10)
    (hd1 : ∀ s ∈ Icc 0 h, |dEvalQ px s - evalQ pv s| ≤ ε)
    (hd2 : ∀ s ∈ Icc 0 h, |dEvalQ pv s + evalQ px s + evalQ px s ^ 3| ≤ ε)
    (h0 : |x t0 - evalQ px 0| ≤ δ) (h0' : |v t0 - evalQ pv 0| ≤ δ)
    (hB : δ * (1 / (1 - 41 / 10 * h)) + ε / (41 / 10) * (1 / (1 - 41 / 10 * h) - 1) ≤ B) :
    ∀ t ∈ Icc t0 (t0 + h), |x t - evalQ px (t - t0)| ≤ B ∧ |v t - evalQ pv (t - t0)| ≤ B := by
  have hs : ∀ t ∈ Ico t0 (t0 + h), t - t0 ∈ Icc 0 h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => duffF)
    (s := fun _ => box) (K := ⟨41 / 10, by norm_num⟩)
    (f := fun t => (x t, v t)) (f' := fun t => (v t, -1 * x t - 1 * x t ^ 3)) (εf := 0)
    (g := fun t => (evalQ px (t - t0), evalQ pv (t - t0)))
    (g' := fun t => (dEvalQ px (t - t0), dEvalQ pv (t - t0))) (εg := ε) (δ := δ)
    (a := t0) (b := t0 + h)
    (fun _ _ => lip_box)
    (fun t ht => (hdx t ht).continuousWithinAt.prodMk (hdv t ht).continuousWithinAt)
    (fun t ht => (right_of_Icc (hdx t (Ico_subset_Icc_self ht)) ht).prodMk
      (right_of_Icc (hdv t (Ico_subset_Icc_self ht)) ht))
    (fun t _ => by simp [duffF])
    (fun t ht => hbox t (Ico_subset_Icc_self ht))
    (((continuous_evalQ px).comp (continuous_sub_right t0)).prodMk
      ((continuous_evalQ pv).comp (continuous_sub_right t0))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ px (t - t0)).comp_sub_const t t0).prodMk
      ((hasDerivAt_evalQ pv (t - t0)).comp_sub_const t t0)).hasDerivWithinAt)
    (fun t ht => by
      simp only [duffF, Prod.dist_eq, Real.dist_eq]
      refine max_le (hd1 _ (hs t ht)) ?_
      have := hd2 _ (hs t ht)
      convert this using 2; ring)
    (fun t ht => ⟨hpx _ (hs t ht), hpv _ (hs t ht)⟩)
    (by simp only [Prod.dist_eq, Real.dist_eq, sub_self]; exact max_le h0 h0')
  intro t ht
  have h1 := key t ht
  have h2 : gronwallBound δ (41 / 10) (0 + ε) (t - t0) ≤ B := by
    refine le_trans ?_ hB
    rw [zero_add]
    exact gronwallBound_le_cell hδ hε (by norm_num) (by linarith [ht.2]) hh hKh
  simp only [Prod.dist_eq, Real.dist_eq] at h1
  exact ⟨(le_max_left _ _).trans (h1.trans h2), (le_max_right _ _).trans (h1.trans h2)⟩

end Checked.Sim.DuffingCell
