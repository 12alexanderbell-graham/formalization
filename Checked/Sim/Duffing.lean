import Checked.Sim.ODETools
import Checked.Sim.DuffingCell
import Checked.Sim.DuffingCerts
import Checked.Sim.DuffingExists
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Rigorous simulation (THE RESULT part 1, "simulations"): the first zero of the Duffing
# oscillator, certified by a validated ODE enclosure

**Question.** The undamped, unforced Duffing oscillator x'' + k x + β x³ = 0 (the anharmonic
oscillator of every mechanics text; hardening spring for β > 0) has no elementary closed-form
solution; its period is known in closed form through Jacobi elliptic functions (Rand, *Lecture
Notes on Nonlinear Vibrations*, §2.2: T = 4K(k)/√(1+A²), k² = A²/(2(1+A²))). With
k = β = 1, x(0) = 1, x'(0) = 0 the solution is x(t) = cn(√2 t | m = 1/4) (modulus 1/2), whose
first zero is t₁ = K(m = 1/4)/√2 ≈ 1.1920055073 (period ≈ 4.7680220291). The number is not
new: the closed form is the independent check of the *method*, a validated simulator in Lean
that needs no closed form.

**What is stated here** (frozen before proof, annex 40.1):
1. `duffing_first_zero`: every solution of x'' + x + x³ = 0, x(0) = 1, x'(0) = 0 on [0, 6/5]
   is strictly positive on [0, 1.192005] and strictly negative at t = 1.192006; hence (by
   continuity and the intermediate value theorem) its earliest zero in [0, 6/5] lies in
   (1.192005, 1.192006). Calling it the quarter period, and the period 4t₁, are informal
   remarks (they use the time-reversal symmetry, not proved here).
2. `duffing_exists`: such a solution exists (so 1. is not vacuous).

**Method (the simulator).** A piecewise polynomial approximate trajectory with rational
coefficients, a certified bound on its defect g′ − F(g) on each cell (exact rational arithmetic),
the Lipschitz constant of F on a box that every solution stays in (energy conservation), and
Grönwall's inequality (Mathlib `dist_le_of_approx_trajectories_ODE_of_mem`) give a proved
enclosure of every true solution. No floating point is trusted.

Conventions: `IsDuffingIVP k β x₀ v₀ T x` means x is differentiable at every t ∈ [0, T] with
derivative v t, v is differentiable there with derivative −k x − β x³, and x 0 = x₀, v 0 = v₀
(two-sided derivatives at the endpoints: x and v must be differentiable at 0 and T as functions
on ℝ; the equation itself is required only at points of [0, T]. This loses no generality for
this equation: energy is conserved, solutions exist for all time, and a solution with one-sided
derivatives agrees on [0, T] with a global one).

FROZEN in run 2026-11-04T0628Z before proof work.
-/

namespace Checked.Sim.Duffing
open Set Checked.Sim

/-- `x` solves the Duffing initial value problem x'' + k·x + β·x³ = 0, x(0) = x₀, x'(0) = v₀ on
the time interval [0, T]: there is a velocity function `v` with x′ = v and v′ = −k·x − β·x³ at
every time in [0, T], and x(0) = x₀, v(0) = v₀. -/
def IsDuffingIVP (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∃ v : ℝ → ℝ, v 0 = v₀ ∧
    ∀ t ∈ Icc 0 T, HasDerivAt x (v t) t ∧ HasDerivAt v (-k * x t - β * x t ^ 3) t

/-- Positivity on a cell from an enclosure and a crude lower bound of the polynomial. -/
theorem pos_cell (px : List ℚ) (c : ℚ) (cs : List ℚ) (hp : px = c :: cs) {t0 t1 B : ℝ}
    {x : ℝ → ℝ}
    (henc : ∀ t ∈ Icc t0 t1, |x t - Checked.Sim.evalQ px (t - t0)| ≤ B)
    (hlow : B < c - (t1 - t0) * Checked.Sim.evalQ (cs.map (fun c => |c|)) (t1 - t0)) :
    ∀ t ∈ Icc t0 t1, 0 < x t := by
  intro t ht
  have h1 := henc t ht
  have h2 := Checked.Sim.evalQ_ge c cs (s := t - t0) (h := t1 - t0) (by linarith [ht.1])
    (by linarith [ht.2])
  rw [hp] at h1
  rw [abs_le] at h1; linarith [h1.1]

/-- Negativity on a cell from an enclosure and a crude upper bound of the polynomial. -/
theorem neg_cell (pv : List ℚ) (c : ℚ) (cs : List ℚ) (hp : pv = c :: cs) {t0 t1 B : ℝ}
    {v : ℝ → ℝ}
    (henc : ∀ t ∈ Icc t0 t1, |v t - Checked.Sim.evalQ pv (t - t0)| ≤ B)
    (hup : c + (t1 - t0) * Checked.Sim.evalQ (cs.map (fun c => |c|)) (t1 - t0) + B < 0) :
    ∀ t ∈ Icc t0 t1, v t < 0 := by
  intro t ht
  have h1 := henc t ht
  have h2 := Checked.Sim.evalQ_le c cs (s := t - t0) (h := t1 - t0) (by linarith [ht.1])
    (by linarith [ht.2])
  rw [hp] at h1
  rw [abs_le] at h1; linarith [h1.2]

/-- A function with negative derivative on a closed interval is antitone there. -/
theorem anti_of_neg {x v : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt x (v t) (Icc a b) t)
    (hn : ∀ t ∈ Icc a b, v t < 0) : AntitoneOn x (Icc a b) := by
  have hD : ∀ t ∈ Ioo a b, HasDerivAt x (v t) t := fun t ht =>
    (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun t ht => (hd t ht).continuousWithinAt) ?_ ?_
  · intro t ht
    rw [interior_Icc] at ht
    exact (hD t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hD t ht).deriv]
    exact (hn t (Ioo_subset_Icc_self ht)).le

/-- Core form of `duffing_first_zero` for solutions with derivatives taken within [0, 6/5]
(one-sided at the endpoints; the weakest reading): positive on [0, 1.192005], negative at
1.192006. -/
theorem first_zero_within {x v : ℝ → ℝ} (hx0 : x 0 = 1) (hv0 : v 0 = 0)
    (hd : ∀ t ∈ Icc (0 : ℝ) (6 / 5), HasDerivWithinAt x (v t) (Icc 0 (6 / 5)) t ∧
      HasDerivWithinAt v (-1 * x t - 1 * x t ^ 3) (Icc 0 (6 / 5)) t) :
    (∀ t ∈ Icc (0 : ℝ) (1192005 / 1000000), 0 < x t) ∧ x (1192006 / 1000000) < 0 := by
  have hbox := DuffingCell.in_box hx0 hv0 hd
  have sub : ∀ a b : ℝ, 0 ≤ a → b ≤ 6 / 5 → ∀ t ∈ Icc a b, t ∈ Icc (0 : ℝ) (6 / 5) :=
    fun a b ha hb t ht => ⟨ha.trans ht.1, ht.2.trans hb⟩
  have s0 := DuffingCerts.step0 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) (by rw [hx0]; norm_num) (by rw [hv0]; norm_num)
  have s1 := DuffingCerts.step1 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s0.2.1 s0.2.2
  have s2 := DuffingCerts.step2 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s1.2.1 s1.2.2
  have s3 := DuffingCerts.step3 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s2.2.1 s2.2.2
  have s4 := DuffingCerts.step4 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s3.2.1 s3.2.2
  have s5 := DuffingCerts.step5 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s4.2.1 s4.2.2
  have s6 := DuffingCerts.step6 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s5.2.1 s5.2.2
  have s7 := DuffingCerts.step7 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s6.2.1 s6.2.2
  have s8 := DuffingCerts.step8 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s7.2.1 s7.2.2
  have s9 := DuffingCerts.step9 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s8.2.1 s8.2.2
  have s10 := DuffingCerts.step10 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s9.2.1 s9.2.2
  have s11 := DuffingCerts.step11 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s10.2.1 s10.2.2
  have s12 := DuffingCerts.step12 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s11.2.1 s11.2.2
  have s13 := DuffingCerts.step13 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s12.2.1 s12.2.2
  have s14 := DuffingCerts.step14 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s13.2.1 s13.2.2
  have s15 := DuffingCerts.step15 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s14.2.1 s14.2.2
  have s16 := DuffingCerts.step16 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s15.2.1 s15.2.2
  have s17 := DuffingCerts.step17 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s16.2.1 s16.2.2
  have s18 := DuffingCerts.step18 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s17.2.1 s17.2.2
  have s19 := DuffingCerts.step19 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s18.2.1 s18.2.2
  have s20 := DuffingCerts.step20 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s19.2.1 s19.2.2
  have s21 := DuffingCerts.step21 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s20.2.1 s20.2.2
  have s22 := DuffingCerts.step22 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s21.2.1 s21.2.2
  have s23 := DuffingCerts.step23 (x := x) (v := v) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).2.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t ht => hbox t (sub _ _ (by norm_num) (by norm_num) t ht)) s22.2.1 s22.2.2
  have hdl : ∀ t ∈ Icc (23/20 : ℝ) (6/5 : ℝ), HasDerivWithinAt x (v t) (Icc (23/20 : ℝ) (6/5 : ℝ)) t :=
    fun t ht => (hd t (sub _ _ (by norm_num) (by norm_num) t ht)).1.mono (Icc_subset_Icc (by norm_num) (by norm_num))
  have hneg := neg_cell DuffingCerts.pv23 _ _ rfl (fun t ht => (s23.1 t ht).2) (by norm_num [evalQ])
  have hanti := anti_of_neg hdl hneg
  have hPlo : evalQ DuffingCerts.px23 ((1192005 / 1000000 : ℝ) - (23/20 : ℝ)) = (24853262365612746735523978575311454605821/40000000000000000000000000000000000000000000000 : ℝ) := by
    norm_num [DuffingCerts.px23, evalQ]
  have hPhi : evalQ DuffingCerts.px23 ((1192006 / 1000000 : ℝ) - (23/20 : ℝ)) = (-14731770318447354823452743839230166522749073/24414062500000000000000000000000000000000000000000 : ℝ) := by
    norm_num [DuffingCerts.px23, evalQ]
  have elo := (s23.1 (1192005 / 1000000) ⟨by norm_num, by norm_num⟩).1
  have ehi := (s23.1 (1192006 / 1000000) ⟨by norm_num, by norm_num⟩).1
  rw [hPlo, abs_le] at elo
  rw [hPhi, abs_le] at ehi
  have xlo : 0 < x (1192005 / 1000000) := by linarith [elo.1]
  refine ⟨?_, by linarith [ehi.2]⟩
  have P0 := pos_cell DuffingCerts.px0 _ _ rfl (fun t ht => (s0.1 t ht).1) (by norm_num [evalQ])
  have P1 := pos_cell DuffingCerts.px1 _ _ rfl (fun t ht => (s1.1 t ht).1) (by norm_num [evalQ])
  have P2 := pos_cell DuffingCerts.px2 _ _ rfl (fun t ht => (s2.1 t ht).1) (by norm_num [evalQ])
  have P3 := pos_cell DuffingCerts.px3 _ _ rfl (fun t ht => (s3.1 t ht).1) (by norm_num [evalQ])
  have P4 := pos_cell DuffingCerts.px4 _ _ rfl (fun t ht => (s4.1 t ht).1) (by norm_num [evalQ])
  have P5 := pos_cell DuffingCerts.px5 _ _ rfl (fun t ht => (s5.1 t ht).1) (by norm_num [evalQ])
  have P6 := pos_cell DuffingCerts.px6 _ _ rfl (fun t ht => (s6.1 t ht).1) (by norm_num [evalQ])
  have P7 := pos_cell DuffingCerts.px7 _ _ rfl (fun t ht => (s7.1 t ht).1) (by norm_num [evalQ])
  have P8 := pos_cell DuffingCerts.px8 _ _ rfl (fun t ht => (s8.1 t ht).1) (by norm_num [evalQ])
  have P9 := pos_cell DuffingCerts.px9 _ _ rfl (fun t ht => (s9.1 t ht).1) (by norm_num [evalQ])
  have P10 := pos_cell DuffingCerts.px10 _ _ rfl (fun t ht => (s10.1 t ht).1) (by norm_num [evalQ])
  have P11 := pos_cell DuffingCerts.px11 _ _ rfl (fun t ht => (s11.1 t ht).1) (by norm_num [evalQ])
  have P12 := pos_cell DuffingCerts.px12 _ _ rfl (fun t ht => (s12.1 t ht).1) (by norm_num [evalQ])
  have P13 := pos_cell DuffingCerts.px13 _ _ rfl (fun t ht => (s13.1 t ht).1) (by norm_num [evalQ])
  have P14 := pos_cell DuffingCerts.px14 _ _ rfl (fun t ht => (s14.1 t ht).1) (by norm_num [evalQ])
  have P15 := pos_cell DuffingCerts.px15 _ _ rfl (fun t ht => (s15.1 t ht).1) (by norm_num [evalQ])
  have P16 := pos_cell DuffingCerts.px16 _ _ rfl (fun t ht => (s16.1 t ht).1) (by norm_num [evalQ])
  have P17 := pos_cell DuffingCerts.px17 _ _ rfl (fun t ht => (s17.1 t ht).1) (by norm_num [evalQ])
  have P18 := pos_cell DuffingCerts.px18 _ _ rfl (fun t ht => (s18.1 t ht).1) (by norm_num [evalQ])
  have P19 := pos_cell DuffingCerts.px19 _ _ rfl (fun t ht => (s19.1 t ht).1) (by norm_num [evalQ])
  have P20 := pos_cell DuffingCerts.px20 _ _ rfl (fun t ht => (s20.1 t ht).1) (by norm_num [evalQ])
  have P21 := pos_cell DuffingCerts.px21 _ _ rfl (fun t ht => (s21.1 t ht).1) (by norm_num [evalQ])
  have P22 := pos_cell DuffingCerts.px22 _ _ rfl (fun t ht => (s22.1 t ht).1) (by norm_num [evalQ])
  intro t ht
  rcases le_total t (1/20 : ℝ) with h0 | h0
  · exact P0 t ⟨ht.1, h0⟩
  rcases le_total t (1/10 : ℝ) with h1 | h1
  · exact P1 t ⟨h0, h1⟩
  rcases le_total t (3/20 : ℝ) with h2 | h2
  · exact P2 t ⟨h1, h2⟩
  rcases le_total t (1/5 : ℝ) with h3 | h3
  · exact P3 t ⟨h2, h3⟩
  rcases le_total t (1/4 : ℝ) with h4 | h4
  · exact P4 t ⟨h3, h4⟩
  rcases le_total t (3/10 : ℝ) with h5 | h5
  · exact P5 t ⟨h4, h5⟩
  rcases le_total t (7/20 : ℝ) with h6 | h6
  · exact P6 t ⟨h5, h6⟩
  rcases le_total t (2/5 : ℝ) with h7 | h7
  · exact P7 t ⟨h6, h7⟩
  rcases le_total t (9/20 : ℝ) with h8 | h8
  · exact P8 t ⟨h7, h8⟩
  rcases le_total t (1/2 : ℝ) with h9 | h9
  · exact P9 t ⟨h8, h9⟩
  rcases le_total t (11/20 : ℝ) with h10 | h10
  · exact P10 t ⟨h9, h10⟩
  rcases le_total t (3/5 : ℝ) with h11 | h11
  · exact P11 t ⟨h10, h11⟩
  rcases le_total t (13/20 : ℝ) with h12 | h12
  · exact P12 t ⟨h11, h12⟩
  rcases le_total t (7/10 : ℝ) with h13 | h13
  · exact P13 t ⟨h12, h13⟩
  rcases le_total t (3/4 : ℝ) with h14 | h14
  · exact P14 t ⟨h13, h14⟩
  rcases le_total t (4/5 : ℝ) with h15 | h15
  · exact P15 t ⟨h14, h15⟩
  rcases le_total t (17/20 : ℝ) with h16 | h16
  · exact P16 t ⟨h15, h16⟩
  rcases le_total t (9/10 : ℝ) with h17 | h17
  · exact P17 t ⟨h16, h17⟩
  rcases le_total t (19/20 : ℝ) with h18 | h18
  · exact P18 t ⟨h17, h18⟩
  rcases le_total t (1 : ℝ) with h19 | h19
  · exact P19 t ⟨h18, h19⟩
  rcases le_total t (21/20 : ℝ) with h20 | h20
  · exact P20 t ⟨h19, h20⟩
  rcases le_total t (11/10 : ℝ) with h21 | h21
  · exact P21 t ⟨h20, h21⟩
  rcases le_total t (23/20 : ℝ) with h22 | h22
  · exact P22 t ⟨h21, h22⟩
  exact xlo.trans_le (hanti ⟨h22, by linarith [ht.2]⟩ ⟨by norm_num, by norm_num⟩ ht.2)

/-- First zero of the Duffing oscillator x'' + x + x³ = 0 released from rest at x = 1: every
solution on [0, 6/5] is strictly positive for all times in [0, 1.192005] and strictly negative
at time 1.192006, so its first zero (the quarter period) lies strictly between 1.192005 and
1.192006. -/
theorem duffing_first_zero (x : ℝ → ℝ) (hx : IsDuffingIVP 1 1 1 0 (6 / 5) x) :
    (∀ t ∈ Icc (0 : ℝ) (1192005 / 1000000), 0 < x t) ∧ x (1192006 / 1000000) < 0 := by
  obtain ⟨hx0, v, hv0, hd⟩ := hx
  exact first_zero_within hx0 hv0 fun t ht =>
    ⟨(hd t ht).1.hasDerivWithinAt, (hd t ht).2.hasDerivWithinAt⟩

/-- There is a solution of the Duffing initial value problem x'' + x + x³ = 0, x(0) = 1,
x'(0) = 0 on the time interval [0, 6/5]. -/
theorem duffing_exists : ∃ x : ℝ → ℝ, IsDuffingIVP 1 1 1 0 (6 / 5) x := by
  obtain ⟨x, v, hx0, hv0, hd⟩ := DuffingExists.exists_solution
  exact ⟨x, hx0, v, hv0, hd⟩

end Checked.Sim.Duffing
