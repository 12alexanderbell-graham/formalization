import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Checked.Sim.MMCell
import Checked.Sim.MMEnclose

/-!
# Rigorous simulation of a chemical reaction network (THE RESULT parts 1 and 5): the
# half-conversion time of the full Michaelis–Menten mechanism, certified

**Question.** The Michaelis–Menten mechanism E + S ⇌ C → E + P (rate constants k₁ forward,
k₋₁ backward, k₂ catalytic) under mass-action kinetics is the basic model of enzyme catalysis.
Its full (not quasi-steady-state) rate equations have no closed-form solution. With
k₁ = k₋₁ = k₂ = 1 and initial concentrations [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0 (units: [S]₀ for
concentrations, 1/k₂ for time) the enzyme is *not* in excess-substrate conditions, so the
quasi-steady-state (Briggs–Haldane) approximation is not reliable; the half-conversion time
of the product, t½ with [P](t½) = [S]₀/2, must be computed from the full equations.
Floating-point integration (mpmath Taylor, 30 digits) gives t½ ≈ 2.566514530. This file states
it as a theorem about *every* solution of the rate equations.

**What is stated here** (frozen before proof, annex 40.1):
1. `mm_half_conversion`: every solution of the mass-action rate equations on [0, 13/5]
   (derivatives within the interval) with these rate constants and initial values has
   [P](t) < 1/2 at every t ∈ [0, 2.5665] and [P](2.5666) > 1/2; hence (continuity and the
   intermediate value theorem) the product first reaches half conversion between 2.5665
   and 2.5666.
2. `mm_solution_exists`: such a solution exists (so 1. is not vacuous).

Conventions: `IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` (km₁ = k₋₁) means the four concentration
functions s = [S], e = [E], c = [C], p = [P] take the initial values s₀, e₀, c₀, p₀ at t = 0 and
at every t ∈ [0, T] have derivatives *within* [0, T] (one-sided at the endpoints)
  s′ = −k₁ e s + k₋₁ c,  e′ = −k₁ e s + (k₋₁ + k₂) c,  c′ = k₁ e s − (k₋₁ + k₂) c,  p′ = k₂ c.
No positivity, conservation law or quasi-steady-state assumption is built in: conservation
(e + c and s + c + p constant) follows from the equations.
-/

namespace Checked.Sim.MichaelisMenten
open Set Checked.Sim.MMCell

/-! ### Proof tools (not part of the frozen statements) -/

theorem fstW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {S : Set ℝ} {t : ℝ} (h : HasDerivWithinAt α d S t) :
    HasDerivWithinAt (fun s => (α s).1) d.1 S t := by
  have := h.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa using this

theorem sndW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {S : Set ℝ} {t : ℝ} (h : HasDerivWithinAt α d S t) :
    HasDerivWithinAt (fun s => (α s).2) d.2 S t := by
  have := h.hasFDerivWithinAt.snd.hasDerivWithinAt
  simpa using this

/-- A function with zero derivative within [0, T] at every point of [0, T] is constant there. -/
theorem const_of_zero {F : ℝ → ℝ} {T : ℝ}
    (hF : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt F 0 (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, F t = F 0 :=
  constant_of_has_deriv_right_zero (fun t ht => (hF t ht).continuousWithinAt)
    (fun t ht => (hF t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))

/-- Clamp of `y` to [lo, hi]. -/
noncomputable def cl (lo hi y : ℝ) : ℝ := max lo (min hi y)

theorem cl_sub (lo hi y z : ℝ) : |cl lo hi y - cl lo hi z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem cl_mem {lo hi : ℝ} (h : lo ≤ hi) (y : ℝ) : lo ≤ cl lo hi y ∧ cl lo hi y ≤ hi := by
  unfold cl
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem cl_of_mem {lo hi y : ℝ} (h1 : lo ≤ y) (h2 : y ≤ hi) : cl lo hi y = y := by
  unfold cl; rw [min_eq_right h2, max_eq_right h1]

/-- Clamp into the box. -/
noncomputable def clampB (p : ℝ × ℝ) : ℝ × ℝ := (cl (-1 / 10) (11 / 10) p.1, cl (-1 / 10) (1 / 4) p.2)

theorem clampB_mem (p : ℝ × ℝ) : clampB p ∈ box := by
  have h1 := cl_mem (show (-1 / 10 : ℝ) ≤ 11 / 10 by norm_num) p.1
  have h2 := cl_mem (show (-1 / 10 : ℝ) ≤ 1 / 4 by norm_num) p.2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-- The clamped field: globally Lipschitz and bounded, equal to `mmF` on the box. -/
noncomputable def Φc (p : ℝ × ℝ) : ℝ × ℝ := mmF (clampB p)

theorem Φc_eq : ∀ p ∈ box, Φc p = mmF p := by
  intro p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  simp only [Φc, clampB, cl_of_mem h1 h2, cl_of_mem h3 h4]

theorem lipΦc : LipschitzWith ⟨21 / 5, by norm_num⟩ Φc := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have h := lip_box.dist_le_mul _ (clampB_mem p) _ (clampB_mem q)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _))
  simp only [clampB, Prod.dist_eq, Real.dist_eq]
  exact max_le_max (cl_sub _ _ _ _) (cl_sub _ _ _ _)

theorem normΦc (p : ℝ × ℝ) : ‖Φc p‖ ≤ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := clampB_mem p
  set u := (clampB p).1
  set w := (clampB p).2
  have m1 := mul_nonneg (show 0 ≤ u + 1 / 10 by linarith) (show 0 ≤ w + 1 / 10 by linarith)
  have m2 := mul_nonneg (show 0 ≤ 11 / 10 - u by linarith) (show 0 ≤ 1 / 4 - w by linarith)
  have m3 := mul_nonneg (show 0 ≤ u + 1 / 10 by linarith) (show 0 ≤ 1 / 4 - w by linarith)
  have m4 := mul_nonneg (show 0 ≤ 11 / 10 - u by linarith) (show 0 ≤ w + 1 / 10 by linarith)
  simp only [Φc, mmF, Prod.norm_def, Real.norm_eq_abs]
  refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;> nlinarith

theorem exists_clamped : ∃ α : ℝ → ℝ × ℝ, α 0 = (1, 0) ∧
    ∀ t ∈ Icc (0 : ℝ) (13 / 5), HasDerivWithinAt α (Φc (α t)) (Icc 0 (13 / 5)) t := by
  have hPL : IsPicardLindelof (fun _ => Φc) (tmin := 0) (tmax := 13 / 5)
      ⟨0, by norm_num, by norm_num⟩ ((1 : ℝ), (0 : ℝ)) 6 0 2 ⟨21 / 5, by norm_num⟩ :=
    { lipschitzOnWith := fun _ _ => lipΦc.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ p _ => by
        have := normΦc p; exact_mod_cast this
      mul_max_le := by
        simp only [NNReal.coe_ofNat, NNReal.coe_zero, sub_zero]
        norm_num }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hα⟩

/-- `IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` (km₁ = k₋₁): the concentrations s = [S] (substrate),
e = [E] (free enzyme), c = [C] (enzyme–substrate complex), p = [P] (product) solve the
mass-action rate equations of the Michaelis–Menten mechanism E + S ⇌ C → E + P with forward,
backward and catalytic rate constants k₁, k₋₁, k₂ on the time interval [0, T]: initial values
s₀, e₀, c₀, p₀ at t = 0, and at every t ∈ [0, T] derivatives within [0, T]
s′ = −k₁ e s + k₋₁ c, e′ = −k₁ e s + (k₋₁ + k₂) c, c′ = k₁ e s − (k₋₁ + k₂) c, p′ = k₂ c. -/
def IsMMSolution (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ) : Prop :=
  s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀ ∧ ∀ t ∈ Icc 0 T,
    HasDerivWithinAt s (-k₁ * e t * s t + km₁ * c t) (Icc 0 T) t ∧
    HasDerivWithinAt e (-k₁ * e t * s t + (km₁ + k₂) * c t) (Icc 0 T) t ∧
    HasDerivWithinAt c (k₁ * e t * s t - (km₁ + k₂) * c t) (Icc 0 T) t ∧
    HasDerivWithinAt p (k₂ * c t) (Icc 0 T) t

/-- Certified half-conversion time of the full Michaelis–Menten mechanism with
k₁ = k₋₁ = k₂ = 1, [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0: every solution of the mass-action rate
equations on the time interval [0, 13/5] (derivatives within the interval) has product
concentration strictly below 1/2 at all times in [0, 2.5665] and strictly above 1/2 at time
2.5666, so half of the substrate is first converted to product between 2.5665 and 2.5666. -/
theorem mm_half_conversion {s e c p : ℝ → ℝ} (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :
    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) := by
  obtain ⟨hs0, he0, hc0, hp0, hd⟩ := h
  have hE := const_of_zero (F := fun t => e t + c t) (fun t ht => by
      have := (hd t ht).2.1.add (hd t ht).2.2.1
      convert this using 1; ring)
  have hM := const_of_zero (F := fun t => s t + c t + p t) (fun t ht => by
      have := ((hd t ht).1.add (hd t ht).2.2.1).add (hd t ht).2.2.2
      convert this using 1; ring)
  have he : ∀ t ∈ Icc (0 : ℝ) (13 / 5), e t = 1 - c t := fun t ht => by
    have := hE t ht; simp only [he0, hc0] at this; linarith
  have hp : ∀ t ∈ Icc (0 : ℝ) (13 / 5), p t = 1 - s t - c t := fun t ht => by
    have := hM t ht; simp only [hs0, hc0, hp0] at this; linarith
  have hy : ∀ t ∈ Icc (0 : ℝ) (13 / 5), HasDerivWithinAt (fun t => (s t, c t))
      (mmF (s t, c t)) (Icc 0 (13 / 5)) t := fun t ht => by
    have := (hd t ht).1.prodMk (hd t ht).2.2.1
    convert this using 1
    simp only [mmF, he t ht, Prod.mk.injEq]
    constructor <;> ring
  obtain ⟨-, hpos, hneg⟩ := Checked.Sim.MMCerts.enclose (Φ := mmF) (fun _ _ => rfl) hy
    (by simp [hs0, hc0])
  refine ⟨fun t ht => ?_, ?_⟩
  · have := hpos t ht
    rw [hp t ⟨ht.1, by linarith [ht.2]⟩]
    simp only at this
    linarith
  · have := hneg
    rw [hp _ ⟨by norm_num, by norm_num⟩]
    simp only at this
    linarith

/-- There is a solution of the mass-action rate equations of the Michaelis–Menten mechanism
with k₁ = k₋₁ = k₂ = 1, [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0 on the time interval [0, 13/5]
(derivatives within the interval). -/
theorem mm_solution_exists :
    ∃ s e c p : ℝ → ℝ, IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p := by
  obtain ⟨α, h0, hα⟩ := exists_clamped
  obtain ⟨hbox, -, -⟩ := Checked.Sim.MMCerts.enclose (Φ := Φc) Φc_eq hα h0
  refine ⟨fun t => (α t).1, fun t => 1 - (α t).2, fun t => (α t).2,
    fun t => 1 - (α t).1 - (α t).2, by simp [h0], by simp [h0], by simp [h0], by simp [h0],
    fun t ht => ?_⟩
  have hd := hα t ht
  rw [Φc_eq _ (hbox t ht)] at hd
  have h1 := fstW hd
  have h2 := sndW hd
  simp only [mmF] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert h1 using 1; ring
  · convert (hasDerivWithinAt_const t _ (1 : ℝ)).sub h2 using 1; ring
  · convert h2 using 1; ring
  · convert ((hasDerivWithinAt_const t _ (1 : ℝ)).sub h1).sub h2 using 1; ring

end Checked.Sim.MichaelisMenten
