import Mathlib

/-!
# Blind specification for `Work.Sim.Duffing.IsDuffingIVP`

Written without seeing the body of `IsDuffingIVP`, from textbook mechanics only.

Intended meaning: `IsDuffingIVP k β x₀ v₀ T x` iff `x` solves, on the closed time interval
`[0, T]`, the Duffing initial value problem
`x'' + k x + β x³ = 0`, `x(0) = x₀`, `x'(0) = v₀`.

Conventions (chosen to be the *weakest* textbook reading, so that any reasonable stricter
definition, e.g. "twice differentiable on a neighbourhood of `[0,T]`", implies the spec):
* derivatives at the endpoints `0` and `T` are one-sided (`HasDerivWithinAt _ _ (Icc 0 T)`);
* the velocity is carried as an explicit witness `v` (so the `x'(0) = v₀` condition is
  stated as `v 0 = v₀`).
For `T > 0` the witness is unique on `[0,T]` (it is `derivWithin x (Icc 0 T)`), see the
`init_vel` / `energy` fields. For `T = 0` the closed interval is the single point `{0}`,
one-sided derivatives there carry no information, and the spec only says `x 0 = x₀`;
a neighbourhood-based definition is stricter at `T = 0` (this is the one known
convention gap; it only affects the direction `DuffingSpec → IsDuffingIVP`).

Contents
* `refIVP`            : reference definition (one-sided at the endpoints).
* `refIVPNhds`        : a stricter reference (two-sided derivatives at every point of `[0,T]`).
* `DuffingSpec`       : the spec (determining law + anchors / consequences).
* `refIVP_iff_spec`   : `refIVP ↔ DuffingSpec` (both directions proved).
* `refIVPNhds_spec`   : the stricter reference satisfies the spec.
* `DuffingSpec.unique`: the spec determines `x` on `[0,T]` (Gronwall).
* symmetry lemmas     : reflection `x ↦ -x`, restriction, time translation, time reversal.
* near-miss examples  : wrong cubic sign, missing velocity condition, wrong frequency,
  endpoint jump, `cos` for the nonlinear equation.
-/

set_option linter.dupNamespace false

namespace Work.Fidelity.DuffingSpec

open Set Filter Topology Real

/-! ## Reference definitions -/

/-- Reference definition, textbook style: `x(0) = x₀`, and there is a velocity `v` with
`v(0) = v₀`, `x' = v` and `v' = -(k x + β x³)` on `[0,T]` (one-sided at the endpoints). -/
def refIVP (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∃ v : ℝ → ℝ, v 0 = v₀ ∧ ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt x (v t) (Icc 0 T) t ∧
    HasDerivWithinAt v (-(k * x t + β * x t ^ 3)) (Icc 0 T) t

/-- Stricter reference: `x` and `x'` are (two-sided) differentiable at every point of `[0,T]`
and `x'' + k x + β x³ = 0` there. -/
def refIVPNhds (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = x₀ ∧ deriv x 0 = v₀ ∧ ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivAt x (deriv x t) t ∧
    HasDerivAt (deriv x) (-(k * x t + β * x t ^ 3)) t

/-! ## The specification -/

/-- What a correct `IsDuffingIVP k β x₀ v₀ T x` must satisfy.
`init_pos` + `law` are the DETERMINING general law (see `DuffingSpec.unique`); the other
fields are textbook anchors/consequences (all derivable from the law, see `refIVP_spec`). -/
structure DuffingSpec (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) : Prop where
  /-- initial position -/
  init_pos : x 0 = x₀
  /-- DETERMINING LAW: first-order system `x' = v`, `v' = -(k x + β x³)` on `[0,T]`,
  `v(0) = v₀` (one-sided derivatives at the endpoints). -/
  law : ∃ v : ℝ → ℝ, v 0 = v₀ ∧ ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt x (v t) (Icc 0 T) t ∧
    HasDerivWithinAt v (-(k * x t + β * x t ^ 3)) (Icc 0 T) t
  /-- a solution is continuous on the closed interval -/
  cont : ContinuousOn x (Icc 0 T)
  /-- initial velocity as a one-sided derivative (meaningful for `T > 0`) -/
  init_vel : 0 < T → derivWithin x (Icc 0 T) 0 = v₀
  /-- the ODE in its literal second-order form, with ordinary `deriv`, in the open interval -/
  ode_interior : ∀ t ∈ Ioo (0 : ℝ) T, deriv (deriv x) t + k * x t + β * x t ^ 3 = 0
  /-- energy conservation `E = x'²/2 + k x²/2 + β x⁴/4` -/
  energy : 0 < T → ∀ t ∈ Icc (0 : ℝ) T,
    (derivWithin x (Icc 0 T) t) ^ 2 / 2 + k * x t ^ 2 / 2 + β * x t ^ 4 / 4
      = v₀ ^ 2 / 2 + k * x₀ ^ 2 / 2 + β * x₀ ^ 4 / 4
  /-- linear oscillator, `β = 0`, `k > 0` -/
  linear_case : β = 0 → 0 < k → ∀ t ∈ Icc (0 : ℝ) T,
    x t = x₀ * cos (√k * t) + v₀ / √k * sin (√k * t)
  /-- linear repulsive case, `β = 0`, `k < 0` -/
  linear_neg_case : β = 0 → k < 0 → ∀ t ∈ Icc (0 : ℝ) T,
    x t = x₀ * cosh (√(-k) * t) + v₀ / √(-k) * sinh (√(-k) * t)
  /-- free particle, `k = β = 0` -/
  free_case : k = 0 → β = 0 → ∀ t ∈ Icc (0 : ℝ) T, x t = x₀ + v₀ * t
  /-- equilibria: starting at rest at a zero of the force, the particle stays there -/
  equilibrium : ∀ c : ℝ, k * c + β * c ^ 3 = 0 → x₀ = c → v₀ = 0 →
    ∀ t ∈ Icc (0 : ℝ) T, x t = c
  /-- trivial solution -/
  trivial_case : x₀ = 0 → v₀ = 0 → ∀ t ∈ Icc (0 : ℝ) T, x t = 0

/-! ## Analytic helpers -/

lemma mem_nhdsGE_Icc {T s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) : Icc (0 : ℝ) T ∈ 𝓝[≥] s :=
  mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)

/-- zero one-sided derivative on `[0,T]` ⇒ constant. -/
lemma const_of_deriv_zero {T : ℝ} {g : ℝ → ℝ}
    (hg : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt g 0 (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, g t = g 0 :=
  constant_of_has_deriv_right_zero (fun t ht => (hg t ht).continuousWithinAt)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (mem_nhdsGE_Icc hs))

/-- Gronwall core: `e' = f`, `f' = -a e` with `a` bounded, zero data ⇒ `e = 0`. -/
lemma zero_of_linear {T A : ℝ} {e f a : ℝ → ℝ}
    (he : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt e (f t) (Icc 0 T) t)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (-(a t * e t)) (Icc 0 T) t)
    (ha : ∀ t ∈ Icc (0 : ℝ) T, |a t| ≤ A)
    (he0 : e 0 = 0) (hf0 : f 0 = 0) : ∀ t ∈ Icc (0 : ℝ) T, e t = 0 := by
  intro t ht
  have hcont : ContinuousOn (fun s => (e s, f s)) (Icc 0 T) := fun s hs =>
    ((he s hs).prodMk (hf s hs)).continuousWithinAt
  have hder : ∀ s ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => (e s, f s)) (f s, -(a s * e s)) (Ici s) s := by
    intro s hs
    exact ((he s (Ico_subset_Icc_self hs)).prodMk
      (hf s (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin (mem_nhdsGE_Icc hs)
  have hbound : ∀ s ∈ Ico (0 : ℝ) T,
      ‖((f s, -(a s * e s)) : ℝ × ℝ)‖ ≤ (max A 1) * ‖((e s, f s) : ℝ × ℝ)‖ + 0 := by
    intro s hs
    have hA := ha s (Ico_subset_Icc_self hs)
    rw [add_zero, Prod.norm_def, Prod.norm_def]
    simp only [Real.norm_eq_abs, abs_neg, abs_mul]
    have h1 : |f s| ≤ max |e s| |f s| := le_max_right _ _
    have h2 : |e s| ≤ max |e s| |f s| := le_max_left _ _
    have hM : 0 ≤ max |e s| |f s| := le_trans (abs_nonneg _) h2
    have hA1 : |a s| ≤ max A 1 := hA.trans (le_max_left _ _)
    have h11 : (1 : ℝ) ≤ max A 1 := le_max_right _ _
    apply max_le
    · nlinarith
    · exact mul_le_mul hA1 h2 (abs_nonneg _) (by linarith)
  have h0 : ‖((e 0, f 0) : ℝ × ℝ)‖ ≤ 0 := by simp [he0, hf0]
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder h0 hbound t ht
  rw [gronwallBound_ε0_δ0] at key
  have h' : ((e t, f t) : ℝ × ℝ) = 0 := norm_eq_zero.mp (le_antisymm key (norm_nonneg _))
  simpa using congrArg Prod.fst h'

/-! ## Uniqueness for the reference -/

theorem refIVP_unique {k β x₀ v₀ T : ℝ} {x y : ℝ → ℝ}
    (hx : refIVP k β x₀ v₀ T x) (hy : refIVP k β x₀ v₀ T y) :
    ∀ t ∈ Icc (0 : ℝ) T, x t = y t := by
  obtain ⟨hx0, v, hv0, hxv⟩ := hx
  obtain ⟨hy0, u, hu0, hyu⟩ := hy
  have cx : ContinuousOn x (Icc 0 T) := fun t ht => (hxv t ht).1.continuousWithinAt
  have cy : ContinuousOn y (Icc 0 T) := fun t ht => (hyu t ht).1.continuousWithinAt
  have hq : ContinuousOn (fun t => k + β * (x t ^ 2 + x t * y t + y t ^ 2)) (Icc 0 T) :=
    continuousOn_const.add (continuousOn_const.mul (((cx.pow 2).add (cx.mul cy)).add (cy.pow 2)))
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have key := zero_of_linear (T := T) (A := A) (e := fun t => x t - y t) (f := fun t => v t - u t)
    (a := fun t => k + β * (x t ^ 2 + x t * y t + y t ^ 2))
    (fun t ht => (hxv t ht).1.sub (hyu t ht).1)
    (fun t ht => ((hxv t ht).2.sub (hyu t ht).2).congr_deriv (by ring))
    (fun t ht => by simpa [Real.norm_eq_abs] using hA t ht)
    (by simp [hx0, hy0]) (by simp [hv0, hu0])
  exact fun t ht => sub_eq_zero.mp (key t ht)

/-- Build `refIVP` from global two-sided derivatives. -/
lemma refIVP_of_hasDerivAt {k β x₀ v₀ T : ℝ} {y w : ℝ → ℝ}
    (hy0 : y 0 = x₀) (hw0 : w 0 = v₀) (hy : ∀ t, HasDerivAt y (w t) t)
    (hw : ∀ t, HasDerivAt w (-(k * y t + β * y t ^ 3)) t) : refIVP k β x₀ v₀ T y :=
  ⟨hy0, w, hw0, fun t _ => ⟨(hy t).hasDerivWithinAt, (hw t).hasDerivWithinAt⟩⟩

lemma linear_sol {x₀ v₀ T ω : ℝ} (hω : 0 < ω) :
    refIVP (ω ^ 2) 0 x₀ v₀ T (fun t => x₀ * cos (ω * t) + v₀ / ω * sin (ω * t)) := by
  have hne : ω ≠ 0 := hω.ne'
  have hc : ∀ t, HasDerivAt (fun s => ω * s) ω t := fun t => by
    simpa using (hasDerivAt_id t).const_mul ω
  refine refIVP_of_hasDerivAt (w := fun t => v₀ * cos (ω * t) - x₀ * ω * sin (ω * t))
    (by simp) (by simp) (fun t => ?_) (fun t => ?_)
  · convert (((hc t).cos).const_mul x₀).add (((hc t).sin).const_mul (v₀ / ω)) using 1
    field_simp
    ring
  · convert (((hc t).cos).const_mul v₀).sub (((hc t).sin).const_mul (x₀ * ω)) using 1
    field_simp
    ring

lemma linear_neg_sol {x₀ v₀ T ω : ℝ} (hω : 0 < ω) :
    refIVP (-ω ^ 2) 0 x₀ v₀ T (fun t => x₀ * cosh (ω * t) + v₀ / ω * sinh (ω * t)) := by
  have hne : ω ≠ 0 := hω.ne'
  have hc : ∀ t, HasDerivAt (fun s => ω * s) ω t := fun t => by
    simpa using (hasDerivAt_id t).const_mul ω
  refine refIVP_of_hasDerivAt (w := fun t => v₀ * cosh (ω * t) + x₀ * ω * sinh (ω * t))
    (by simp) (by simp) (fun t => ?_) (fun t => ?_)
  · convert (((hc t).cosh).const_mul x₀).add (((hc t).sinh).const_mul (v₀ / ω)) using 1
    field_simp
    ring
  · convert (((hc t).cosh).const_mul v₀).add (((hc t).sinh).const_mul (x₀ * ω)) using 1
    field_simp
    ring

/-! ## Reference ⇒ spec, spec ⇒ reference -/

theorem refIVP_spec {k β x₀ v₀ T : ℝ} {x : ℝ → ℝ} (h : refIVP k β x₀ v₀ T x) :
    DuffingSpec k β x₀ v₀ T x := by
  obtain ⟨hx0, v, hv0, hxv⟩ := h
  have href : refIVP k β x₀ v₀ T x := ⟨hx0, v, hv0, hxv⟩
  have hdw : 0 < T → ∀ t ∈ Icc (0 : ℝ) T, derivWithin x (Icc 0 T) t = v t :=
    fun hT t ht => (hxv t ht).1.derivWithin (uniqueDiffOn_Icc hT t ht)
  refine
    { init_pos := hx0
      law := ⟨v, hv0, hxv⟩
      cont := fun t ht => (hxv t ht).1.continuousWithinAt
      init_vel := fun hT => (hdw hT 0 ⟨le_rfl, hT.le⟩).trans hv0
      ode_interior := ?_
      energy := ?_
      linear_case := ?_
      linear_neg_case := ?_
      free_case := ?_
      equilibrium := ?_
      trivial_case := ?_ }
  · intro t ht
    have hev : deriv x =ᶠ[𝓝 t] v := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact ((hxv s (Ioo_subset_Icc_self hs)).1.hasDerivAt (Icc_mem_nhds hs.1 hs.2)).deriv
    rw [hev.deriv_eq,
      ((hxv t (Ioo_subset_Icc_self ht)).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
    ring
  · intro hT t ht
    have hE : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt
        (fun s => v s ^ 2 / 2 + k * x s ^ 2 / 2 + β * x s ^ 4 / 4) 0 (Icc 0 T) s := by
      intro s hs
      obtain ⟨h1, h2⟩ := hxv s hs
      have := (((h2.pow 2).div_const 2).add (((h1.pow 2).const_mul k).div_const 2)).add
        (((h1.pow 4).const_mul β).div_const 4)
      convert this using 1
      norm_num
      ring
    have := const_of_deriv_zero hE t ht
    rw [hdw hT t ht, this, hx0, hv0]
  · intro hβ hk t ht
    subst hβ
    have hk' : k = (√k) ^ 2 := (Real.sq_sqrt hk.le).symm
    have hsol := linear_sol (x₀ := x₀) (v₀ := v₀) (T := T) (Real.sqrt_pos.mpr hk)
    rw [← hk'] at hsol
    exact refIVP_unique href hsol t ht
  · intro hβ hk t ht
    subst hβ
    have hk' : k = -(√(-k)) ^ 2 := by rw [Real.sq_sqrt (by linarith)]; ring
    have hsol := linear_neg_sol (x₀ := x₀) (v₀ := v₀) (T := T)
      (Real.sqrt_pos.mpr (by linarith : 0 < -k))
    rw [← hk'] at hsol
    exact refIVP_unique href hsol t ht
  · intro hk hβ t ht
    subst hk hβ
    have hsol : refIVP 0 0 x₀ v₀ T (fun t => x₀ + v₀ * t) :=
      refIVP_of_hasDerivAt (w := fun _ => v₀) (by simp) rfl
        (fun t => by simpa using ((hasDerivAt_id t).const_mul v₀).const_add x₀)
        (fun t => by simpa using hasDerivAt_const t v₀)
    exact refIVP_unique href hsol t ht
  · intro c hc hx₀ hv₀ t ht
    subst hx₀ hv₀
    have hsol : refIVP k β x₀ 0 T (fun _ => x₀) :=
      refIVP_of_hasDerivAt (w := fun _ => 0) rfl rfl
        (fun t => hasDerivAt_const t x₀)
        (fun t => by rw [hc, neg_zero]; exact hasDerivAt_const t 0)
    exact refIVP_unique href hsol t ht
  · intro hx₀ hv₀ t ht
    subst hx₀ hv₀
    have hsol : refIVP k β 0 0 T (fun _ => 0) :=
      refIVP_of_hasDerivAt (w := fun _ => 0) rfl rfl
        (fun t => hasDerivAt_const t 0)
        (fun t => by simpa using hasDerivAt_const t (0 : ℝ))
    exact refIVP_unique href hsol t ht

theorem spec_refIVP {k β x₀ v₀ T : ℝ} {x : ℝ → ℝ} (h : DuffingSpec k β x₀ v₀ T x) :
    refIVP k β x₀ v₀ T x :=
  ⟨h.init_pos, h.law⟩

theorem refIVP_iff_spec {k β x₀ v₀ T : ℝ} {x : ℝ → ℝ} :
    refIVP k β x₀ v₀ T x ↔ DuffingSpec k β x₀ v₀ T x :=
  ⟨refIVP_spec, spec_refIVP⟩

/-- The stricter (neighbourhood / two-sided) textbook reading also satisfies the spec. -/
theorem refIVPNhds_spec {k β x₀ v₀ T : ℝ} {x : ℝ → ℝ} (h : refIVPNhds k β x₀ v₀ T x) :
    DuffingSpec k β x₀ v₀ T x :=
  refIVP_spec ⟨h.1, deriv x, h.2.1, fun t ht =>
    ⟨(h.2.2 t ht).1.hasDerivWithinAt, (h.2.2 t ht).2.hasDerivWithinAt⟩⟩

/-- DETERMINING: the spec pins down `x` on `[0,T]`. -/
theorem DuffingSpec.unique {k β x₀ v₀ T : ℝ} {x y : ℝ → ℝ}
    (hx : DuffingSpec k β x₀ v₀ T x) (hy : DuffingSpec k β x₀ v₀ T y) :
    ∀ t ∈ Icc (0 : ℝ) T, x t = y t :=
  refIVP_unique (spec_refIVP hx) (spec_refIVP hy)

/-- The spec only depends on `x` restricted to `[0,T]`. -/
theorem DuffingSpec.congr {k β x₀ v₀ T : ℝ} {x y : ℝ → ℝ} (hT : 0 ≤ T)
    (hx : DuffingSpec k β x₀ v₀ T x) (hxy : EqOn x y (Icc 0 T)) :
    DuffingSpec k β x₀ v₀ T y := by
  obtain ⟨hx0, v, hv0, hxv⟩ := spec_refIVP hx
  refine refIVP_spec ⟨(hxy ⟨le_rfl, hT⟩).symm.trans hx0, v, hv0, fun t ht => ⟨?_, ?_⟩⟩
  · exact (hxv t ht).1.congr_of_mem (fun s hs => (hxy hs).symm) ht
  · rw [← hxy ht]; exact (hxv t ht).2

/-! ## Symmetries and structural properties -/

/-- Reflection symmetry `x ↦ -x` (the force is odd). -/
theorem DuffingSpec.neg {k β x₀ v₀ T : ℝ} {x : ℝ → ℝ} (h : DuffingSpec k β x₀ v₀ T x) :
    DuffingSpec k β (-x₀) (-v₀) T (fun t => -x t) := by
  obtain ⟨hx0, v, hv0, hxv⟩ := spec_refIVP h
  refine refIVP_spec ⟨by simp [hx0], fun t => -v t, by simp [hv0], fun t ht => ⟨?_, ?_⟩⟩
  · exact (hxv t ht).1.neg
  · exact (hxv t ht).2.neg.congr_deriv (by ring)

/-- Restriction to a shorter interval. -/
theorem DuffingSpec.restrict {k β x₀ v₀ T T' : ℝ} {x : ℝ → ℝ} (hT' : T' ≤ T)
    (h : DuffingSpec k β x₀ v₀ T x) : DuffingSpec k β x₀ v₀ T' x := by
  obtain ⟨hx0, v, hv0, hxv⟩ := spec_refIVP h
  have hsub : Icc (0 : ℝ) T' ⊆ Icc 0 T := Icc_subset_Icc_right hT'
  exact refIVP_spec ⟨hx0, v, hv0, fun t ht =>
    ⟨(hxv t (hsub ht)).1.mono hsub, (hxv t (hsub ht)).2.mono hsub⟩⟩

/-- Time translation (autonomy): restarting at time `s` with the current state. -/
theorem DuffingSpec.shift {k β x₀ v₀ T s : ℝ} {x : ℝ → ℝ} (hT : 0 < T) (hs : s ∈ Icc 0 T)
    (h : DuffingSpec k β x₀ v₀ T x) :
    DuffingSpec k β (x s) (derivWithin x (Icc 0 T) s) (T - s) (fun t => x (t + s)) := by
  obtain ⟨hx0, v, hv0, hxv⟩ := spec_refIVP h
  have hmaps : MapsTo (fun t => t + s) (Icc 0 (T - s)) (Icc 0 T) := fun t ht =>
    ⟨by linarith [ht.1, hs.1], by linarith [ht.2]⟩
  have hd : ∀ t, HasDerivWithinAt (fun t => t + s) 1 (Icc 0 (T - s)) t := fun t =>
    ((hasDerivAt_id t).add_const s).hasDerivWithinAt
  refine refIVP_spec ⟨by simp, fun t => v (t + s), ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [zero_add]
    exact ((hxv s hs).1.derivWithin (uniqueDiffOn_Icc hT s hs)).symm
  · exact (((hxv (t + s) (hmaps ht)).1).comp t (hd t) hmaps).congr_deriv (mul_one _)
  · exact (((hxv (t + s) (hmaps ht)).2).comp t (hd t) hmaps).congr_deriv
      (by simp only [mul_one])

/-- Time reversal: running the solution backwards from `T` with reversed velocity. -/
theorem DuffingSpec.reverse {k β x₀ v₀ T : ℝ} {x : ℝ → ℝ} (hT : 0 < T)
    (h : DuffingSpec k β x₀ v₀ T x) :
    DuffingSpec k β (x T) (-derivWithin x (Icc 0 T) T) T (fun t => x (T - t)) := by
  obtain ⟨hx0, v, hv0, hxv⟩ := spec_refIVP h
  have hmaps : MapsTo (fun t => T - t) (Icc 0 T) (Icc 0 T) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hd : ∀ t, HasDerivWithinAt (fun t => T - t) (-1) (Icc 0 T) t := fun t => by
    simpa using ((hasDerivAt_id t).const_sub T).hasDerivWithinAt
  have hTm : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  refine refIVP_spec ⟨by simp, fun t => -v (T - t), ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [sub_zero]
    rw [(hxv T hTm).1.derivWithin (uniqueDiffOn_Icc hT T hTm)]
  · have := ((hxv (T - t) (hmaps ht)).1).comp t (hd t) hmaps
    exact this.congr_deriv (by ring)
  · have := ((hxv (T - t) (hmaps ht)).2).comp t (hd t) hmaps
    exact this.neg.congr_deriv (by simp)

/-! ## Near-misses that must FAIL -/

/-- Near-miss definition: wrong sign of the cubic term. -/
def wrongSignIVP (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∃ v : ℝ → ℝ, v 0 = v₀ ∧ ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt x (v t) (Icc 0 T) t ∧
    HasDerivWithinAt v (-(k * x t - β * x t ^ 3)) (Icc 0 T) t

/-- Near-miss definition: initial velocity condition forgotten. -/
def noVelIVP (k β x₀ T : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∃ v : ℝ → ℝ, ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt x (v t) (Icc 0 T) t ∧
    HasDerivWithinAt v (-(k * x t + β * x t ^ 3)) (Icc 0 T) t

lemma cos_half_pos : 0 < cos (1 / 2 : ℝ) :=
  cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_gt_three]⟩

/-- Positive anchor: `cos` solves the harmonic oscillator `k = 1, β = 0`, `x₀ = 1, v₀ = 0`. -/
example : DuffingSpec 1 0 1 0 1 cos :=
  refIVP_spec (refIVP_of_hasDerivAt (w := fun t => -sin t) (by simp) (by simp)
    (fun t => hasDerivAt_cos t)
    (fun t => by convert (hasDerivAt_sin t).neg using 1; ring))

/-- ... but `cos` does not solve the nonlinear equation `β = 1`. -/
example : ¬ DuffingSpec 1 1 1 0 1 cos := by
  intro h
  have := h.ode_interior (1 / 2) ⟨by norm_num, by norm_num⟩
  simp [Real.deriv_cos'] at this
  nlinarith [cos_half_pos, pow_pos cos_half_pos 3]

/-- Wrong frequency: `cos t` is not the `k = 4` oscillator (that is `cos (2t)`). -/
example : ¬ DuffingSpec 4 0 1 0 1 cos := by
  intro h
  have := h.ode_interior (1 / 2) ⟨by norm_num, by norm_num⟩
  simp [Real.deriv_cos'] at this
  nlinarith [cos_half_pos]

/-- Wrong cubic sign: `x ≡ 1` solves `x'' + x - x³ = 0` (wrong-sign predicate, `k = β = 1`) ... -/
example : wrongSignIVP 1 1 1 0 1 (fun _ => 1) :=
  ⟨rfl, fun _ => 0, rfl, fun t _ =>
    ⟨hasDerivWithinAt_const _ _ _, by simpa using hasDerivWithinAt_const t (Icc (0:ℝ) 1) (0:ℝ)⟩⟩

/-- ... but not the true Duffing equation `x'' + x + x³ = 0`. -/
example : ¬ DuffingSpec 1 1 1 0 1 (fun _ => 1) := by
  intro h
  have := h.ode_interior (1 / 2) ⟨by norm_num, by norm_num⟩
  norm_num at this

/-- Positive anchor: `x ≡ 1` IS an equilibrium of the double well `x'' - x + x³ = 0`. -/
example : DuffingSpec (-1) 1 1 0 1 (fun _ => 1) :=
  refIVP_spec (refIVP_of_hasDerivAt (w := fun _ => 0) rfl rfl
    (fun t => hasDerivAt_const t 1) (fun t => by simpa using hasDerivAt_const t (0 : ℝ)))

/-- Missing initial-velocity condition: `sin` passes the predicate without `v₀` ... -/
example : noVelIVP 1 0 0 1 sin :=
  ⟨sin_zero, cos, fun t _ => ⟨(hasDerivAt_sin t).hasDerivWithinAt,
    by simpa using (hasDerivAt_cos t).hasDerivWithinAt (s := Icc (0:ℝ) 1)⟩⟩

/-- ... but fails the spec with `v₀ = 0` (only `x ≡ 0` is allowed). -/
example : ¬ DuffingSpec 1 0 0 0 1 sin := by
  intro h
  have := h.trivial_case rfl rfl 1 ⟨zero_le_one, le_rfl⟩
  linarith [sin_pos_of_pos_of_lt_pi one_pos (by linarith [pi_gt_three] : (1 : ℝ) < π)]

/-- Endpoint jump: solving the ODE only on the open interval is not enough. -/
example : ¬ DuffingSpec 1 0 1 0 1 (fun t => if t = 1 then 5 else cos t) := by
  intro h
  have := h.linear_case rfl one_pos 1 ⟨zero_le_one, le_rfl⟩
  simp at this
  linarith [cos_le_one 1]

end Work.Fidelity.DuffingSpec
