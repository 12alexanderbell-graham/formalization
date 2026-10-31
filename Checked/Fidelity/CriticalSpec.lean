import Mathlib.Analysis.Calculus.Taylor
import Checked.Chemistry.CubicEOS

/-!
# Specification of "critical point of an isotherm"

`C p v` is read: the molar volume `v` is the critical point of the isotherm `p`
(pressure as a function of molar volume at fixed temperature).

Textbook (van der Waals, Landau–Lifshitz §83, Callen §9): the critical point of an
isotherm is the point where the isotherm has a *horizontal inflection*:
`(∂p/∂v)_T = 0` and `(∂²p/∂v²)_T = 0`.

The determining law of the spec states this without derivatives: for a `C²` isotherm,
`C p v` holds iff the isotherm is flat to second order at `v`,
`p v' - p v = o((v' - v)²)` as `v' → v`.

The spec is blind: it was written without seeing the definition under test (subagent, run
2026-10-31T0628Z, frozen in `Work/Fidelity/CriticalSpec.lean`; copied verbatim here, namespace
changed). Added below the copy: `isCriticalIsotherm_meets` (the program's definition
`Checked.Chemistry.CubicEOS.IsCriticalIsotherm` satisfies every field) and
`criticalSpec_pins` (any predicate meeting the spec agrees with it on every isotherm that is
`C²` near the point; proof from the determining law alone).
-/

set_option linter.dupNamespace false

namespace Checked.Fidelity.CriticalSpec

open Asymptotics Filter Topology

/-- Laws every faithful definition `C` of "critical point of an isotherm" must satisfy.
Only the physical domain is constrained: every general law assumes `p` is `C²` near `v`. -/
structure CriticalSpec (C : (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- (a) DETERMINING LAW. For an isotherm that is `C²` near `v`, `v` is critical iff
  the isotherm is flat to second order there: `p(v') − p(v) = o((v' − v)²)` as `v' → v`
  (horizontal tangent and vanishing curvature, i.e. a horizontal inflection). -/
  determining : ∀ (p : ℝ → ℝ) (v : ℝ), ContDiffAt ℝ 2 p v →
    (C p v ↔ (fun v' => p v' - p v) =o[𝓝 v] (fun v' => (v' - v) ^ 2))
  /-- (b) ANCHOR. van der Waals isotherm at `T_c = 8a/(27Rb)` is critical at `v_c = 3b`. -/
  vdW_critical : ∀ a b R : ℝ, 0 < a → 0 < b → 0 < R →
    C (fun v => R * (8 * a / (27 * R * b)) / (v - b) - a / v ^ 2) (3 * b)
  /-- (b) NEAR MISS. Same critical isotherm, wrong volume `v = 2b`. -/
  vdW_wrong_volume : ∀ a b R : ℝ, 0 < a → 0 < b → 0 < R →
    ¬ C (fun v => R * (8 * a / (27 * R * b)) / (v - b) - a / v ^ 2) (2 * b)
  /-- (b) NEAR MISS. Right volume `v = 3b`, wrong temperature `T = a/(4Rb)`. -/
  vdW_wrong_temperature : ∀ a b R : ℝ, 0 < a → 0 < b → 0 < R →
    ¬ C (fun v => R * (a / (4 * R * b)) / (v - b) - a / v ^ 2) (3 * b)
  /-- (b) UNIQUENESS ANCHOR. On the physical branch `v > b`, the only critical point of any
  van der Waals isotherm is `(T, v) = (8a/(27Rb), 3b)`. -/
  vdW_unique : ∀ a b R T v : ℝ, 0 < a → 0 < b → 0 < R → 0 < T → b < v →
    C (fun w => R * T / (w - b) - a / w ^ 2) v → T = 8 * a / (27 * R * b) ∧ v = 3 * b
  /-- (b) NEAR MISS. The ideal gas has no critical point. -/
  ideal_gas : ∀ R T v : ℝ, 0 < R → 0 < T → 0 < v → ¬ C (fun w => R * T / w) v
  /-- (b) NEAR MISS. A straight line `p(v) = c − v` has no critical point. -/
  line : ∀ c v : ℝ, ¬ C (fun w => c - w) v
  /-- (b) NEAR MISS. A mere stationary point (`p' = 0`, `p'' ≠ 0`, e.g. a spinodal-type
  extremum) is not critical. -/
  stationary_not_critical : ∀ P v₀ : ℝ, ¬ C (fun w => P + (w - v₀) ^ 2) v₀
  /-- (b) ANCHOR. The model (mechanically stable) critical isotherm `p = P − k (v − v₀)³`,
  `k > 0`, is critical at `v₀`. -/
  cubic_critical : ∀ P k v₀ : ℝ, 0 < k → C (fun w => P - k * (w - v₀) ^ 3) v₀
  /-- (c) Locality: only the germ of the isotherm at `v` matters. -/
  local_ : ∀ (p q : ℝ → ℝ) (v : ℝ), ContDiffAt ℝ 2 p v → p =ᶠ[𝓝 v] q → (C p v ↔ C q v)
  /-- (c) Shifting the pressure origin does not move the critical point. -/
  add_const : ∀ (p : ℝ → ℝ) (v c : ℝ), ContDiffAt ℝ 2 p v →
    (C (fun w => p w + c) v ↔ C p v)
  /-- (c) Changing the pressure unit (positive rescaling) does not move the critical point. -/
  smul_pos : ∀ (p : ℝ → ℝ) (v k : ℝ), 0 < k → ContDiffAt ℝ 2 p v →
    (C (fun w => k * p w) v ↔ C p v)
  /-- (c) Translating the volume axis translates the critical point. -/
  translate : ∀ (p : ℝ → ℝ) (v s : ℝ), ContDiffAt ℝ 2 p v →
    (C (fun w => p (w + s)) (v - s) ↔ C p v)
  /-- (c) Changing the volume unit (positive rescaling of `v`) rescales the critical volume. -/
  rescale_volume : ∀ (p : ℝ → ℝ) (v k : ℝ), 0 < k → ContDiffAt ℝ 2 p v →
    (C (fun w => p (k * w)) (v / k) ↔ C p v)

/-! ## Reference definition (textbook) and its verification -/

/-- Textbook definition: horizontal inflection, `(∂p/∂v)_T = 0` and `(∂²p/∂v²)_T = 0`. -/
def IsCriticalRef (p : ℝ → ℝ) (v : ℝ) : Prop :=
  deriv p v = 0 ∧ deriv (deriv p) v = 0

/-- Second-order Taylor expansion with Peano remainder at a point where `p` is `C²`. -/
theorem taylor2 {p : ℝ → ℝ} {v : ℝ} (hp : ContDiffAt ℝ 2 p v) :
    (fun x => p x - (p v + deriv p v * (x - v) + deriv (deriv p) v / 2 * (x - v) ^ 2))
      =o[𝓝 v] (fun x => (x - v) ^ 2) := by
  obtain ⟨u, hu, hpu⟩ := hp.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
  have hv : v ∈ Metric.ball v ε := Metric.mem_ball_self hε
  have hs : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) p (Metric.ball v ε) := hpu.mono hεu
  have h := taylor_isLittleO (convex_ball v ε) hv hs
  rw [Metric.isOpen_ball.nhdsWithin_eq hv] at h
  refine h.congr_left (fun x => ?_)
  have h1 : iteratedDerivWithin 1 p (Metric.ball v ε) v = deriv p v := by
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball hv, iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 p (Metric.ball v ε) v = deriv (deriv p) v := by
    rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball hv, iteratedDeriv_succ,
      iteratedDeriv_one]
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h1, h2]
  simp
  ring

/-- A coefficient `c` with `c • g = o(g)` (and `g` frequently nonzero) vanishes. -/
theorem coeff_eq_zero {l : Filter ℝ} {g : ℝ → ℝ} (c : ℝ) (hg : ∃ᶠ x in l, ‖g x‖ ≠ 0)
    (h : (fun x => c * g x) =o[l] g) : c = 0 := by
  by_contra hc
  exact isLittleO_irrefl' hg ((isLittleO_const_mul_left_iff hc).1 h)

theorem frequently_pow_ne (v : ℝ) (n : ℕ) : ∃ᶠ x in 𝓝 v, ‖(x - v) ^ n‖ ≠ 0 := by
  have : ∀ᶠ x in 𝓝[≠] v, ‖(x - v) ^ n‖ ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x - v ≠ 0 := sub_ne_zero.2 hx
    simpa using pow_ne_zero n this
  exact this.frequently.filter_mono nhdsWithin_le_nhds

/-- Determining law for the reference predicate. -/
theorem ref_determining (p : ℝ → ℝ) (v : ℝ) (hp : ContDiffAt ℝ 2 p v) :
    IsCriticalRef p v ↔ (fun v' => p v' - p v) =o[𝓝 v] (fun v' => (v' - v) ^ 2) := by
  have hT := taylor2 hp
  constructor
  · rintro ⟨h1, h2⟩
    refine hT.congr_left (fun x => ?_)
    rw [h1, h2]; ring
  · intro h
    set d1 := deriv p v
    set d2 := deriv (deriv p) v
    -- the polynomial part is o((x-v)^2)
    have hq : (fun x => d1 * (x - v) + d2 / 2 * (x - v) ^ 2) =o[𝓝 v] (fun x => (x - v) ^ 2) :=
      (h.sub hT).congr_left (fun x => by ring)
    -- (x - v)^2 = o(x - v)
    have hsq : (fun x : ℝ => (x - v) ^ 2) =o[𝓝 v] (fun x => x - v) :=
      (isLittleO_pow_sub_sub v one_lt_two).congr_left (fun x => by simp [Real.norm_eq_abs])
    have hd1 : d1 = 0 := by
      apply coeff_eq_zero (l := 𝓝 v) (g := fun x => x - v) d1
      · simpa using frequently_pow_ne v 1
      · have := (hq.trans hsq).sub (hsq.const_mul_left (d2 / 2))
        exact this.congr_left (fun x => by ring)
    have hd2 : d2 / 2 = 0 := by
      apply coeff_eq_zero (l := 𝓝 v) (g := fun x => (x - v) ^ 2) (d2 / 2)
      · exact frequently_pow_ne v 2
      · exact hq.congr_left (fun x => by rw [hd1]; ring)
    exact ⟨hd1, by linarith⟩

/-! ### van der Waals derivative computations -/

theorem vdW_hasDerivAt (c a b x : ℝ) (hb : x ≠ b) (h0 : x ≠ 0) :
    HasDerivAt (fun w => c / (w - b) - a / w ^ 2) (-c / (x - b) ^ 2 + 2 * a / x ^ 3) x := by
  have hxb : x - b ≠ 0 := sub_ne_zero.2 hb
  have e1 := (hasDerivAt_const x c).fun_div ((hasDerivAt_id' x).sub_const b) hxb
  have e2 := (hasDerivAt_const x a).fun_div (hasDerivAt_pow 2 x) (pow_ne_zero 2 h0)
  convert e1.sub e2 using 1
  field_simp
  ring

theorem vdW_hasDerivAt2 (c a b x : ℝ) (hb : x ≠ b) (h0 : x ≠ 0) :
    HasDerivAt (fun w => -c / (w - b) ^ 2 + 2 * a / w ^ 3)
      (2 * c / (x - b) ^ 3 - 6 * a / x ^ 4) x := by
  have hxb : x - b ≠ 0 := sub_ne_zero.2 hb
  have e1 := (hasDerivAt_const x (-c)).fun_div (((hasDerivAt_id' x).sub_const b).pow 2)
    (pow_ne_zero 2 hxb)
  have e2 := (hasDerivAt_const x (2 * a)).fun_div (hasDerivAt_pow 3 x) (pow_ne_zero 3 h0)
  convert e1.add e2 using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem vdW_deriv (c a b x : ℝ) (hb : x ≠ b) (h0 : x ≠ 0) :
    deriv (fun w => c / (w - b) - a / w ^ 2) x = -c / (x - b) ^ 2 + 2 * a / x ^ 3 :=
  (vdW_hasDerivAt c a b x hb h0).deriv

theorem vdW_deriv2 (c a b x : ℝ) (hb : x ≠ b) (h0 : x ≠ 0) :
    deriv (deriv (fun w => c / (w - b) - a / w ^ 2)) x
      = 2 * c / (x - b) ^ 3 - 6 * a / x ^ 4 := by
  have hev : deriv (fun w => c / (w - b) - a / w ^ 2)
      =ᶠ[𝓝 x] (fun w => -c / (w - b) ^ 2 + 2 * a / w ^ 3) := by
    filter_upwards [eventually_ne_nhds hb, eventually_ne_nhds h0] with y hyb hy0
    exact vdW_deriv c a b y hyb hy0
  rw [hev.deriv_eq]
  exact (vdW_hasDerivAt2 c a b x hb h0).deriv

theorem ref_vdW_unique (a b R T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) (_hT : 0 < T)
    (hv : b < v) (h : IsCriticalRef (fun w => R * T / (w - b) - a / w ^ 2) v) :
    T = 8 * a / (27 * R * b) ∧ v = 3 * b := by
  obtain ⟨h1, h2⟩ := h
  have hvb : v ≠ b := ne_of_gt hv
  have hv0 : v ≠ 0 := by linarith
  rw [vdW_deriv _ _ _ _ hvb hv0] at h1
  rw [vdW_deriv2 _ _ _ _ hvb hv0] at h2
  have hw : 0 < v - b := sub_pos.2 hv
  have hvpos : 0 < v := by linarith
  have e1 : R * T * v ^ 3 = 2 * a * (v - b) ^ 2 := by
    field_simp at h1; linarith
  have e2 : R * T * v ^ 4 = 3 * a * (v - b) ^ 3 := by
    field_simp at h2; linarith
  have e3 : 2 * a * (v - b) ^ 2 * v = 3 * a * (v - b) ^ 3 := by
    rw [← e2, ← e1]; ring
  have e4 : 2 * v = 3 * (v - b) := by
    have hpos : 0 < a * (v - b) ^ 2 := by positivity
    have : (a * (v - b) ^ 2) * (2 * v) = (a * (v - b) ^ 2) * (3 * (v - b)) := by
      linarith [e3]
    exact mul_left_cancel₀ hpos.ne' this
  have hv3 : v = 3 * b := by linarith
  refine ⟨?_, hv3⟩
  subst hv3
  field_simp
  have : R * T * (27 * b ^ 3) = 2 * a * (4 * b ^ 2) := by
    have := e1; ring_nf at this ⊢; linarith
  nlinarith [this, pow_pos hb 2]

theorem ref_vdW_critical (a b R : ℝ) (_ha : 0 < a) (hb : 0 < b) (hR : 0 < R) :
    IsCriticalRef (fun v => R * (8 * a / (27 * R * b)) / (v - b) - a / v ^ 2) (3 * b) := by
  have hvb : 3 * b ≠ b := by intro h; linarith
  have hv0 : 3 * b ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · rw [vdW_deriv _ _ _ _ hvb hv0]
    field_simp
    ring
  · rw [vdW_deriv2 _ _ _ _ hvb hv0]
    field_simp
    ring

/-! ### Simple model isotherms -/

theorem ref_ideal_gas (R T v : ℝ) (hR : 0 < R) (hT : 0 < T) (hv : 0 < v) :
    ¬ IsCriticalRef (fun w => R * T / w) v := by
  rintro ⟨h1, -⟩
  have e := (hasDerivAt_const v (R * T)).fun_div (hasDerivAt_id' v) hv.ne'
  rw [e.deriv] at h1
  have : R * T / v ^ 2 = 0 := by
    have := h1; field_simp at this ⊢; linarith
  have hpos : 0 < R * T / v ^ 2 := by positivity
  linarith

theorem ref_line (c v : ℝ) : ¬ IsCriticalRef (fun w => c - w) v := by
  rintro ⟨h1, -⟩
  have e : HasDerivAt (fun w => c - w) (0 - 1) v := (hasDerivAt_const v c).sub (hasDerivAt_id' v)
  rw [e.deriv] at h1
  norm_num at h1

theorem ref_stationary (P v₀ : ℝ) : ¬ IsCriticalRef (fun w => P + (w - v₀) ^ 2) v₀ := by
  rintro ⟨-, h2⟩
  have hd : deriv (fun w => P + (w - v₀) ^ 2) = fun w => 2 * (w - v₀) := by
    funext w
    have e : HasDerivAt (fun w => P + (w - v₀) ^ 2) (0 + ((2 : ℕ) : ℝ) * (w - v₀) ^ (2 - 1) * 1) w :=
      (hasDerivAt_const w P).add (((hasDerivAt_id' w).sub_const v₀).pow 2)
    rw [e.deriv]; simp
  rw [hd] at h2
  have e := ((hasDerivAt_id' v₀).sub_const v₀).const_mul 2
  rw [e.deriv] at h2
  norm_num at h2

theorem ref_cubic (P k v₀ : ℝ) : IsCriticalRef (fun w => P - k * (w - v₀) ^ 3) v₀ := by
  have hd : deriv (fun w => P - k * (w - v₀) ^ 3) = fun w => -(k * (3 * (w - v₀) ^ 2)) := by
    funext w
    have e : HasDerivAt (fun w => P - k * (w - v₀) ^ 3)
        (0 - k * (((3 : ℕ) : ℝ) * (w - v₀) ^ (3 - 1) * 1)) w :=
      (hasDerivAt_const w P).sub ((((hasDerivAt_id' w).sub_const v₀).pow 3).const_mul k)
    rw [e.deriv]; simp
  refine ⟨by rw [hd]; simp, ?_⟩
  rw [hd]
  have e : HasDerivAt (fun w => -(k * (3 * (w - v₀) ^ 2)))
      (-(k * (3 * (((2 : ℕ) : ℝ) * (v₀ - v₀) ^ (2 - 1) * 1)))) v₀ :=
    ((((hasDerivAt_id' v₀).sub_const v₀).pow 2).const_mul 3 |>.const_mul k).neg
  rw [e.deriv]; simp

/-! ### Invariances -/

theorem ref_local (p q : ℝ → ℝ) (v : ℝ) (h : p =ᶠ[𝓝 v] q) :
    IsCriticalRef p v ↔ IsCriticalRef q v := by
  unfold IsCriticalRef
  rw [h.deriv_eq, h.deriv.deriv_eq]

theorem ref_add_const (p : ℝ → ℝ) (v c : ℝ) :
    IsCriticalRef (fun w => p w + c) v ↔ IsCriticalRef p v := by
  have hd : deriv (fun w => p w + c) = deriv p := funext fun x => deriv_add_const c
  unfold IsCriticalRef
  rw [hd]

theorem ref_smul (p : ℝ → ℝ) (v k : ℝ) (hk : k ≠ 0) :
    IsCriticalRef (fun w => k * p w) v ↔ IsCriticalRef p v := by
  unfold IsCriticalRef
  rw [deriv_const_mul_field', deriv_const_mul_field']
  simp [hk]

theorem ref_translate (p : ℝ → ℝ) (v s : ℝ) :
    IsCriticalRef (fun w => p (w + s)) (v - s) ↔ IsCriticalRef p v := by
  have hd : deriv (fun w => p (w + s)) = fun w => deriv p (w + s) :=
    funext fun x => deriv_comp_add_const p s x
  unfold IsCriticalRef
  simp only [hd, deriv_comp_add_const, sub_add_cancel]

theorem ref_rescale (p : ℝ → ℝ) (v k : ℝ) (hk : k ≠ 0) :
    IsCriticalRef (fun w => p (k * w)) (v / k) ↔ IsCriticalRef p v := by
  have hd : deriv (fun w => p (k * w)) = fun w => k * deriv p (k * w) :=
    funext fun x => by rw [deriv_comp_mul_left, smul_eq_mul]
  unfold IsCriticalRef
  have hkv : k * (v / k) = v := by field_simp
  simp only [hd, deriv_const_mul_field', deriv_comp_mul_left, smul_eq_mul, hkv]
  simp [hk]

/-- The textbook reference predicate satisfies the whole specification. -/
theorem ref_satisfies : CriticalSpec IsCriticalRef where
  determining := ref_determining
  vdW_critical := ref_vdW_critical
  vdW_wrong_volume := by
    intro a b R ha hb hR h
    have hT : 0 < 8 * a / (27 * R * b) := by positivity
    have := (ref_vdW_unique a b R _ (2 * b) ha hb hR hT (by linarith) h).2
    linarith
  vdW_wrong_temperature := by
    intro a b R ha hb hR h
    have hT : 0 < a / (4 * R * b) := by positivity
    have := (ref_vdW_unique a b R _ (3 * b) ha hb hR hT (by linarith) h).1
    field_simp at this
    nlinarith [mul_pos ha (mul_pos hR hb)]
  vdW_unique := ref_vdW_unique
  ideal_gas := ref_ideal_gas
  line := ref_line
  stationary_not_critical := ref_stationary
  cubic_critical := fun P k v₀ _ => ref_cubic P k v₀
  local_ := fun p q v _ h => ref_local p q v h
  add_const := fun p v c _ => ref_add_const p v c
  smul_pos := fun p v k hk _ => ref_smul p v k hk.ne'
  translate := fun p v s _ => ref_translate p v s
  rescale_volume := fun p v k hk _ => ref_rescale p v k hk.ne'




/-! ## The program's definition: meets and pin (run 2026-10-31T0628Z) -/

/-- The program's `IsCriticalIsotherm` meets the blind specification. -/
theorem isCriticalIsotherm_meets : CriticalSpec Checked.Chemistry.CubicEOS.IsCriticalIsotherm :=
  ref_satisfies

/-- Pin: any predicate meeting `CriticalSpec` agrees with `IsCriticalIsotherm` on every isotherm
that is `C²` near the volume considered (from the determining law alone). -/
theorem criticalSpec_pins (C : (ℝ → ℝ) → ℝ → Prop) (h : CriticalSpec C) (p : ℝ → ℝ) (v : ℝ)
    (hp : ContDiffAt ℝ 2 p v) : C p v ↔ Checked.Chemistry.CubicEOS.IsCriticalIsotherm p v := by
  rw [h.determining p v hp]
  exact (ref_determining p v hp).symm

end Checked.Fidelity.CriticalSpec
