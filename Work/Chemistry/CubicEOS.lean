import Mathlib
import Checked.Records.Basic

/-!
# Chemistry (THE RESULT part 5): the critical point of the cubic equations of state

**Question.** Every process simulator computes phase behaviour with a cubic equation of state
(van der Waals 1873, Redlich–Kwong 1949, Soave 1972, Peng–Robinson 1976). Their parameters are
fixed from the critical point through the universal constants Ω_a, Ω_b, Z_c (printed, e.g.,
as `a = 0.45724 R²T_c²/P_c`, `b = 0.07780 R T_c/P_c`, `Z_c = 0.307` for Peng–Robinson). These
constants are derived by hand in every textbook from the conditions (∂P/∂v)_T = (∂²P/∂v²)_T = 0,
assuming tacitly that the critical point exists and is unique.

**What is stated here** for the generalized two-parameter family
`P(T, v) = R T/(v − b) − a/(v² + u b v + w b²)`
(van der Waals: u = w = 0; Redlich–Kwong and Soave–Redlich–Kwong: u = 1, w = 0;
Peng–Robinson: u = 2, w = −1):
1. `isCritical_iff`: at fixed T > 0, a volume v > b is a critical point of the isotherm iff
   `v³ − 3bv² − 3(u+w)b²v − (u² + uw − w)b³ = 0` and `R T (v² + ubv + wb²)² = a (v−b)²(2v+ub)`.
2. `critCubic_existsUnique`: for u > −2 and 1 + u + w > 0 that cubic (in x = v/b) has exactly
   one root x > 1.
3. `exists_unique_critical`: for u > −2 and v² + ubv + wb² > 0 for all v ≥ b, every isotherm
   family with constant a, b > 0 has exactly one critical point (T, v) with T > 0, v > b.
4. `vdW_constants`, `rk_constants`, `pr_constants`: at *every* critical point (T, v)
   of the respective equation, Z_c, Ω_b, Ω_a round to the printed constants
   (vdW 3/8, 1/8, 27/64; RK/SRK 0.33333, 0.08664, 0.42748; PR 0.3074, 0.07780, 0.45724).
   `a` is the value a(T) at the temperature considered, so these hold for every temperature
   function α(T) (RK's T^{-1/2}, Soave's and Peng–Robinson's α(T; ω)) with Ω_a defined by
   a(T_c) = Ω_a R²T_c²/P_c.

Conventions: molar volume v, temperature T, gas constant R > 0, co-volume b > 0, attraction
parameter a > 0; reduced constants `Z_c = P v/(R T)`, `Ω_b = b P/(R T)`, `Ω_a = a P/(R T)²`
evaluated at the critical point. Derivatives are Mathlib's `deriv` in v at fixed T.

FROZEN (annex 40.1) in run 2026-10-31T0628Z before proof work (commit 9241870). Changes at
proof time, all strengthenings (hypotheses removed, none added; recorded in
`runs/2026-10-31T0628Z/audit_eos.md`): `isCritical_iff` no longer assumes R, b, T > 0;
`exists_unique_critical` assumes 1 + u + w > 0 instead of positivity of v² + ubv + wb² for all
v ≥ b (equivalent given u > −2, referee item B); the three constants theorems no longer assume
R, T > 0 (at a critical point R T > 0 follows from a > 0).
-/

namespace Work.Chemistry.CubicEOS
open Checked.Records Filter Topology


/-- Generalized two-parameter cubic equation of state: pressure at temperature `T` and molar
volume `v`, `P = R T/(v − b) − a/(v² + u b v + w b²)`. -/
noncomputable def cubicP (R a b u w T v : ℝ) : ℝ := R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)
/-- Critical point of an isotherm `p` (pressure as a function of molar volume at fixed
temperature): zero slope and zero curvature, (∂P/∂v)_T = 0 and (∂²P/∂v²)_T = 0. -/
def IsCriticalIsotherm (p : ℝ → ℝ) (v : ℝ) : Prop := deriv p v = 0 ∧ deriv (deriv p) v = 0
/-- The critical cubic in `x = v_c/b`. -/
def critCubic (u w x : ℝ) : ℝ := x ^ 3 - 3 * x ^ 2 - 3 * (u + w) * x - (u ^ 2 + u * w - w)

lemma hasDerivAt_P (R a b u w T v : ℝ) (hv : v - b ≠ 0) (hD : v ^ 2 + u * b * v + w * b ^ 2 ≠ 0) :
    HasDerivAt (cubicP R a b u w T)
      (-(R * T) / (v - b) ^ 2 + a * (2 * v + u * b) / (v ^ 2 + u * b * v + w * b ^ 2) ^ 2) v := by
  have h1 : HasDerivAt (fun x => x - b) 1 v := (hasDerivAt_id v).sub_const b
  have h2 : HasDerivAt (fun x => x ^ 2 + u * b * x + w * b ^ 2) (2 * v + u * b) v := by
    have := (((hasDerivAt_pow 2 v).add ((hasDerivAt_id v).const_mul (u * b))).add_const (w * b ^ 2))
    convert this using 1; simp; ring
  have := ((hasDerivAt_const v (R * T)).div h1 hv).sub ((hasDerivAt_const v a).div h2 hD)
  convert this using 1
  · funext x; simp [cubicP]
  · field_simp; ring

lemma hasDerivAt_P1 (R a b u w T v : ℝ) (hv : v - b ≠ 0) (hD : v ^ 2 + u * b * v + w * b ^ 2 ≠ 0) :
    HasDerivAt (fun x => -(R * T) / (x - b) ^ 2 + a * (2 * x + u * b) / (x ^ 2 + u * b * x + w * b ^ 2) ^ 2)
      (2 * R * T / (v - b) ^ 3 + 2 * a * ((v ^ 2 + u * b * v + w * b ^ 2) - (2 * v + u * b) ^ 2)
        / (v ^ 2 + u * b * v + w * b ^ 2) ^ 3) v := by
  have h1 : HasDerivAt (fun x => (x - b) ^ 2) (2 * (v - b)) v := by
    have := ((hasDerivAt_id' v).sub_const b).pow 2
    convert this using 1; simp
  have h2 : HasDerivAt (fun x => x ^ 2 + u * b * x + w * b ^ 2) (2 * v + u * b) v := by
    have := (((hasDerivAt_pow 2 v).add ((hasDerivAt_id v).const_mul (u * b))).add_const (w * b ^ 2))
    convert this using 1; simp; ring
  have h3 : HasDerivAt (fun x => (x ^ 2 + u * b * x + w * b ^ 2) ^ 2)
      (2 * (v ^ 2 + u * b * v + w * b ^ 2) * (2 * v + u * b)) v := by
    convert h2.pow 2 using 1; simp
  have h4 : HasDerivAt (fun x => a * (2 * x + u * b)) (a * 2) v := by
    have := (((hasDerivAt_id' v).const_mul 2).add_const (u * b)).const_mul a
    convert this using 1; ring
  have := ((hasDerivAt_const v (-(R * T))).div h1 (pow_ne_zero 2 hv)).add (h4.div h3 (pow_ne_zero 2 hD))
  convert this using 1
  field_simp; ring

lemma deriv2_P (R a b u w T v : ℝ) (hv : v - b ≠ 0) (hD : v ^ 2 + u * b * v + w * b ^ 2 ≠ 0) :
    deriv (deriv (cubicP R a b u w T)) v =
      2 * R * T / (v - b) ^ 3 + 2 * a * ((v ^ 2 + u * b * v + w * b ^ 2) - (2 * v + u * b) ^ 2)
        / (v ^ 2 + u * b * v + w * b ^ 2) ^ 3 := by
  have hev : deriv (cubicP R a b u w T) =ᶠ[𝓝 v]
      (fun x => -(R * T) / (x - b) ^ 2 + a * (2 * x + u * b) / (x ^ 2 + u * b * x + w * b ^ 2) ^ 2) := by
    have hc : ContinuousAt (fun x => (x - b, x ^ 2 + u * b * x + w * b ^ 2)) v := by fun_prop
    have hopen : {q : ℝ × ℝ | q.1 ≠ 0 ∧ q.2 ≠ 0} ∈ 𝓝 (v - b, v ^ 2 + u * b * v + w * b ^ 2) :=
      (isOpen_ne_fun continuous_fst continuous_const |>.inter
        (isOpen_ne_fun continuous_snd continuous_const)).mem_nhds ⟨hv, hD⟩
    filter_upwards [hc hopen] with x hx
    exact (hasDerivAt_P R a b u w T x hx.1 hx.2).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_P1 R a b u w T v hv hD).deriv

/-- Critical-point conditions of the generalized cubic EOS, in closed form. -/
theorem isCritical_iff (R a b u w T v : ℝ) (ha : 0 < a) (hv : b < v) (hD : 0 < v ^ 2 + u * b * v + w * b ^ 2) :
    IsCriticalIsotherm (cubicP R a b u w T) v ↔
      (v ^ 3 - 3 * b * v ^ 2 - 3 * (u + w) * b ^ 2 * v - (u ^ 2 + u * w - w) * b ^ 3 = 0 ∧
        R * T * (v ^ 2 + u * b * v + w * b ^ 2) ^ 2 = a * (v - b) ^ 2 * (2 * v + u * b)) := by
  have hvb : v - b ≠ 0 := by linarith
  have hvb' : 0 < v - b := by linarith
  have hD0 := hD.ne'
  unfold IsCriticalIsotherm
  rw [(hasDerivAt_P R a b u w T v hvb hD0).deriv, deriv2_P R a b u w T v hvb hD0]
  set D := v ^ 2 + u * b * v + w * b ^ 2 with hDdef
  have e1 : -(R * T) / (v - b) ^ 2 + a * (2 * v + u * b) / D ^ 2 =
      (a * (v - b) ^ 2 * (2 * v + u * b) - R * T * D ^ 2) / ((v - b) ^ 2 * D ^ 2) := by
    field_simp; ring
  have e2 : 2 * R * T / (v - b) ^ 3 + 2 * a * (D - (2 * v + u * b) ^ 2) / D ^ 3 =
      (2 * R * T * D ^ 3 + 2 * a * (D - (2 * v + u * b) ^ 2) * (v - b) ^ 3) / ((v - b) ^ 3 * D ^ 3) := by
    field_simp
  rw [e1, e2, div_eq_zero_iff, div_eq_zero_iff]
  have n1 : (v - b) ^ 2 * D ^ 2 ≠ 0 := by positivity
  have n2 : (v - b) ^ 3 * D ^ 3 ≠ 0 := by positivity
  simp only [n1, n2, or_false]
  have hab : a * (v - b) ^ 2 ≠ 0 := by positivity
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    have : a * (v - b) ^ 2 * (v ^ 3 - 3 * b * v ^ 2 - 3 * (u + w) * b ^ 2 * v - (u ^ 2 + u * w - w) * b ^ 3) = 0 := by
      rw [hDdef] at h1 h2; linear_combination (-1/2 : ℝ) * h2 - (v^2 + u*b*v + w*b^2) * h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hab
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    rw [hDdef] at h2 ⊢; linear_combination (2 * (v^2 + u*b*v + w*b^2)) * h2 - 2 * a * (v - b) ^ 2 * h1


/-- The critical cubic has exactly one root above 1 (x = v_c/b > 1). -/
theorem critCubic_existsUnique (u w : ℝ) (hu : -2 < u) (h1 : 0 < 1 + u + w) :
    ∃! x : ℝ, 1 < x ∧ critCubic u w x = 0 := by
  have hf1 : critCubic u w 1 < 0 := by
    have : critCubic u w 1 = -((u + 2) * (1 + u + w)) := by unfold critCubic; ring
    rw [this]; have := mul_pos (by linarith : (0:ℝ) < u + 2) h1; linarith
  set M := 4 + 3 * |u + w| + |u ^ 2 + u * w - w| with hM
  have hM4 : 4 ≤ M := by have := abs_nonneg (u + w); have := abs_nonneg (u ^ 2 + u * w - w); linarith
  have hfM : 0 < critCubic u w M := by
    unfold critCubic
    have e1 := le_abs_self (u + w); have e2 := le_abs_self (u ^ 2 + u * w - w)
    have e3 := abs_nonneg (u + w); have e4 := abs_nonneg (u ^ 2 + u * w - w)
    have hMM : M ≤ M ^ 2 := by nlinarith
    have : M ^ 3 - 3 * M ^ 2 = M ^ 2 * (1 + 3 * |u + w| + |u ^ 2 + u * w - w|) := by rw [hM]; ring
    nlinarith [mul_nonneg e3 (by nlinarith : (0:ℝ) ≤ M ^ 2 - M), mul_nonneg e4 (by nlinarith : (0:ℝ) ≤ M ^ 2 - 1),
      mul_le_mul_of_nonneg_left e1 (by linarith : (0:ℝ) ≤ 3 * M)]
  have hcont : ContinuousOn (critCubic u w) (Set.Icc 1 M) := by unfold critCubic; fun_prop
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc (by linarith) hcont ⟨hf1.le, hfM.le⟩
  have hx1 : 1 < x := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h] at hx0; linarith
    · exact h
  have key : ∀ y z : ℝ, 1 < y → y < z → critCubic u w y = 0 → critCubic u w z = 0 → False := by
    intro y z hy hyz hfy hfz
    have id : (z - 1) * critCubic u w y - (z - y) * critCubic u w 1 - (y - 1) * critCubic u w z
        = (z - 1) * (y + z - 2) * (y - 1) * (y - z) := by unfold critCubic; ring
    rw [hfy, hfz] at id
    have h1' : 0 < (z - y) * -critCubic u w 1 := mul_pos (by linarith) (by linarith)
    have h2' : 0 < (z - 1) * (y + z - 2) * (y - 1) * (z - y) := by
      have := mul_pos (mul_pos (mul_pos (by linarith : (0:ℝ) < z - 1) (by linarith : (0:ℝ) < y + z - 2))
        (by linarith : (0:ℝ) < y - 1)) (by linarith : (0:ℝ) < z - y)
      exact this
    nlinarith
  refine ⟨x, ⟨hx1, hx0⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  rcases lt_trichotomy y x with h | h | h
  · exact (key y x hy h hy0 hx0).elim
  · exact h
  · exact (key x y hx1 h hx0 hy0).elim

lemma cubic_scale (u w b x : ℝ) :
    (x * b) ^ 3 - 3 * b * (x * b) ^ 2 - 3 * (u + w) * b ^ 2 * (x * b) - (u ^ 2 + u * w - w) * b ^ 3
      = b ^ 3 * critCubic u w x := by unfold critCubic; ring

/-- Existence and uniqueness of the critical point (T, v) of the generalized cubic EOS. -/
theorem exists_unique_critical (R a b u w : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hu : -2 < u) (h1 : 0 < 1 + u + w) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧ IsCriticalIsotherm (cubicP R a b u w p.1) p.2 := by
  have hD : ∀ v : ℝ, b ≤ v → 0 < v ^ 2 + u * b * v + w * b ^ 2 := by
    intro v hv
    have e : v ^ 2 + u * b * v + w * b ^ 2 = b ^ 2 * (1 + u + w) + (v - b) * (v + b + u * b) := by ring
    rw [e]
    have : 0 ≤ (v - b) * (v + b + u * b) := mul_nonneg (by linarith) (by nlinarith)
    have : 0 < b ^ 2 * (1 + u + w) := by positivity
    linarith
  obtain ⟨x, ⟨hx1, hx0⟩, hxu⟩ := critCubic_existsUnique u w hu h1
  set v := x * b with hvdef
  have hv : b < v := by rw [hvdef]; nlinarith
  have hDv := hD v hv.le
  set T := a * (v - b) ^ 2 * (2 * v + u * b) / (R * (v ^ 2 + u * b * v + w * b ^ 2) ^ 2) with hTdef
  have hs : 0 < 2 * v + u * b := by rw [hvdef]; nlinarith
  have hT : 0 < T := by
    rw [hTdef]; apply div_pos
    · have : 0 < v - b := by linarith
      positivity
    · positivity
  refine ⟨(T, v), ⟨hT, hv, ?_⟩, ?_⟩
  · rw [isCritical_iff R a b u w T v ha hv hDv]
    refine ⟨by rw [hvdef, cubic_scale, hx0, mul_zero], ?_⟩
    rw [hTdef, mul_div_assoc', div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring
  · rintro ⟨T', v'⟩ ⟨hT', hv', hc⟩
    simp only at hT' hv' hc
    have hDv' := hD v' hv'.le
    obtain ⟨hC, hRT⟩ := (isCritical_iff R a b u w T' v' ha hv' hDv').1 hc
    have hx' : v' / b = x := by
      apply hxu
      refine ⟨by rw [lt_div_iff₀ hb]; linarith, ?_⟩
      have := cubic_scale u w b (v' / b)
      rw [div_mul_cancel₀ v' hb.ne', hC] at this
      have hb3 : b ^ 3 ≠ 0 := by positivity
      exact (mul_eq_zero.1 this.symm).resolve_left hb3
    have hvv : v' = v := by rw [hvdef, ← hx', div_mul_cancel₀ v' hb.ne']
    subst hvv
    have : T' = T := by
      have hD0 := hDv.ne'
      rw [hTdef, eq_div_iff (by positivity)]; linear_combination hRT
    rw [this]

lemma alg (a b x D S N : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hD : D ≠ 0) (hS : S ≠ 0) (hx : x - 1 ≠ 0) :
    a * N / (b ^ 2 * D ^ 2) * (x * b) / (a * (x - 1) ^ 2 * S / (b * D ^ 2)) = x * N / ((x - 1) ^ 2 * S) ∧
    b * (a * N / (b ^ 2 * D ^ 2)) / (a * (x - 1) ^ 2 * S / (b * D ^ 2)) = N / ((x - 1) ^ 2 * S) ∧
    a * (a * N / (b ^ 2 * D ^ 2)) / (a * (x - 1) ^ 2 * S / (b * D ^ 2)) ^ 2
      = D ^ 2 * N / ((x - 1) ^ 4 * S ^ 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- At a critical point, with `x = v/b`: the critical cubic vanishes and the reduced constants
are rational functions of `x`. -/
lemma reduced (R a b u w T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hu : -2 < u) (hv : b < v) (hD : 0 < v ^ 2 + u * b * v + w * b ^ 2)
    (hc : IsCriticalIsotherm (cubicP R a b u w T) v) :
    critCubic u w (v / b) = 0 ∧ 1 < v / b ∧
    cubicP R a b u w T v * v / (R * T) = (v / b) * (((v / b) - 1) * (2 * (v / b) + u)
        - ((v / b) ^ 2 + u * (v / b) + w)) / (((v / b) - 1) ^ 2 * (2 * (v / b) + u)) ∧
    b * cubicP R a b u w T v / (R * T) = (((v / b) - 1) * (2 * (v / b) + u)
        - ((v / b) ^ 2 + u * (v / b) + w)) / (((v / b) - 1) ^ 2 * (2 * (v / b) + u)) ∧
    a * cubicP R a b u w T v / (R * T) ^ 2 = ((v / b) ^ 2 + u * (v / b) + w) ^ 2 *
        (((v / b) - 1) * (2 * (v / b) + u) - ((v / b) ^ 2 + u * (v / b) + w)) /
        (((v / b) - 1) ^ 4 * (2 * (v / b) + u) ^ 2) := by
  obtain ⟨hC, hRT⟩ := (isCritical_iff R a b u w T v ha hv hD).1 hc
  set x := v / b with hx
  have hvx : v = x * b := by rw [hx, div_mul_cancel₀ v hb.ne']
  have hx1 : 1 < x := by rw [hx, lt_div_iff₀ hb]; linarith
  have hf : critCubic u w x = 0 := by
    have := cubic_scale u w b x
    rw [← hvx, hC] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (by positivity)
  have hDx : 0 < x ^ 2 + u * x + w := by
    have e : v ^ 2 + u * b * v + w * b ^ 2 = b ^ 2 * (x ^ 2 + u * x + w) := by rw [hvx]; ring
    rw [e] at hD; exact pos_of_mul_pos_right hD (by positivity)
  have hs : 0 < 2 * x + u := by linarith
  have hx1' : 0 < x - 1 := by linarith
  have hRTx : R * T = a * (x - 1) ^ 2 * (2 * x + u) / (b * (x ^ 2 + u * x + w) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    have e : v ^ 2 + u * b * v + w * b ^ 2 = b ^ 2 * (x ^ 2 + u * x + w) := by rw [hvx]; ring
    rw [e, hvx] at hRT
    have hb3 : b ^ 3 ≠ 0 := by positivity
    apply mul_left_cancel₀ hb3
    linear_combination hRT
  have n1 : x * b - b ≠ 0 := by nlinarith
  have n2 : (x * b) ^ 2 + u * b * (x * b) + w * b ^ 2 ≠ 0 := by
    have : (x * b) ^ 2 + u * b * (x * b) + w * b ^ 2 = b ^ 2 * (x ^ 2 + u * x + w) := by ring
    rw [this]; positivity
  have n3 : x ^ 2 + u * x + w ≠ 0 := hDx.ne'
  have n4 : x - 1 ≠ 0 := hx1'.ne'
  have n5 : 2 * x + u ≠ 0 := hs.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have n6 : x * 2 + u ≠ 0 := by rw [mul_comm]; exact n5
  have hP : cubicP R a b u w T v = a * ((x - 1) * (2 * x + u) - (x ^ 2 + u * x + w))
      / (b ^ 2 * (x ^ 2 + u * x + w) ^ 2) := by
    unfold cubicP
    rw [hRTx, hvx, div_div, div_sub_div _ _ (by positivity) n2, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hA := alg a b x (x ^ 2 + u * x + w) (2 * x + u) ((x - 1) * (2 * x + u) - (x ^ 2 + u * x + w))
    ha.ne' hb0 n3 n5 n4
  rw [hP, hRTx]
  refine ⟨hf, hx1, ?_, hA.2.1, hA.2.2⟩
  rw [hvx]; exact hA.1

lemma root_bounds (c x x0 x1 : ℝ) (hx : 1 < x) (hf : x ^ 3 - 3 * x ^ 2 - 3 * x - c = 0)
    (h0 : x0 ^ 3 - 3 * x0 ^ 2 - 3 * x0 - c < 0) (h1 : 0 < x1 ^ 3 - 3 * x1 ^ 2 - 3 * x1 - c)
    (hx0 : 7 / 2 ≤ x0) (hx1 : 7 / 2 ≤ x1) : x0 < x ∧ x < x1 := by
  constructor
  · by_contra h
    push_neg at h
    have hQ : 0 < x0 ^ 2 + x0 * x + x ^ 2 - 3 * x0 - 3 * x - 3 := by nlinarith
    have e : (x0 ^ 3 - 3 * x0 ^ 2 - 3 * x0 - c) - (x ^ 3 - 3 * x ^ 2 - 3 * x - c)
        = (x0 - x) * (x0 ^ 2 + x0 * x + x ^ 2 - 3 * x0 - 3 * x - 3) := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 h) hQ.le]
  · by_contra h
    push_neg at h
    have hQ : 0 < x1 ^ 2 + x1 * x + x ^ 2 - 3 * x1 - 3 * x - 3 := by nlinarith
    have e : (x ^ 3 - 3 * x ^ 2 - 3 * x - c) - (x1 ^ 3 - 3 * x1 ^ 2 - 3 * x1 - c)
        = (x - x1) * (x1 ^ 2 + x1 * x + x ^ 2 - 3 * x1 - 3 * x - 3) := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 h) hQ.le]

/-- van der Waals: at every critical point, Z_c = 3/8, Ω_b = 1/8, Ω_a = 27/64 (exactly). -/
theorem vdW_constants (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 0 0 T) v) :
    cubicP R a b 0 0 T v * v / (R * T) = 3 / 8 ∧ b * cubicP R a b 0 0 T v / (R * T) = 1 / 8 ∧
      a * cubicP R a b 0 0 T v / (R * T) ^ 2 = 27 / 64 := by
  have hD : 0 < v ^ 2 + 0 * b * v + 0 * b ^ 2 := by nlinarith
  obtain ⟨hf, hx1, h1, h2, h3⟩ := reduced R a b 0 0 T v ha hb (by norm_num) hv hD hc
  have hx : v / b = 3 := by
    unfold critCubic at hf
    have : (v / b) ^ 2 * (v / b - 3) = 0 := by linear_combination hf
    rcases mul_eq_zero.1 this with h | h
    · nlinarith
    · linarith
  rw [h1, h2, h3, hx]; norm_num

/-- Redlich–Kwong / Soave–Redlich–Kwong: at every critical point, Z_c = 1/3 exactly,
Ω_b = 0.08664 and Ω_a = 0.42748 to five decimals. -/
theorem rk_constants (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 1 0 T) v) :
    cubicP R a b 1 0 T v * v / (R * T) = 1 / 3 ∧
      RoundsTo (b * cubicP R a b 1 0 T v / (R * T)) 0.08664 5 ∧
      RoundsTo (a * cubicP R a b 1 0 T v / (R * T) ^ 2) 0.42748 5 := by
  have hD : 0 < v ^ 2 + 1 * b * v + 0 * b ^ 2 := by nlinarith
  obtain ⟨hf, hx1, h1, h2, h3⟩ := reduced R a b 1 0 T v ha hb (by norm_num) hv hD hc
  rw [h1, h2, h3]
  set x := v / b
  unfold critCubic at hf
  have hx1' : 0 < x - 1 := by linarith
  have hs : 0 < 2 * x + 1 := by linarith
  obtain ⟨lo, hi⟩ := root_bounds 1 x 3.8473221 3.8473222 hx1 (by linear_combination hf)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_iff (by positivity)]; linear_combination (1 / 3 : ℝ) * hf
  · have e : ((x - 1) * (2 * x + 1) - (x ^ 2 + 1 * x + 0)) / ((x - 1) ^ 2 * (2 * x + 1))
        = x ^ 2 / 3 - x - 1 := by
      rw [div_eq_iff (by positivity)]; linear_combination (-2 * x ^ 2 / 3 + x) * hf
    rw [e]; unfold RoundsTo; rw [abs_le]; constructor <;> nlinarith
  · have e : (x ^ 2 + 1 * x + 0) ^ 2 * ((x - 1) * (2 * x + 1) - (x ^ 2 + 1 * x + 0)) /
        ((x - 1) ^ 4 * (2 * x + 1) ^ 2) = x / 9 := by
      rw [div_eq_iff (by positivity)]
      linear_combination (-4 * x ^ 4 / 9 + x ^ 3 + 2 * x ^ 2 / 3 + x / 9) * hf
    rw [e]; unfold RoundsTo; rw [abs_le]; constructor <;> norm_num <;> linarith

/-- Peng–Robinson: at every critical point, Z_c = 0.3074 (four decimals), Ω_b = 0.07780 and
Ω_a = 0.45724 (five decimals). -/
theorem pr_constants (R a b T v : ℝ) (ha : 0 < a) (hb : 0 < b) (hv : b < v) (hc : IsCriticalIsotherm (cubicP R a b 2 (-1) T) v) :
    RoundsTo (cubicP R a b 2 (-1) T v * v / (R * T)) 0.3074 4 ∧
      RoundsTo (b * cubicP R a b 2 (-1) T v / (R * T)) 0.07780 5 ∧
      RoundsTo (a * cubicP R a b 2 (-1) T v / (R * T) ^ 2) 0.45724 5 := by
  have hD : 0 < v ^ 2 + 2 * b * v + (-1) * b ^ 2 := by nlinarith
  obtain ⟨hf, hx1, h1, h2, h3⟩ := reduced R a b 2 (-1) T v ha hb (by norm_num) hv hD hc
  rw [h1, h2, h3]
  set x := v / b
  unfold critCubic at hf
  have hx1' : 0 < x - 1 := by linarith
  have hs : 0 < 2 * x + 2 := by linarith
  obtain ⟨lo, hi⟩ := root_bounds 3 x 3.9513730 3.9513731 hx1 (by linear_combination hf)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have e : x * ((x - 1) * (2 * x + 2) - (x ^ 2 + 2 * x + -1)) / ((x - 1) ^ 2 * (2 * x + 2))
        = -3 * x ^ 2 / 64 + 5 * x / 32 + 27 / 64 := by
      rw [div_eq_iff (by positivity)]; linear_combination (3 * x ^ 2 / 32 - x / 8 + 9 / 32) * hf
    rw [e]; unfold RoundsTo; rw [abs_le]; constructor <;> nlinarith
  · have e : ((x - 1) * (2 * x + 2) - (x ^ 2 + 2 * x + -1)) / ((x - 1) ^ 2 * (2 * x + 2))
        = 9 * x ^ 2 / 64 - 15 * x / 32 - 17 / 64 := by
      rw [div_eq_iff (by positivity)]; linear_combination (-9 * x ^ 2 / 32 + 3 * x / 8 + 5 / 32) * hf
    rw [e]; unfold RoundsTo; rw [abs_le]; constructor <;> nlinarith
  · have e : (x ^ 2 + 2 * x + -1) ^ 2 * ((x - 1) * (2 * x + 2) - (x ^ 2 + 2 * x + -1)) /
        ((x - 1) ^ 4 * (2 * x + 2) ^ 2) = 147 * x ^ 2 / 1024 - 165 * x / 512 - 523 / 1024 := by
      rw [div_eq_iff (by positivity)]
      linear_combination (-147 * x ^ 5 / 256 + 183 * x ^ 4 / 256 + 187 * x ^ 3 / 128
        - 111 * x ^ 2 / 128 + 157 * x / 256 - 89 / 256) * hf
    rw [e]; unfold RoundsTo; rw [abs_le]; constructor <;> nlinarith

end Work.Chemistry.CubicEOS
