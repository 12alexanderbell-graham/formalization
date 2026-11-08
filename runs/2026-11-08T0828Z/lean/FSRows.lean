import Mathlib
import Checked.Homann.Homann
import Checked.Blasius.Blasius

/-! Scaling of the Falkner–Skan-type system f' = p, p' = q, q' = −a f q − b (1 − p²) on [0, ∞):
F(s) = c f(s/c), P(s) = p(s/c), Q(s) = q(s/c)/c solves the same system with a/c², b/c². -/

namespace FSScale
open Set Filter Topology

lemma mapsTo_div {c : ℝ} (hc : 0 < c) : MapsTo (fun s : ℝ => s / c) (Ici 0) (Ici 0) :=
  fun s hs => div_nonneg (mem_Ici.mp hs) hc.le

lemma hd {c : ℝ} (x : ℝ) : HasDerivWithinAt (fun s : ℝ => s / c) (1 / c) (Ici 0) x := by
  simpa using (hasDerivWithinAt_id x (Ici (0:ℝ))).div_const c

theorem scale {a b c : ℝ} (hc : 0 < c) {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(a * f η * q η) - b * (1 - p η ^ 2)) (Ici 0) η) :
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => c * f (s / c)) (p (s / c)) (Ici 0) s) ∧
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => p (s / c)) (q (s / c) / c) (Ici 0) s) ∧
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => q (s / c) / c)
      (-(a / c ^ 2 * (c * f (s / c)) * (q (s / c) / c)) - b / c ^ 2 * (1 - p (s / c) ^ 2)) (Ici 0) s) := by
  have hm := mapsTo_div hc
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have h := ((hf (s / c) (hm hs)).comp s (hd s) hm).const_mul c
    exact h.congr_deriv (by field_simp)
  · have h := (hp (s / c) (hm hs)).comp s (hd s) hm
    exact h.congr_deriv (by field_simp)
  · have h := ((hq (s / c) (hm hs)).comp s (hd s) hm).div_const c
    exact h.congr_deriv (by field_simp)

theorem scale_lim {c : ℝ} (hc : 0 < c) {p : ℝ → ℝ} (h : Tendsto p atTop (𝓝 1)) :
    Tendsto (fun s => p (s / c)) atTop (𝓝 1) :=
  h.comp (tendsto_id.atTop_div_const hc)

lemma sqrt2_lt : Real.sqrt 2 < 1.4142135624 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
lemma lt_sqrt2 : (1.4142135623 : ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
lemma sqrt2_le' : Real.sqrt 2 ≤ 1.41421356237310 :=
  ((Real.sqrt_lt' (by norm_num)).mpr (by norm_num)).le
lemma le_sqrt2' : (1.41421356237309 : ℝ) ≤ Real.sqrt 2 :=
  ((Real.lt_sqrt (by norm_num)).mpr (by norm_num)).le

/-- Falkner–Skan β = 1/2 (Homann by the similarity scaling): there is a solution of
g''' + g g'' + (1 − g'²)/2 = 0 on [0, ∞), g(0) = g'(0) = 0, g' → 1, with g''(0) in
(0.927680039, 0.927680040). -/
theorem fs_half_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := by
  obtain ⟨f, p, q, hf, hp, hq, f0, p0, lim, lo, hi⟩ := Checked.Homann.homann_exists
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hc : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨A, B, C⟩ := scale hc hf hp hq'
  refine ⟨_, _, _, A, B, fun s hs => (C s hs).congr_deriv (by rw [h2]; ring), ?_, ?_,
    scale_lim hc lim, ?_, ?_⟩
  · simp [f0]
  · simp [p0]
  · show 0.927680039 < q (0 / Real.sqrt 2) / Real.sqrt 2
    rw [zero_div, lt_div_iff₀ hc]
    nlinarith [sqrt2_lt]
  · show q (0 / Real.sqrt 2) / Real.sqrt 2 < 0.927680040
    rw [zero_div, div_lt_iff₀ hc]
    nlinarith [lt_sqrt2]

/-- Falkner–Skan β = 0 (Blasius in the normalisation g''' + g g'' = 0): for every solution on
[0, ∞) with g(0) = g'(0) = 0 and g' → 1, the wall value g''(0) lies between 0.4695999883610
and 0.4695999883611. -/
theorem fs_zero_wall_shear (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.4695999883610 ≤ q 0 ∧ q 0 ≤ 0.4695999883611 := by
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 0 * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hc : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨A, B, C⟩ := scale hc hf hp hq'
  have key := Checked.Blasius.blasius_wall_shear _ _ _ A B
    (fun s hs => (C s hs).congr_deriv (by rw [h2]; ring)) (by simp [hf0]) (by simp [hp0])
    (scale_lim hc hlim)
  simp only [zero_div] at key
  obtain ⟨k1, k2⟩ := key
  have e : q 0 = Real.sqrt 2 * (q 0 / Real.sqrt 2) := by field_simp
  have hq0 : 0 ≤ q 0 / Real.sqrt 2 := le_trans (by norm_num) k1
  rw [e]
  constructor <;> nlinarith [sqrt2_le', le_sqrt2']

#print axioms fs_half_exists
#print axioms fs_zero_wall_shear

end FSScale
