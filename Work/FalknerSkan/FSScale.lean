import Mathlib

/-! Falkner–Skan scaling (run 2026-11-08T0828Z): for c > 0, if (f, p, q) solves f' = p, p' = q,
q' = −a f q − b (1 − p²) within [0, ∞), then F(s) = c f(s/c), P(s) = p(s/c), Q(s) = q(s/c)/c
solves the same system with a/c² and b/c² in place of a and b (`scale`), and P has the same limit
at infinity (`scale_lim`). -/

namespace Work.FalknerSkan.FSScale
open Set Filter Topology

theorem mapsTo_div {c : ℝ} (hc : 0 < c) : MapsTo (fun s : ℝ => s / c) (Ici 0) (Ici 0) :=
  fun s hs => div_nonneg (mem_Ici.mp hs) hc.le

theorem hd {c : ℝ} (x : ℝ) : HasDerivWithinAt (fun s : ℝ => s / c) (1 / c) (Ici 0) x := by
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

/-- Rational bounds on √2 used to transfer the wall-shear windows. -/
theorem sqrt2_lt : Real.sqrt 2 < 1.4142135624 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem lt_sqrt2 : (1.4142135623 : ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
theorem sqrt2_le' : Real.sqrt 2 ≤ 1.41421356237310 :=
  ((Real.sqrt_lt' (by norm_num)).mpr (by norm_num)).le
theorem le_sqrt2' : (1.41421356237309 : ℝ) ≤ Real.sqrt 2 :=
  ((Real.lt_sqrt (by norm_num)).mpr (by norm_num)).le


end Work.FalknerSkan.FSScale
