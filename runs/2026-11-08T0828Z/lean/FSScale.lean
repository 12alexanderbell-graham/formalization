import Mathlib

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

end FSScale
