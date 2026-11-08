import Work.FalknerSkan.Bounded
import Checked.FalknerSkan.FSScale

/-! Scratch (run 2026-11-08T1228Z), next step 2: the Falkner–Skan β = 1/2 row in the class
−1 ≤ f' ≤ 1, from the Homann bounded-class theorems by the scaling F(s) = c f(s/c), c = 1/√2. -/

namespace Scratch1228FS
open Set Filter Topology Checked.FalknerSkan.FSScale

theorem to_homann {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η) :
    let c := 1 / Real.sqrt 2
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => c * f (s / c)) (p (s / c)) (Ici 0) s) ∧
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => p (s / c)) (q (s / c) / c) (Ici 0) s) ∧
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => q (s / c) / c)
      (-(2 * (c * f (s / c)) * (q (s / c) / c)) - 1 + p (s / c) ^ 2) (Ici 0) s) := by
  intro c
  have hc : 0 < c := by positivity
  have hc2 : c ^ 2 = 1 / 2 := by
    simp only [c, div_pow, one_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hq' : ∀ η ∈ Ici (0 : ℝ),
      HasDerivWithinAt q (-(1 * f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := scale hc hf hp hq'
  refine ⟨A, B, fun s hs => (C s hs).congr_deriv ?_⟩
  rw [hc2]; ring

/-- Falkner–Skan β = 1/2: every solution of f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1 and −1 ≤ p ≤ 1 on [0, ∞) has q(0) strictly between 0.927680039 and
0.927680040. -/
theorem fs_half_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := by
  obtain ⟨A, B, C⟩ := to_homann hf hp hq
  set c := 1 / Real.sqrt 2 with hcdef
  have hc : 0 < c := by positivity
  have hmap : ∀ s ∈ Ici (0 : ℝ), s / c ∈ Ici (0 : ℝ) := fun s hs => mapsTo_div hc hs
  have W := Work.FalknerSkan.Bounded.homann_bounded_window _ _ _ A B C
    (by simp [hf0]) (by simp [hp0]) (scale_lim hc hlim) (fun s hs => hb _ (hmap s hs))
  simp only [zero_div] at W
  have hs2 : Real.sqrt 2 * c = 1 := by
    rw [hcdef]; field_simp
  have hq0 : q 0 / c = Real.sqrt 2 * q 0 := by
    rw [div_eq_iff hc.ne']; linear_combination (-(q 0)) * hs2
  rw [hq0] at W
  have hpos : 0 < Real.sqrt 2 := by positivity
  constructor
  · nlinarith [sqrt2_lt, W.1]
  · nlinarith [lt_sqrt2, W.2]

/-- Falkner–Skan β = 1/2: any two solutions of f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1 and −1 ≤ p ≤ 1 on [0, ∞) are equal on [0, ∞). -/
theorem fs_half_bounded_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 2 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  obtain ⟨A, B, C⟩ := to_homann hf hp hq
  obtain ⟨A₂, B₂, C₂⟩ := to_homann hf₂ hp₂ hq₂
  set c := 1 / Real.sqrt 2 with hcdef
  have hc : 0 < c := by positivity
  have hmap : ∀ s ∈ Ici (0 : ℝ), s / c ∈ Ici (0 : ℝ) := fun s hs => mapsTo_div hc hs
  have U := Work.FalknerSkan.Bounded.homann_bounded_equal _ _ _ _ _ _ A B C
    (by simp [hf0]) (by simp [hp0]) (scale_lim hc hlim) (fun s hs => hb _ (hmap s hs))
    A₂ B₂ C₂ (by simp [hf₂0]) (by simp [hp₂0]) (scale_lim hc hlim₂)
    (fun s hs => hb₂ _ (hmap s hs))
  intro η hη
  have hη0 : (0 : ℝ) ≤ η := hη
  have hs : η * c ∈ Ici (0 : ℝ) := Set.mem_Ici.2 (mul_nonneg hη0 hc.le)
  obtain ⟨u1, u2, u3⟩ := U (η * c) hs
  simp only [mul_div_assoc, div_self hc.ne', mul_one] at u1 u2 u3
  refine ⟨?_, u2, ?_⟩
  · exact mul_left_cancel₀ hc.ne' u1
  · exact (div_left_inj' hc.ne').1 u3

end Scratch1228FS
