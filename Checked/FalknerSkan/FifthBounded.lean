import Checked.FalknerSkan.FSScale
import Checked.FSFifth.F5Bounded
/-! Falkner–Skan wedge flow with pressure-gradient coefficient one fifth: every solution of the boundary-value problem whose velocity profile is bounded by one in absolute value on the closed half-line has its wall shear inside the window of the statement, any two such solutions are equal on the closed half-line, and a solution with velocity profile in the half-open unit interval exists; obtained from the coefficient-five theorems of `Checked.FSFifth.F5Bounded` by the similarity scaling of `Checked.FalknerSkan.FSScale`. Module `FifthBounded`, promoted from `Work/FalknerSkan/FifthBounded.lean`. -/

namespace Checked.FalknerSkan.FifthBounded
open Set Filter Topology Checked.FalknerSkan.FSScale

theorem sqrt5_lt : Real.sqrt 5 < 2.2360679776 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem lt_sqrt5 : (2.2360679774 : ℝ) < Real.sqrt 5 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

theorem to_k5 {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η) :
    let c := 1 / Real.sqrt 5
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => c * f (s / c)) (p (s / c)) (Ici 0) s) ∧
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => p (s / c)) (q (s / c) / c) (Ici 0) s) ∧
    (∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => q (s / c) / c)
      (-(5 * (c * f (s / c)) * (q (s / c) / c)) - 1 + p (s / c) ^ 2) (Ici 0) s) := by
  intro c
  have hc : 0 < c := by positivity
  have hc2 : c ^ 2 = 1 / 5 := by
    simp only [c, div_pow, one_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have hq' : ∀ η ∈ Ici (0 : ℝ),
      HasDerivWithinAt q (-(1 * f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := scale hc hf hp hq'
  refine ⟨A, B, fun s hs => (C s hs).congr_deriv ?_⟩
  rw [hc2]; ring

/-- Falkner–Skan β = 1/5: every solution of f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞) (f has
derivative p, p has derivative q, q has derivative −f q − (1 − p²)/5, one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 0.6867081809 and 0.6867081811. -/
theorem fs_fifth_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    0.6867081809 < q 0 ∧ q 0 < 0.6867081811 := by
  obtain ⟨A, B, C⟩ := to_k5 hf hp hq
  set c := 1 / Real.sqrt 5 with hcdef
  have hc : 0 < c := by positivity
  have hmap : ∀ s ∈ Ici (0 : ℝ), s / c ∈ Ici (0 : ℝ) := fun s hs => mapsTo_div hc hs
  have W := Checked.FSFifth.F5Bounded.k5_bounded_window _ _ _ A B C
    (by simp [hf0]) (by simp [hp0]) (scale_lim hc hlim) (fun s hs => hb _ (hmap s hs))
  simp only [zero_div] at W
  have hs2 : Real.sqrt 5 * c = 1 := by
    rw [hcdef]; field_simp
  have hq0 : q 0 / c = Real.sqrt 5 * q 0 := by
    rw [div_eq_iff hc.ne']; linear_combination (-(q 0)) * hs2
  rw [hq0] at W
  have hpos : 0 < Real.sqrt 5 := by positivity
  constructor
  · nlinarith [sqrt5_lt, W.1]
  · nlinarith [lt_sqrt5, W.2]

/-- Falkner–Skan β = 1/5: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0,
p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞): f η = f₂ η, p η = p₂ η and q η = q₂ η for
every η ≥ 0. -/
theorem fs_fifth_bounded_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 5 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  obtain ⟨A, B, C⟩ := to_k5 hf hp hq
  obtain ⟨A₂, B₂, C₂⟩ := to_k5 hf₂ hp₂ hq₂
  set c := 1 / Real.sqrt 5 with hcdef
  have hc : 0 < c := by positivity
  have hmap : ∀ s ∈ Ici (0 : ℝ), s / c ∈ Ici (0 : ℝ) := fun s hs => mapsTo_div hc hs
  have U := Checked.FSFifth.F5Bounded.k5_bounded_equal _ _ _ _ _ _ A B C
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

/-- Falkner–Skan β = 1/5: there is a solution of f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − (1 − p²)/5, one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 0.6867081809 and 0.6867081811. -/
theorem fs_fifth_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    0.6867081809 < q 0 ∧ q 0 < 0.6867081811 := by
  obtain ⟨f, p, q, hf, hp, hq, f0, p0, lim, hb, lo, hi⟩ :=
    Checked.FSFifth.F5Bounded.k5_exists_bounded
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(5 * f η * q η) - 1 * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hc : (0 : ℝ) < Real.sqrt 5 := by positivity
  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  obtain ⟨A, B, C⟩ := scale hc hf hp hq'
  refine ⟨_, _, _, A, B, fun s hs => (C s hs).congr_deriv (by rw [h2]; ring), ?_, ?_,
    scale_lim hc lim, fun s hs => hb _ (mapsTo_div hc hs), ?_, ?_⟩
  · simp [f0]
  · simp [p0]
  · show 0.6867081809 < q (0 / Real.sqrt 5) / Real.sqrt 5
    rw [zero_div, lt_div_iff₀ hc]
    nlinarith [sqrt5_lt]
  · show q (0 / Real.sqrt 5) / Real.sqrt 5 < 0.6867081811
    rw [zero_div, div_lt_iff₀ hc]
    nlinarith [lt_sqrt5]

end Checked.FalknerSkan.FifthBounded
