import Checked.FalknerSkan.Bounded
import Checked.FalknerSkan.HalfBounded
import Checked.FalknerSkan.FifthBounded
import Checked.FalknerSkan.LimitCore
/-! Falkner–Skan and stagnation-point boundary-value problems without any bound on the velocity profile: for a pressure-gradient coefficient in the half-open unit interval every solution has positive second derivative, and the window and equality theorems of the class bounded by one in absolute value hold for every solution of the boundary-value problem. Module `Limit`, promoted from `Work/FalknerSkan/Unrestricted.lean`. -/

namespace Checked.FalknerSkan.Limit
open Set Filter Topology Checked.FalknerSkan.LimitCore

/-- Falkner–Skan with pressure-gradient coefficient β, 0 < β ≤ 1: every solution of
f''' + f f'' + β (1 − f'²) = 0 on [0, ∞) (f has derivative p, p has derivative q, q has derivative
−f q − β (1 − p²), one-sided at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ has q(η) = f''(η)
positive for every η ≥ 0. -/
theorem fs_monotone_of_limit (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), 0 < q η := by
  have hc : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have hc2 : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ0.le
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc hf hp hq1
  have C' : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => q (s / Real.sqrt β) / Real.sqrt β)
      (-(1 / β * (Real.sqrt β * f (s / Real.sqrt β)) * (q (s / Real.sqrt β) / Real.sqrt β)) - 1 +
        p (s / Real.sqrt β) ^ 2) (Ici 0) s := by
    intro s hs
    refine (C s hs).congr_deriv ?_
    rw [hc2]; field_simp; ring
  have hK : 1 ≤ 1 / β := by rw [le_div_iff₀ hβ0]; linarith
  have hpos := q_pos hK A B C' (by simp [hf0]) (by simp [hp0])
    (Checked.FalknerSkan.FSScale.scale_lim hc hlim)
  intro η hη
  have h := hpos (η * Real.sqrt β) (mul_nonneg (show (0 : ℝ) ≤ η from hη) hc.le)
  simp only [mul_div_assoc, div_self hc.ne', mul_one] at h
  exact (div_pos_iff_of_pos_right hc).1 h

/-- Hiemenz stagnation-point flow: every solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞ has wall shear q(0) = f''(0) strictly between
1.2325876568 and 1.2325876569. -/
theorem hiemenz_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  have hb := in_class (K := 1) (by norm_num) hf hp
    (fun η hη => (hq η hη).congr_deriv (by ring)) hf0 hp0 hlim
  exact Checked.FalknerSkan.Bounded.hiemenz_bounded_window f p q hf hp hq hf0 hp0 hlim hb

/-- Hiemenz stagnation-point flow: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + 1 − f'² = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem hiemenz_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have hb := in_class (K := 1) (by norm_num) hf hp
    (fun η hη => (hq η hη).congr_deriv (by ring)) hf0 hp0 hlim
  have hb₂ := in_class (K := 1) (by norm_num) hf₂ hp₂
    (fun η hη => (hq₂ η hη).congr_deriv (by ring)) hf₂0 hp₂0 hlim₂
  exact Checked.FalknerSkan.Bounded.hiemenz_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

/-- Homann axisymmetric stagnation-point flow: every solution of f''' + 2 f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −2 f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞ has wall shear q(0) = f''(0) strictly between
1.3119376938 and 1.3119376939. -/
theorem homann_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  have hb := in_class (K := 2) (by norm_num) hf hp
    (fun η hη => (hq η hη).congr_deriv (by ring)) hf0 hp0 hlim
  exact Checked.FalknerSkan.Bounded.homann_bounded_window f p q hf hp hq hf0 hp0 hlim hb

/-- Homann axisymmetric stagnation-point flow: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + 2 f f'' + 1 − f'² = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem homann_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(2 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have hb := in_class (K := 2) (by norm_num) hf hp
    (fun η hη => (hq η hη).congr_deriv (by ring)) hf0 hp0 hlim
  have hb₂ := in_class (K := 2) (by norm_num) hf₂ hp₂
    (fun η hη => (hq₂ η hη).congr_deriv (by ring)) hf₂0 hp₂0 hlim₂
  exact Checked.FalknerSkan.Bounded.homann_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

/-- Falkner–Skan β = 1/2: every solution of f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −f q − (1 − p²)/2, one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞ has wall shear q(0) = f''(0) strictly between
0.927680039 and 0.927680040. -/
theorem fs_half_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.927680039 < q 0 ∧ q 0 < 0.927680040 := by
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim
      (fs_monotone_of_limit (1 / 2) (by norm_num) (by norm_num) f p q hf hp hq hf0 hp0 hlim) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  exact Checked.FalknerSkan.HalfBounded.fs_half_bounded_window f p q hf hp hq hf0 hp0 hlim hb

/-- Falkner–Skan β = 1/2: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + (1 − f'²)/2 = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem fs_half_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 2 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim
      (fs_monotone_of_limit (1 / 2) (by norm_num) (by norm_num) f p q hf hp hq hf0 hp0 hlim) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  have hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp₂ hp₂0 hlim₂
      (fs_monotone_of_limit (1 / 2) (by norm_num) (by norm_num) f₂ p₂ q₂ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  exact Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

/-- Falkner–Skan β = 1/5: every solution of f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞) (f has derivative p, p has
derivative q, q has derivative −f q − (1 − p²)/5, one-sided at 0) with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞ has wall shear q(0) = f''(0) strictly between
0.6867081809 and 0.6867081811. -/
theorem fs_fifth_limit_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1)) :
    0.6867081809 < q 0 ∧ q 0 < 0.6867081811 := by
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim
      (fs_monotone_of_limit (1 / 5) (by norm_num) (by norm_num) f p q hf hp hq hf0 hp0 hlim) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  exact Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_window f p q hf hp hq hf0 hp0 hlim hb

/-- Falkner–Skan β = 1/5: for every solution (f, p, q) and every solution (f₂, p₂, q₂) of
f''' + f f'' + (1 − f'²)/5 = 0 on [0, ∞) (derivatives one-sided at 0), both with f(0) = 0, p(0) = 0 and
p(η) → 1 as η → ∞: f η = f₂ η, p η = p₂ η and q η = q₂ η for every
η ≥ 0. -/
theorem fs_fifth_limit_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 / 5 * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 / 5 * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1)) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim
      (fs_monotone_of_limit (1 / 5) (by norm_num) (by norm_num) f p q hf hp hq hf0 hp0 hlim) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  have hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 := fun η hη => by
    have h := Checked.FalknerSkan.BoundedTools.bounded_of_pos hp₂ hp₂0 hlim₂
      (fs_monotone_of_limit (1 / 5) (by norm_num) (by norm_num) f₂ p₂ q₂ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂) η hη
    exact ⟨by linarith [h.1], h.2.le⟩
  exact Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

end Checked.FalknerSkan.Limit
