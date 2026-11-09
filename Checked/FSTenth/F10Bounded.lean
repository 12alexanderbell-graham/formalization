import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Checked.FalknerSkan.MonotoneExists
import Checked.FalknerSkan.BoundedTools
import Checked.FSTenth.FSTenth
import Checked.FSTenth.F10IVP
import Checked.FSTenth.F10ExMono
/-! Falkner–Skan one-tenth row, the coefficient-ten problem in the class where the velocity profile is bounded by one in absolute value: window, equality of two solutions and existence by the Crocco comparison and the shooting construction. Module `F10Bounded`, promoted from `Work/FSTenth/F10Bounded.lean`. -/

namespace Checked.FSTenth.F10Bounded
open Set Filter Topology

/-- Coefficient 10 (Falkner–Skan β = 1/10 scaled): every solution of f''' + 10 f f'' + 1 − f'² = 0 on
[0, ∞) (f has derivative p, p has derivative q, q has derivative −10 f q − 1 + p², one-sided at 0)
with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 1.8563683593 and 1.8563683595. -/
theorem k10_monotone_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(10 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    1.8563683593 < q 0 ∧ q 0 < 1.8563683595 := by
  have hq1 := hq
  obtain ⟨g, u, v, hg, hu, hv, hg0, hu0, hv0⟩ := Checked.FSTenth.F10IVP.ivp_lo
  have hU := Checked.FSTenth.k10_under 3 le_rfl g u v hg hu hv hg0 hu0 hv0
  have hlo := Checked.FalknerSkan.CroccoWindow.ge_of_under (by norm_num : (0:ℝ) ≤ 10) hf hp hq1 hf0 hp0 hlim hpos
    hg hu hv hg0 hu0 hv0 hU
  obtain ⟨g', u', v', hg', hu', hv', hg0', hu0', hv0'⟩ := Checked.FSTenth.F10IVP.ivp_hi
  have hO := Checked.FSTenth.k10_over 3 le_rfl g' u' v' hg' hu' hv' hg0' hu0' hv0'
  have hhi := Checked.FalknerSkan.CroccoWindow.le_of_over (by norm_num : (0:ℝ) ≤ 10) hf hp hq1 hf0 hp0 hlim hpos
    hg' hu' hv' hg0' hu0' hv0' hO
  have hsub : Icc (0 : ℝ) 3 ⊆ Ici 0 := fun x hx => hx.1
  refine ⟨lt_of_le_of_ne hlo ?_, lt_of_le_of_ne hhi ?_⟩
  · intro h
    obtain ⟨η, hη, hneg, -⟩ := Checked.FSTenth.k10_under 3 le_rfl f p q
      (fun η hη => (hf η (hsub hη)).mono hsub) (fun η hη => (hp η (hsub hη)).mono hsub)
      (fun η hη => (hq η (hsub hη)).mono hsub) hf0 hp0 h.symm
    linarith [hpos η hη.1.le]
  · intro h
    obtain ⟨η, hη, hbig, -⟩ := Checked.FSTenth.k10_over 3 le_rfl f p q
      (fun η hη => (hf η (hsub hη)).mono hsub) (fun η hη => (hp η (hsub hη)).mono hsub)
      (fun η hη => (hq η (hsub hη)).mono hsub) hf0 hp0 h
    linarith [Checked.FalknerSkan.CroccoWindow.p_lt_one hp hlim hpos η hη.1.le]

/-- Coefficient 10 (Falkner–Skan β = 1/10 scaled): there is a solution of f''' + 10 f f'' + 1 − f'² = 0
on [0, ∞) (f has derivative p, p has derivative q, q has derivative −10 f q − 1 + p², one-sided at
0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, q > 0 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 1.8563683593 and 1.8563683595. -/
theorem k10_exists_monotone : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(10 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
    1.8563683593 < q 0 ∧ q 0 < 1.8563683595 := by
  exact Checked.FSTenth.F10ExMono.exists_bvp_pos

/-- Coefficient 10 (Falkner–Skan β = 1/10 scaled): every solution of f''' + 10 f f'' + 1 − f'² = 0 on
[0, ∞) (f has derivative p, p has derivative q, q has derivative −10 f q − 1 + p², one-sided at 0)
with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and −1 ≤ p ≤ 1 on [0, ∞) has wall shear
q(0) = f''(0) strictly between 1.8563683593 and 1.8563683595. -/
theorem k10_bounded_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(10 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) :
    1.8563683593 < q 0 ∧ q 0 < 1.8563683595 := by
  exact k10_monotone_window f p q hf hp hq hf0 hp0 hlim
    (Checked.FalknerSkan.BoundedTools.pos_of_abs_le hf hp hq hp0 hlim hb)

/-- Coefficient 10: two solutions in the class −1 ≤ p ≤ 1 are equal. -/
theorem k10_bounded_equal (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(10 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(10 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hb₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have hpos := Checked.FalknerSkan.BoundedTools.pos_of_abs_le hf hp hq hp0 hlim hb
  have hpos₂ := Checked.FalknerSkan.BoundedTools.pos_of_abs_le hf₂ hp₂ hq₂ hp₂0 hlim₂ hb₂
  have hw : q 0 = q₂ 0 := le_antisymm
    (not_lt.1 (Checked.FalknerSkan.MonotoneExists.not_lt_wall (by norm_num : (0:ℝ) ≤ 10) hf₂ hp₂ hq₂ hf₂0 hp₂0
      hlim₂ hpos₂ hf hp hq hf0 hp0 hlim hpos))
    (not_lt.1 (Checked.FalknerSkan.MonotoneExists.not_lt_wall (by norm_num : (0:ℝ) ≤ 10) hf hp hq hf0 hp0 hlim
      hpos hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂))
  exact Checked.FalknerSkan.BoundedTools.eq_of_start hf hp hq hf₂ hp₂ hq₂ (hf0.trans hf₂0.symm) (hp0.trans hp₂0.symm) hw

/-- Coefficient 10 (Falkner–Skan β = 1/10 scaled): there is a solution of f''' + 10 f f'' + 1 − f'² = 0
on [0, ∞) (f has derivative p, p has derivative q, q has derivative −10 f q − 1 + p², one-sided at
0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, 0 ≤ p < 1 on [0, ∞), and wall shear
q(0) = f''(0) strictly between 1.8563683593 and 1.8563683595. -/
theorem k10_exists_bounded : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(10 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1) ∧
    1.8563683593 < q 0 ∧ q 0 < 1.8563683595 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hlo, hhi⟩ :=
    k10_exists_monotone
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, Checked.FalknerSkan.BoundedTools.bounded_of_pos hp hp0 hlim hpos, hlo, hhi⟩

end Checked.FSTenth.F10Bounded
