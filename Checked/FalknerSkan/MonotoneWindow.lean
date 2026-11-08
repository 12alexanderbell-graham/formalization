import Checked.Hiemenz.Hiemenz
import Checked.Hiemenz.HIVP
import Checked.Homann.Homann
import Checked.Homann.HmIVP
import Checked.FalknerSkan.CroccoWindow
/-! Hiemenz and Homann stagnation-point flows: every solution of the boundary-value problem with positive second derivative on the closed half-line has its wall shear inside the window printed in the statements of `hiemenz_monotone_window` and `homann_monotone_window`, the ends of which are the certified shooting values. Module `MonotoneWindow`, promoted from `Work/FalknerSkan/MonotoneWindow.lean`. -/

namespace Checked.FalknerSkan.MonotoneWindow
open Set Filter Topology

/-- Hiemenz stagnation-point flow: every solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_monotone_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 1 + p η ^ 2) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  obtain ⟨g, u, v, hg, hu, hv, hg0, hu0, hv0⟩ := Checked.Hiemenz.HIVP.ivp_lo
  have hU := Checked.Hiemenz.hiemenz_under (15 / 2) le_rfl g u v hg hu hv hg0 hu0 hv0
  have hlo := Checked.FalknerSkan.CroccoWindow.ge_of_under zero_le_one hf hp hq1 hf0 hp0 hlim hpos
    hg hu (fun η hη => (hv η hη).congr_deriv (by ring)) hg0 hu0 hv0 hU
  obtain ⟨g', u', v', hg', hu', hv', hg0', hu0', hv0'⟩ := Checked.Hiemenz.HIVP.ivp_hi
  have hO := Checked.Hiemenz.hiemenz_over (15 / 2) le_rfl g' u' v' hg' hu' hv' hg0' hu0' hv0'
  have hhi := Checked.FalknerSkan.CroccoWindow.le_of_over zero_le_one hf hp hq1 hf0 hp0 hlim hpos
    hg' hu' (fun η hη => (hv' η hη).congr_deriv (by ring)) hg0' hu0' hv0' hO
  have hsub : Icc (0 : ℝ) (15 / 2) ⊆ Ici 0 := fun x hx => hx.1
  refine ⟨lt_of_le_of_ne hlo ?_, lt_of_le_of_ne hhi ?_⟩
  · intro h
    obtain ⟨η, hη, hneg, -⟩ := Checked.Hiemenz.hiemenz_under (15 / 2) le_rfl f p q
      (fun η hη => (hf η (hsub hη)).mono hsub) (fun η hη => (hp η (hsub hη)).mono hsub)
      (fun η hη => (hq η (hsub hη)).mono hsub) hf0 hp0 h.symm
    linarith [hpos η hη.1.le]
  · intro h
    obtain ⟨η, hη, hbig, -⟩ := Checked.Hiemenz.hiemenz_over (15 / 2) le_rfl f p q
      (fun η hη => (hf η (hsub hη)).mono hsub) (fun η hη => (hp η (hsub hη)).mono hsub)
      (fun η hη => (hq η (hsub hη)).mono hsub) hf0 hp0 h
    linarith [Checked.FalknerSkan.CroccoWindow.p_lt_one hp hlim hpos η hη.1.le]

/-- Homann axisymmetric stagnation-point flow: every solution of f''' + 2 f f'' + 1 − f'² = 0 on
[0, ∞) (f has derivative p, p has derivative q, q has derivative −2 f q − 1 + p², one-sided at 0)
with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on [0, ∞) has wall shear q(0) = f''(0)
strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_monotone_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  have hq1 := hq
  obtain ⟨g, u, v, hg, hu, hv, hg0, hu0, hv0⟩ := Checked.Homann.HmIVP.ivp_lo
  have hU := Checked.Homann.homann_under 6 le_rfl g u v hg hu hv hg0 hu0 hv0
  have hlo := Checked.FalknerSkan.CroccoWindow.ge_of_under zero_le_two hf hp hq1 hf0 hp0 hlim hpos
    hg hu hv hg0 hu0 hv0 hU
  obtain ⟨g', u', v', hg', hu', hv', hg0', hu0', hv0'⟩ := Checked.Homann.HmIVP.ivp_hi
  have hO := Checked.Homann.homann_over 6 le_rfl g' u' v' hg' hu' hv' hg0' hu0' hv0'
  have hhi := Checked.FalknerSkan.CroccoWindow.le_of_over zero_le_two hf hp hq1 hf0 hp0 hlim hpos
    hg' hu' hv' hg0' hu0' hv0' hO
  have hsub : Icc (0 : ℝ) 6 ⊆ Ici 0 := fun x hx => hx.1
  refine ⟨lt_of_le_of_ne hlo ?_, lt_of_le_of_ne hhi ?_⟩
  · intro h
    obtain ⟨η, hη, hneg, -⟩ := Checked.Homann.homann_under 6 le_rfl f p q
      (fun η hη => (hf η (hsub hη)).mono hsub) (fun η hη => (hp η (hsub hη)).mono hsub)
      (fun η hη => (hq η (hsub hη)).mono hsub) hf0 hp0 h.symm
    linarith [hpos η hη.1.le]
  · intro h
    obtain ⟨η, hη, hbig, -⟩ := Checked.Homann.homann_over 6 le_rfl f p q
      (fun η hη => (hf η (hsub hη)).mono hsub) (fun η hη => (hp η (hsub hη)).mono hsub)
      (fun η hη => (hq η (hsub hη)).mono hsub) hf0 hp0 h
    linarith [Checked.FalknerSkan.CroccoWindow.p_lt_one hp hlim hpos η hη.1.le]

end Checked.FalknerSkan.MonotoneWindow
