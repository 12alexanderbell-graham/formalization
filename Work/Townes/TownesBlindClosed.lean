import Mathlib
import Work.Townes.TownesBlind
import Work.Townes.TownesShooting

/-!
# Townes shooting pair: the blind restatement, closed

The blind restater's statements `Blind.Townes.under` and `Blind.Townes.over` (run
2026-11-07T0228Z: two-sided derivatives on the open interval (0, 13.6), θ and θ' continuous on
[0, 13.6], θ'(0) = 0) follow from the program's frozen headlines
`Work.Townes.Shooting.townes_under` / `townes_over` (derivatives within [0, S], φ continuous at 0,
no assumption on φ(0)) with S = 13.6: the one-sided derivatives at the two ends come from
continuity of the derivative (`hasDerivWithinAt_Ici_of_tendsto_deriv` and its left version).
-/

namespace Work.Townes.BlindClosed
open Set Filter Topology

theorem left_end {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ r ∈ Ioo a b, HasDerivAt f (g r) r)
    (hc : ContinuousWithinAt f (Icc a b) a) (hg : ContinuousWithinAt g (Icc a b) a) :
    HasDerivWithinAt f (g a) (Icc a b) a := by
  have ht : Tendsto g (𝓝[>] a) (𝓝 (g a)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact hg.tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have h := hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo a b)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (hc.mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab)
    (ht.congr' (by filter_upwards [Ioo_mem_nhdsGT hab] with x hx using ((hd x hx).deriv).symm))
  exact h.mono Icc_subset_Ici_self

theorem right_end {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ r ∈ Ioo a b, HasDerivAt f (g r) r)
    (hc : ContinuousWithinAt f (Icc a b) b) (hg : ContinuousWithinAt g (Icc a b) b) :
    HasDerivWithinAt f (g b) (Icc a b) b := by
  have ht : Tendsto g (𝓝[<] b) (𝓝 (g b)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact hg.tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have h := hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo a b)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (hc.mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab)
    (ht.congr' (by filter_upwards [Ioo_mem_nhdsLT hab] with x hx using ((hd x hx).deriv).symm))
  exact h.mono Icc_subset_Iic_self

/-- The blind solution predicate gives the hypotheses of the program's headlines on [0, 13.6]. -/
theorem hyps (a : ℝ) (θ θ' : ℝ → ℝ) (h : Blind.Townes.IsSolution a θ θ') :
    (∀ r ∈ Icc (0 : ℝ) 13.6, HasDerivWithinAt θ (θ' r) (Icc 0 13.6) r) ∧
    ContinuousWithinAt θ' (Icc 0 13.6) 0 ∧
    (∀ r ∈ Ioc (0 : ℝ) 13.6,
      HasDerivWithinAt θ' (-(1 / r * θ' r) + θ r - θ r ^ 3) (Icc 0 13.6) r) ∧
    θ 0 = a := by
  obtain ⟨hd, hd', hc, hc', -, h0⟩ := h
  have hpos : (0 : ℝ) < 13.6 := by norm_num
  have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 13.6 := ⟨le_rfl, hpos.le⟩
  have mS : (13.6 : ℝ) ∈ Icc (0 : ℝ) 13.6 := ⟨hpos.le, le_rfl⟩
  refine ⟨fun r hr => ?_, hc' 0 m0, fun r hr => ?_, h0⟩
  · rcases eq_or_lt_of_le hr.1 with h1 | h1
    · subst h1; exact left_end hpos hd (hc 0 hr) (hc' 0 hr)
    rcases eq_or_lt_of_le hr.2 with h2 | h2
    · subst h2; exact right_end hpos hd (hc _ hr) (hc' _ hr)
    · exact (hd r ⟨h1, h2⟩).hasDerivWithinAt
  · set G : ℝ → ℝ := fun x => -(1 / x * θ' x) + θ x - θ x ^ 3 with hG
    have hd2 : ∀ x ∈ Ioo (0 : ℝ) 13.6, HasDerivAt θ' (G x) x := fun x hx => by
      have := hd' x hx
      convert this using 1
      simp only [hG]
      ring
    rcases eq_or_lt_of_le hr.2 with h2 | h2
    · subst h2
      have hGc : ContinuousWithinAt G (Icc 0 13.6) 13.6 := by
        simp only [hG]
        exact (((continuousWithinAt_const.div continuousWithinAt_id (by norm_num)).mul
          (hc' _ mS)).neg.add (hc _ mS)).sub ((hc _ mS).pow 3)
      exact right_end hpos hd2 (hc' _ mS) hGc
    · exact (hd2 r ⟨hr.1, h2⟩).hasDerivWithinAt

/-- The blind undershoot statement follows from `Work.Townes.Shooting.townes_under`. -/
theorem blind_under (θ θ' : ℝ → ℝ) (h : Blind.Townes.IsSolution 2.2062008646 θ θ') :
    ∃ r : ℝ, 0 < r ∧ r ≤ 13.6 ∧ 0 < θ' r ∧ ∀ s ∈ Set.Icc (0 : ℝ) r, 0 < θ s := by
  obtain ⟨hθ, hφ0, hφ, h0⟩ := hyps _ θ θ' h
  obtain ⟨r, hr, hp, hall⟩ :=
    Work.Townes.Shooting.townes_under 13.6 (by norm_num) θ θ' hθ hφ0 hφ h0
  exact ⟨r, hr.1, hr.2.trans (by norm_num), hp, hall⟩

/-- The blind overshoot statement follows from `Work.Townes.Shooting.townes_over`. -/
theorem blind_over (θ θ' : ℝ → ℝ) (h : Blind.Townes.IsSolution 2.2062008647 θ θ') :
    ∃ r : ℝ, 0 < r ∧ r ≤ 13.6 ∧ θ r < 0 ∧ ∀ s ∈ Set.Ioc (0 : ℝ) r, θ' s < 0 := by
  obtain ⟨hθ, hφ0, hφ, h0⟩ := hyps _ θ θ' h
  obtain ⟨r, hr, hn, hall⟩ :=
    Work.Townes.Shooting.townes_over 13.6 (by norm_num) θ θ' hθ hφ0 hφ h0
  exact ⟨r, hr.1, hr.2.trans (by norm_num), hn, hall⟩

end Work.Townes.BlindClosed
