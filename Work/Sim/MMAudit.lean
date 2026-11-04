import Mathlib
import Work.Sim.MichaelisMenten
import Work.Sim.MMBlind
import Work.Fidelity.MMSpec

/-!
# Audit of the Michaelis–Menten half-conversion statements (run 2026-11-04T0828Z)

1. The blind restatement (`Work/Sim/MMBlind.lean`, written from the problem in words, without
   seeing the frozen file) is equivalent in content: its predicate equals the program's
   `IsMMSolution 1 1 1 1 1 0 0` (same equations up to ring normalisation, same one-sided
   derivative convention, same initial values), and both blind claims are closed in Lean from the
   program's theorems (`blind_claimA`, `blind_claimB`).
2. The program's `IsMMSolution` meets the blind specification `MMSpec`
   (`Work/Fidelity/MMSpec.lean`, written without seeing the definition): `isMM_meets`.
-/

namespace Work.Sim.MMAudit
open Set

theorem blind_iff (s e c p : ℝ → ℝ) (T : ℝ) :
    Work.Sim.MMBlind.IsMMSolution s e c p T ↔
      Work.Sim.MichaelisMenten.IsMMSolution 1 1 1 1 1 0 0 T s e c p := by
  unfold Work.Sim.MMBlind.IsMMSolution Work.Sim.MichaelisMenten.IsMMSolution
  constructor <;> rintro ⟨h1, h2, h3, h4, hd⟩ <;> refine ⟨h1, h2, h3, h4, fun t ht => ?_⟩ <;>
    obtain ⟨d1, d2, d3, d4⟩ := hd t ht <;>
    exact ⟨d1.congr_deriv (by ring), d2.congr_deriv (by ring), d3.congr_deriv (by ring),
      d4.congr_deriv (by ring)⟩

theorem blind_claimA (s e c p : ℝ → ℝ)
    (h : Work.Sim.MMBlind.IsMMSolution s e c p (26 / 10)) :
    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) := by
  rw [blind_iff, show (26 / 10 : ℝ) = 13 / 5 by norm_num] at h
  exact Work.Sim.MichaelisMenten.mm_half_conversion h

theorem blind_claimB : ∃ s e c p : ℝ → ℝ, Work.Sim.MMBlind.IsMMSolution s e c p (26 / 10) := by
  obtain ⟨s, e, c, p, h⟩ := Work.Sim.MichaelisMenten.mm_solution_exists
  exact ⟨s, e, c, p, by rw [blind_iff, show (26 / 10 : ℝ) = 13 / 5 by norm_num]; exact h⟩

theorem isMM_eq_ref :
    Work.Sim.MichaelisMenten.IsMMSolution = Work.Fidelity.MMSpec.refMM := by
  funext k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p
  unfold Work.Sim.MichaelisMenten.IsMMSolution Work.Fidelity.MMSpec.refMM
  have e1 : ∀ t, -k₁ * e t * s t + km₁ * c t = -(k₁ * e t * s t) + km₁ * c t := fun t => by ring
  have e2 : ∀ t, -k₁ * e t * s t + (km₁ + k₂) * c t = -(k₁ * e t * s t) + (km₁ + k₂) * c t :=
    fun t => by ring
  simp only [e1, e2]

/-- The program's definition meets the blind specification. -/
theorem isMM_meets : Work.Fidelity.MMSpec.MMSpec Work.Sim.MichaelisMenten.IsMMSolution := by
  rw [isMM_eq_ref]; exact Work.Fidelity.MMSpec.refMM_meets

/-- Corollary (referee correction 1, run 2026-11-04T0828Z): the product of every solution first
reaches half conversion at a time strictly between 2.5665 and 2.5666 — there is τ in that interval
with [P](τ) = 1/2 and [P] < 1/2 on [0, τ). -/
theorem first_half_conversion {s e c p : ℝ → ℝ}
    (h : Work.Sim.MichaelisMenten.IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :
    ∃ τ ∈ Ioo (25665 / 10000 : ℝ) (25666 / 10000), p τ = 1 / 2 ∧
      ∀ t ∈ Ico (0 : ℝ) τ, p t < 1 / 2 := by
  have hsign := Work.Sim.MichaelisMenten.mm_half_conversion h
  obtain ⟨-, -, -, -, hd⟩ := h
  set lo : ℝ := 25665 / 10000
  set hi : ℝ := 25666 / 10000
  have hlo : lo < hi := by norm_num [lo, hi]
  have hsub : Icc lo hi ⊆ Icc 0 (13 / 5) := Icc_subset_Icc (by norm_num [lo]) (by norm_num [hi])
  have hcont : ContinuousOn p (Icc lo hi) := fun t ht =>
    ((hd t (hsub ht)).2.2.2.continuousWithinAt).mono hsub
  have hplo : p lo < 1 / 2 := hsign.1 lo ⟨by norm_num [lo], le_rfl⟩
  set Z := {t ∈ Icc lo hi | p t = 1 / 2} with hZ
  have hZc : IsClosed Z := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hlo.le hcont ⟨hplo.le, hsign.2.le⟩
    exact ⟨c, hc, hc0⟩
  have hZb : BddBelow Z := ⟨lo, fun t ht => ht.1.1⟩
  set τ := sInf Z
  have hτ : τ ∈ Z := hZc.csInf_mem hZne hZb
  have hτne_lo : τ ≠ lo := fun h => by have := hτ.2; rw [h] at this; linarith
  have hτne_hi : τ ≠ hi := fun h => by have := hτ.2; rw [h] at this; linarith [hsign.2]
  refine ⟨τ, ⟨lt_of_le_of_ne hτ.1.1 (Ne.symm hτne_lo), lt_of_le_of_ne hτ.1.2 hτne_hi⟩, hτ.2,
    fun t ht => ?_⟩
  rcases le_total t lo with h | h
  · exact hsign.1 t ⟨ht.1, h⟩
  · by_contra hneg
    push Not at hneg
    have hsub2 : Icc lo t ⊆ Icc lo hi := Icc_subset_Icc le_rfl (ht.2.le.trans hτ.1.2)
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc h (hcont.mono hsub2) ⟨hplo.le, hneg⟩
    have hcZ : c ∈ Z := ⟨hsub2 hc, hc0⟩
    have := csInf_le hZb hcZ
    linarith [hc.2, ht.2]

end Work.Sim.MMAudit
