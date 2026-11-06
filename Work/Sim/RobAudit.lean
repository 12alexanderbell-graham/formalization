import Work.Sim.RobBlind
import Work.Sim.Robertson

/-!
# Robertson at t = 40: blind restatement closed

The two statements of the blind restatement (`Work.Sim.RobBlind`, Sonnet, run
2026-11-06T0428Z, from the source alone) proved from the program's frozen theorems
`Work.Sim.Robertson.rob_state40` and `Work.Sim.Robertson.rob_exists`. The blind reading asks for
two-sided derivatives on the open interval only (plus continuity on the closed one); the
program's one-sided endpoint derivatives follow from the limit of the derivative.
-/

namespace Work.Sim.RobAudit
open Set Filter Topology

/-- Derivatives within [a, b] at every point of [a, b] from continuity on [a, b] and
two-sided derivatives on (a, b), when the derivative is continuous on [a, b]. -/

theorem within_Icc_of_interior {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ContinuousOn f' (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t := by
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ Ioo a b, deriv f t = f' t := fun t ht => (hd t ht).deriv
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h1 | h1
  · subst h1
    have lim : Tendsto (fun x => deriv f x) (𝓝[>] a) (𝓝 (f' a)) := by
      have e : 𝓝[>] a = 𝓝[Ioo a b] a := (nhdsWithin_Ioo_eq_nhdsGT hab).symm
      rw [e]
      have c := ((hf' a ht).mono (Ioo_subset_Icc_self)).tendsto
      exact c.congr' (eventually_nhdsWithin_of_forall fun x hx => (hderiv x hx).symm)
    have := hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
      ((hf a ht).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab) lim
    exact this.mono Icc_subset_Ici_self
  rcases eq_or_lt_of_le ht.2 with h2 | h2
  · subst h2
    have lim : Tendsto (fun x => deriv f x) (𝓝[<] t) (𝓝 (f' t)) := by
      have e : 𝓝[<] t = 𝓝[Ioo a t] t := (nhdsWithin_Ioo_eq_nhdsLT hab).symm
      rw [e]
      have c := ((hf' t ht).mono (Ioo_subset_Icc_self)).tendsto
      exact c.congr' (eventually_nhdsWithin_of_forall fun x hx => (hderiv x hx).symm)
    have := hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
      ((hf t ht).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab) lim
    exact this.mono Icc_subset_Iic_self
  exact (hd t ⟨h1, h2⟩).hasDerivWithinAt

theorem blind_state40 (y₁ y₂ y₃ : ℝ → ℝ) (h : Work.Sim.RobBlind.Solves y₁ y₂ y₃ 40) :
    (7158270/10000000 : ℝ) < y₁ 40 ∧ y₁ 40 < 7158271/10000000 ∧
    (91855/10000000000 : ℝ) < y₂ 40 ∧ y₂ 40 < 91856/10000000000 ∧
    (2841637/10000000 : ℝ) < y₃ 40 ∧ y₃ 40 < 2841638/10000000 := by
  obtain ⟨c1, c2, c3, h1, h2, h3, hd⟩ := h
  have hab : (0 : ℝ) < 40 := by norm_num
  have d1 := within_Icc_of_interior (f' := fun t => -(1 / 25 : ℝ) * y₁ t + 10000 * y₂ t * y₃ t)
    hab c1 (by fun_prop) (fun t ht => by
      have := (hd t ht).1; convert this using 1; norm_num)
  have d2 := within_Icc_of_interior
    (f' := fun t => (1 / 25 : ℝ) * y₁ t - 10000 * y₂ t * y₃ t - 30000000 * y₂ t ^ 2)
    hab c2 (by fun_prop) (fun t ht => by
      have := (hd t ht).2.1; convert this using 1; norm_num)
  have d3 := within_Icc_of_interior (f' := fun t => 30000000 * y₂ t ^ 2)
    hab c3 (by fun_prop) (fun t ht => (hd t ht).2.2)
  have hR : Work.Sim.Robertson.IsRobSolution (1 / 25) 10000 30000000 1 0 0 40 y₁ y₂ y₃ :=
    ⟨h1, h2, h3, fun t ht => ⟨by simpa using d1 t ht, d2 t ht, d3 t ht⟩⟩
  exact Work.Sim.Robertson.rob_state40 hR

theorem blind_exists : ∃ y₁ y₂ y₃ : ℝ → ℝ, Work.Sim.RobBlind.Solves y₁ y₂ y₃ 40 := by
  obtain ⟨y₁, y₂, y₃, h1, h2, h3, hd⟩ := Work.Sim.Robertson.rob_exists
  refine ⟨y₁, y₂, y₃, fun t ht => (hd t ht).1.continuousWithinAt,
    fun t ht => (hd t ht).2.1.continuousWithinAt, fun t ht => (hd t ht).2.2.continuousWithinAt,
    h1, h2, h3, fun t ht => ?_⟩
  have hn : Icc (0 : ℝ) 40 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have ht' : t ∈ Icc (0 : ℝ) 40 := Ioo_subset_Icc_self ht
  refine ⟨?_, ?_, ?_⟩
  · have := ((hd t ht').1).hasDerivAt hn
    convert this using 1; norm_num
  · have := ((hd t ht').2.1).hasDerivAt hn
    convert this using 1; norm_num
  · exact ((hd t ht').2.2).hasDerivAt hn

end Work.Sim.RobAudit
