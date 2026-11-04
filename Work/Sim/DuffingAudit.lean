import Work.Sim.Duffing
import Work.Sim.DuffingBlind
import Work.Fidelity.DuffingSpec

/-!
# Audit of `Work.Sim.Duffing`: the blind restatement closed in Lean

The blind restater (run 2026-11-04T0628Z, `DuffingBlind.lean`, written from the claim alone)
chose derivatives *within* [0, 1.2] (one-sided at the endpoints), a weaker hypothesis than the
frozen `IsDuffingIVP` (two-sided). Its main theorem and its existence theorem follow from the
program's core theorem `first_zero_within` and from `duffing_exists`; its corollary
`first_zero_mem` (the earliest zero lies in (1.192005, 1.192006)) is closed by IVT and a
compact infimum; `first_zero_unique` is not closed here. Also: `IsDuffingIVP` meets the blind
spec `DuffingSpec`, and the result holds for every function meeting that spec.
-/

namespace Work.Sim.DuffingAudit
open Set Work.Sim.DuffingBlind

theorem blind_pos_then_neg_closed (x : ℝ → ℝ) (hx : SolvesIVP horizon x) :
    (∀ t ∈ Icc (0 : ℝ) tLo, 0 < x t) ∧ x tHi < 0 := by
  obtain ⟨v, hx0, hv0, hdx, hdv⟩ := hx
  unfold tLo tHi
  unfold horizon at hdx hdv
  exact Work.Sim.Duffing.first_zero_within hx0 hv0 fun t ht =>
    ⟨hdx t ht, by convert hdv t ht using 1; ring⟩

theorem blind_exists_closed : ∃ x : ℝ → ℝ, SolvesIVP horizon x := by
  obtain ⟨x, hx0, v, hv0, hd⟩ := Work.Sim.Duffing.duffing_exists
  refine ⟨x, v, hx0, hv0, fun t ht => (hd t ht).1.hasDerivWithinAt, fun t ht => ?_⟩
  convert (hd t ht).2.hasDerivWithinAt using 1; ring

/-- `IsDuffingIVP` meets the blind spec (`DuffingSpec`, written without seeing the definition). -/
theorem isDuffingIVP_meets {k β x₀ v₀ T : ℝ} {x : ℝ → ℝ}
    (h : Work.Sim.Duffing.IsDuffingIVP k β x₀ v₀ T x) :
    Work.Fidelity.DuffingSpec.DuffingSpec k β x₀ v₀ T x := by
  obtain ⟨hx0, v, hv0, hd⟩ := h
  refine Work.Fidelity.DuffingSpec.refIVP_spec ⟨hx0, v, hv0, fun t ht =>
    ⟨(hd t ht).1.hasDerivWithinAt, ?_⟩⟩
  convert (hd t ht).2.hasDerivWithinAt using 1; ring

/-- The certified first-zero bounds hold for every function meeting the blind spec
(the spec is the textbook IVP with derivatives within [0, T]); this is the statement a pin of
the definition would give. -/
theorem first_zero_of_spec {x : ℝ → ℝ}
    (hx : Work.Fidelity.DuffingSpec.DuffingSpec 1 1 1 0 (6 / 5) x) :
    (∀ t ∈ Icc (0 : ℝ) (1192005 / 1000000), 0 < x t) ∧ x (1192006 / 1000000) < 0 := by
  obtain ⟨hx0, v, hv0, hd⟩ := Work.Fidelity.DuffingSpec.spec_refIVP hx
  exact Work.Sim.Duffing.first_zero_within hx0 hv0 fun t ht =>
    ⟨(hd t ht).1, by convert (hd t ht).2 using 1; ring⟩

/-- The blind corollary: the earliest zero lies in (1.192005, 1.192006). -/
theorem blind_first_zero_mem_closed (x : ℝ → ℝ) (hx : SolvesIVP horizon x) :
    ∃ τ ∈ Ioo tLo tHi, x τ = 0 ∧ ∀ t ∈ Ico (0 : ℝ) τ, 0 < x t := by
  have hsign := blind_pos_then_neg_closed x hx
  obtain ⟨v, -, -, hdx, -⟩ := hx
  have hlo : tLo < tHi := by unfold tLo tHi; norm_num
  have hsub : Icc tLo tHi ⊆ Icc 0 horizon := Icc_subset_Icc (by unfold tLo; norm_num)
    (by unfold tHi horizon; norm_num)
  have hcont : ContinuousOn x (Icc tLo tHi) := fun t ht =>
    ((hdx t (hsub ht)).continuousWithinAt).mono hsub
  have hxlo : 0 < x tLo := hsign.1 tLo ⟨by unfold tLo; norm_num, le_rfl⟩
  set Z := {t ∈ Icc tLo tHi | x t = 0} with hZ
  have hZc : IsClosed Z := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := by
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hlo.le hcont ⟨hsign.2.le, hxlo.le⟩
    exact ⟨c, hc, hc0⟩
  have hZb : BddBelow Z := ⟨tLo, fun t ht => ht.1.1⟩
  set τ := sInf Z
  have hτ : τ ∈ Z := hZc.csInf_mem hZne hZb
  have hτne_lo : τ ≠ tLo := fun h => by have := hτ.2; rw [h] at this; linarith
  have hτne_hi : τ ≠ tHi := fun h => by have := hτ.2; rw [h] at this; linarith [hsign.2]
  refine ⟨τ, ⟨lt_of_le_of_ne hτ.1.1 (Ne.symm hτne_lo), lt_of_le_of_ne hτ.1.2 hτne_hi⟩, hτ.2,
    fun t ht => ?_⟩
  rcases le_total t tLo with h | h
  · exact hsign.1 t ⟨ht.1, h⟩
  · by_contra hneg
    push Not at hneg
    have hsub2 : Icc tLo t ⊆ Icc tLo tHi := Icc_subset_Icc le_rfl (ht.2.le.trans hτ.1.2)
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' h (hcont.mono hsub2) ⟨hneg, hxlo.le⟩
    have hcZ : c ∈ Z := ⟨hsub2 hc, hc0⟩
    have := csInf_le hZb hcZ
    linarith [hc.2, ht.2]

end Work.Sim.DuffingAudit
