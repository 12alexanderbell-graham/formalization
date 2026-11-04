#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def sub(rel, old, new):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, "old text occurs %d times" % t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")

def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")

sub("Work/Sim/DuffingAudit.lean", "theorem blind_first_zero_mem_closed (x : ℝ → ℝ) (hx : SolvesIVP horizon x) :\n    ∃ τ ∈ Ioo tLo tHi, x τ = 0 ∧ ∀ t ∈ Ico (0 : ℝ) τ, 0 < x t := by\n  have hsign := blind_pos_then_neg_closed x hx\n  obtain ⟨v, -, -, hdx, -⟩ := hx\n  have hlo : tLo < tHi := by unfold tLo tHi; norm_num\n  have hsub : Icc tLo tHi ⊆ Icc 0 horizon := Icc_subset_Icc (by unfold tLo; norm_num)\n    (by unfold tHi horizon; norm_num)\n  have hcont : ContinuousOn x (Icc tLo tHi) := fun t ht =>\n    ((hdx t (hsub ht)).continuousWithinAt).mono hsub\n  have hxlo : 0 < x tLo := hsign.1 tLo ⟨by unfold tLo; norm_num, le_rfl⟩\n  set Z := {t ∈ Icc tLo tHi | x t = 0} with hZ\n  have hZc : IsClosed Z := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton\n  have hZne : Z.Nonempty := by\n    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hlo.le hcont ⟨hsign.2.le, hxlo.le⟩\n    exact ⟨c, hc, hc0⟩\n  have hZb : BddBelow Z := ⟨tLo, fun t ht => ht.1.1⟩\n  set τ := sInf Z\n  have hτ : τ ∈ Z := hZc.csInf_mem hZne hZb\n  have hτne_lo : τ ≠ tLo := fun h => by have := hτ.2; rw [h] at this; linarith\n  have hτne_hi : τ ≠ tHi := fun h => by have := hτ.2; rw [h] at this; linarith [hsign.2]\n  refine ⟨τ, ⟨lt_of_le_of_ne hτ.1.1 (Ne.symm hτne_lo), lt_of_le_of_ne hτ.1.2 hτne_hi⟩, hτ.2,\n    fun t ht => ?_⟩\n  rcases le_total t tLo with h | h\n  · exact hsign.1 t ⟨ht.1, h⟩\n  · by_contra hneg\n    push Not at hneg\n    have hsub2 : Icc tLo t ⊆ Icc tLo tHi := Icc_subset_Icc le_rfl (ht.2.le.trans hτ.1.2)\n    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' h (hcont.mono hsub2) ⟨hneg, hxlo.le⟩\n    have hcZ : c ∈ Z := ⟨hsub2 hc, hc0⟩\n    have := csInf_le hZb hcZ\n    linarith [hc.2, ht.2]\n\n", 'theorem blind_first_zero_mem_closed (x : ℝ → ℝ) (hx : SolvesIVP horizon x) :\n    ∃ τ ∈ Ioo tLo tHi, x τ = 0 ∧ ∀ t ∈ Ico (0 : ℝ) τ, 0 < x t := by\n  sorry\n\n')
