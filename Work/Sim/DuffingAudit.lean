import Work.Sim.Duffing
import Work.Sim.DuffingBlind

/-!
# Audit of `Work.Sim.Duffing`: the blind restatement closed in Lean

The blind restater (run 2026-11-04T0628Z, `DuffingBlind.lean`, written from the claim alone)
chose derivatives *within* [0, 1.2] (one-sided at the endpoints), a weaker hypothesis than the
frozen `IsDuffingIVP` (two-sided). Its main theorem and its existence theorem follow from the
program's core theorem `first_zero_within` and from `duffing_exists`. Its two extra corollaries
(`first_zero_mem`, `first_zero_unique`) are not closed here.
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

end Work.Sim.DuffingAudit
