import Mathlib.Data.Real.Basic

/-! CONTROL (branch `control/vacuous-headline` only, run 2228Z): a headline with contradictory
hypotheses. It is true and says nothing; CI must fail at the trust-map step because no
non-vacuity witness can exist. A decoy witness with a weaker statement (one hypothesis
dropped) is supplied and must not be accepted. -/

namespace Checked.Trust.Control

theorem vacuous_headline (x : ℝ) (h1 : 0 < x) (h2 : x < 0) : x = 5 :=
  absurd (h1.trans h2) (lt_irrefl 0)

theorem vacuous_headline_decoy : ∃ (x : ℝ) (_ : 0 < x), True := ⟨1, one_pos, trivial⟩

end Checked.Trust.Control
