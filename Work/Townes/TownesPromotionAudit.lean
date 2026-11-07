import Mathlib
import Checked.Townes.TownesShooting
import Checked.Townes.TownesExists
import Work.Townes.TownesBlindClosed
import Work.Townes.TownesExistsBlindClosed

/-!
# Audit of the promoted Townes headlines (run 2026-11-07T0828Z)

The Checked copies (`Checked/Townes/*.lean`, promoted by
`runs/2026-11-07T0828Z/scripts/promote_townes.py`) state the same claims as the frozen Work
statements, and the blind restatements of runs 2026-11-07T0228Z and 0628Z (`Work/Townes/TownesBlind.lean`,
`Work/Townes/TownesExistsBlind.lean`, a different model, from the question alone) follow from the
CHECKED headlines, not from the Work proofs: the proofs of `Work.Townes.BlindClosed.blind_under`,
`blind_over` and `Work.Townes.ExistsBlindClosed.closed` with the Work headline replaced by the Checked one
(the helpers `hyps` and `of_program` are statement-level bridges that use no headline).
-/

namespace Work.Townes.PromotionAudit
open Work.Townes.BlindClosed Work.Townes.ExistsBlindClosed

/-- The blind undershoot statement follows from `Checked.Townes.Shooting.townes_under`. -/
theorem blind_under (θ θ' : ℝ → ℝ) (h : Blind.Townes.IsSolution 2.2062008646 θ θ') :
    ∃ r : ℝ, 0 < r ∧ r ≤ 13.6 ∧ 0 < θ' r ∧ ∀ s ∈ Set.Icc (0 : ℝ) r, 0 < θ s := by
  obtain ⟨hθ, hφ0, hφ, h0⟩ := hyps _ θ θ' h
  obtain ⟨r, hr, hp, hall⟩ :=
    Checked.Townes.Shooting.townes_under 13.6 (by norm_num) θ θ' hθ hφ0 hφ h0
  exact ⟨r, hr.1, hr.2.trans (by norm_num), hp, hall⟩

/-- The blind overshoot statement follows from `Checked.Townes.Shooting.townes_over`. -/
theorem blind_over (θ θ' : ℝ → ℝ) (h : Blind.Townes.IsSolution 2.2062008647 θ θ') :
    ∃ r : ℝ, 0 < r ∧ r ≤ 13.6 ∧ θ r < 0 ∧ ∀ s ∈ Set.Ioc (0 : ℝ) r, θ' s < 0 := by
  obtain ⟨hθ, hφ0, hφ, h0⟩ := hyps _ θ θ' h
  obtain ⟨r, hr, hn, hall⟩ :=
    Checked.Townes.Shooting.townes_over 13.6 (by norm_num) θ θ' hθ hφ0 hφ h0
  exact ⟨r, hr.1, hr.2.trans (by norm_num), hn, hall⟩

/-- The blind existence statement follows from `Checked.Townes.Exists.townes_exists`. -/
theorem blind_exists : ∃ θ : ℝ → ℝ, Blind.TownesExists.IsRadialProfile θ ∧
    (2.2062008646 : ℝ) < θ 0 ∧ θ 0 < (2.2062008647 : ℝ) := by
  obtain ⟨c, hc, θ, φ, h0, hφ0, hθ, hφc, hφ, hpos, -, hlim⟩ := Checked.Townes.Exists.townes_exists
  obtain ⟨Θ, hΘ, hΘ0⟩ := of_program c θ φ h0 hφ0 hθ hφc hφ hpos hlim
  exact ⟨Θ, hΘ, hΘ0 ▸ hc.1, hΘ0 ▸ hc.2⟩

end Work.Townes.PromotionAudit

#print axioms Work.Townes.PromotionAudit.blind_under
#print axioms Work.Townes.PromotionAudit.blind_over
#print axioms Work.Townes.PromotionAudit.blind_exists
