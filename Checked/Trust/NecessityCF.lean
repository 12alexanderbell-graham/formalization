import Checked.Trust.NonVacuity
import Checked.FSSep.RecedeSep
import Checked.FSSep.RecedeSepOver
import Checked.FSSep.RecedeSepSlow
import Checked.FalknerSkan.SeparationPrinted

/-! Hypothesis necessity for the bound below the printed separation value
(`Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed`; run 2026-11-27T0028Z): the zero velocity at
the wall is NEEDED (hypothesis 5). The witness: a separation solution with the wall receding against the stream
(`Checked.FSSep.RecedeSep.core_sepR`, chains `RecedeSepOver` and `RecedeSepSlow`) has zero stream function and zero
shear at the wall, velocity tending to one, positive shear after the wall and the fast approach, and its
pressure-gradient coefficient lies above the printed value. Module `NecessityCF`. -/

namespace Checked.Trust.NecessityCF
open Set Filter Topology

/-- A separation solution with the wall receding against the stream whose pressure-gradient coefficient lies above
the printed separation value. -/
theorem recede_sep :
    ∃ β : ℝ, -(1983 / 10000) < β ∧ ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 < 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  obtain ⟨β, hβ, -, f, p, q, h⟩ :=
    Checked.FSSep.RecedeSep.core_sepR (lo := 5043 / 1000) (hi := 5044 / 1000) (by norm_num) (by norm_num)
      (by norm_num) Checked.FSSep.RecedeSepOver.chain Checked.FSSep.RecedeSepSlow.chain
  exact ⟨β, by norm_num at hβ ⊢; linarith, f, p, q, h⟩

theorem fs_separation_below_printed_h5 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed 5 := by
  obtain ⟨β, hβ, f, p, q, a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := recede_sep
  exact ⟨β, f, p, q, a1, a2, a3, a4, a6, a7, a8, a9, fun h => by linarith⟩

end Checked.Trust.NecessityCF
