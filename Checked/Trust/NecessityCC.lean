import Checked.Trust.NecessityAO
import Checked.Math.GelfandTurningDecay

/-! Hypothesis necessity for the geometrically shrinking bounds on the turning points of the radial Gelfand branch
(`Checked.Math.GelfandTurningDecay.gelfand_turning_decay`, run 2026-11-26T1028Z). The hypotheses are those of
`Checked.Math.GelfandExtrema.gelfand_extrema` in the same order and the conclusion contains that headline's
conclusion, so each witness of `Checked.Trust.NecessityAO` carries over: where the conclusion of the turning points
fails, the conclusion with the radii and the bounds fails too; continuity of φ at the centre is forced by the equation. Module
`NecessityCC`. -/

namespace Checked.Trust.NecessityCC
open Set Filter Topology

theorem gelfand_turning_decay_r2 :
    dropped% Checked.Math.GelfandTurningDecay.gelfand_turning_decay 2 := by
  intro w φ h1 h3 h4
  exact Checked.Math.GelfandTurningDecay.gelfand_turning_decay w φ h1
    (Checked.Trust.NecessityAJ.cont_at_zero_Ici w φ h1 h3) h3 h4

theorem gelfand_turning_decay_h1 :
    necessity% Checked.Math.GelfandTurningDecay.gelfand_turning_decay 1 := by
  obtain ⟨w, φ, x1, x2, x3, hn⟩ := Checked.Trust.NecessityAO.gelfand_extrema_h1
  refine ⟨w, φ, x1, x2, x3, ?_⟩
  rintro ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, -⟩
  exact hn ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

theorem gelfand_turning_decay_h3 :
    necessity% Checked.Math.GelfandTurningDecay.gelfand_turning_decay 3 := by
  obtain ⟨w, φ, x1, x2, x3, hn⟩ := Checked.Trust.NecessityAO.gelfand_extrema_h3
  refine ⟨w, φ, x1, x2, x3, ?_⟩
  rintro ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, -⟩
  exact hn ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

theorem gelfand_turning_decay_h4 :
    necessity% Checked.Math.GelfandTurningDecay.gelfand_turning_decay 4 := by
  obtain ⟨w, φ, x1, x2, x3, hn⟩ := Checked.Trust.NecessityAO.gelfand_extrema_h4
  refine ⟨w, φ, x1, x2, x3, ?_⟩
  rintro ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, -⟩
  exact hn ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

end Checked.Trust.NecessityCC
