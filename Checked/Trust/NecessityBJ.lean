import Checked.Trust.NecessityAO
import Checked.Math.GelfandTurningValuesFive

/-! Hypothesis necessity for the first five turning values of the radial Gelfand branch
(`Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five`, run 2026-11-21T0428Z). The hypotheses are
those of `Checked.Math.GelfandExtrema.gelfand_extrema` in the same order and the conclusion contains that
headline's conclusion, so each witness of `Checked.Trust.NecessityAO` carries over: where the conclusion of the
turning points fails, the conclusion with the values fails too; continuity of φ at the centre is forced by the
equation. Module `NecessityBJ`. -/

namespace Checked.Trust.NecessityBJ
open Set Filter Topology

theorem gelfand_turning_values_five_r2 :
    dropped% Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five 2 := by
  intro w φ h1 h3 h4
  exact Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five w φ h1
    (Checked.Trust.NecessityAJ.cont_at_zero_Ici w φ h1 h3) h3 h4

theorem gelfand_turning_values_five_h1 :
    necessity% Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five 1 := by
  obtain ⟨w, φ, x1, x2, x3, hn⟩ := Checked.Trust.NecessityAO.gelfand_extrema_h1
  refine ⟨w, φ, x1, x2, x3, ?_⟩
  rintro ⟨ζ, a1, a2, a3, a4, a5, a6, -, -, -, -, -, -, -, -, a7, a8, a9, a10, a11, a12, a13, a14⟩
  exact hn ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

theorem gelfand_turning_values_five_h3 :
    necessity% Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five 3 := by
  obtain ⟨w, φ, x1, x2, x3, hn⟩ := Checked.Trust.NecessityAO.gelfand_extrema_h3
  refine ⟨w, φ, x1, x2, x3, ?_⟩
  rintro ⟨ζ, a1, a2, a3, a4, a5, a6, -, -, -, -, -, -, -, -, a7, a8, a9, a10, a11, a12, a13, a14⟩
  exact hn ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

theorem gelfand_turning_values_five_h4 :
    necessity% Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five 4 := by
  obtain ⟨w, φ, x1, x2, x3, hn⟩ := Checked.Trust.NecessityAO.gelfand_extrema_h4
  refine ⟨w, φ, x1, x2, x3, ?_⟩
  rintro ⟨ζ, a1, a2, a3, a4, a5, a6, -, -, -, -, -, -, -, -, a7, a8, a9, a10, a11, a12, a13, a14⟩
  exact hn ⟨ζ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩

end Checked.Trust.NecessityBJ
