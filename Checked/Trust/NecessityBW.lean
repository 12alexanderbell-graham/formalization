import Checked.Trust.NecessityAN
import Checked.Math.BonnorEbertTurningRatio

/-! Hypothesis necessity for the rate of the extrema of the Bonnor–Ebert mass
(`Checked.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio`, run 2026-11-25T1628Z). The hypotheses are those
of `Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone` in the same order and the conclusion contains
that headline's conclusion, so each witness of `Checked.Trust.NecessityAN` carries over: where the conclusion of the
extrema and monotone segments fails, the conclusion with the two limits fails too (1, 3, 4 NEEDED); continuity of φ
at the centre is forced by the equation (2 REDUNDANT). Module `NecessityBW`. -/

namespace Checked.Trust.NecessityBW
open Set Filter Topology

theorem bonnor_ebert_turning_ratio_r2 :
    dropped% Checked.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio 2 := by
  intro w φ h1 h3 h4
  exact Checked.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio w φ h1
    (Checked.Trust.NecessityAJ.cont_at_zero_Ici w φ h1 h3) h3 h4

theorem bonnor_ebert_turning_ratio_h1 :
    necessity% Checked.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio 1 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAN.bonnor_ebert_extrema_monotone_h1
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩⟩

theorem bonnor_ebert_turning_ratio_h3 :
    necessity% Checked.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio 3 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAN.bonnor_ebert_extrema_monotone_h3
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩⟩

theorem bonnor_ebert_turning_ratio_h4 :
    necessity% Checked.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio 4 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAN.bonnor_ebert_extrema_monotone_h4
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩⟩

end Checked.Trust.NecessityBW
