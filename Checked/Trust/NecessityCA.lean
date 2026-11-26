import Checked.Trust.NecessityAN
import Checked.Math.BonnorEbertTurningDecay

/-! Hypothesis necessity for the geometrically shrinking bounds on the extrema of the Bonnor–Ebert mass
(`Checked.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay`, run 2026-11-26T0428Z). The hypotheses are those
of `Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone` in the same order and the conclusion contains
that headline's conclusion, so each witness of `Checked.Trust.NecessityAN` carries over: where the conclusion of the
extrema and monotone segments fails, the conclusion with the two limits and the bounds fails too (1, 3, 4 NEEDED); continuity of φ
at the centre is forced by the equation (2 REDUNDANT). Module `NecessityCA`. -/

namespace Checked.Trust.NecessityCA
open Set Filter Topology

theorem bonnor_ebert_turning_decay_r2 :
    dropped% Checked.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay 2 := by
  intro w φ h1 h3 h4
  exact Checked.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay w φ h1
    (Checked.Trust.NecessityAJ.cont_at_zero_Ici w φ h1 h3) h3 h4

theorem bonnor_ebert_turning_decay_h1 :
    necessity% Checked.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay 1 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAN.bonnor_ebert_extrema_monotone_h1
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, _, _, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩⟩

theorem bonnor_ebert_turning_decay_h3 :
    necessity% Checked.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay 3 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAN.bonnor_ebert_extrema_monotone_h3
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, _, _, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩⟩

theorem bonnor_ebert_turning_decay_h4 :
    necessity% Checked.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay 4 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAN.bonnor_ebert_extrema_monotone_h4
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, _, _, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩⟩

end Checked.Trust.NecessityCA
