import Checked.Trust.NecessityAJ
import Checked.Math.BonnorEbertMonotone

/-! Hypothesis necessity for the extrema and monotone segments of the Bonnor–Ebert mass
(`Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone`, run 2026-11-15T0828Z). The hypotheses are
those of `Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema` in the same order, and the conclusion contains
that headline's conclusion, so the witnesses of `Checked.Trust.NecessityAJ` carry over unchanged: a
counterexample to the weaker conclusion is one to the stronger (1, 3, 4 NEEDED), and continuity of φ at the
centre is forced by the equation (2 REDUNDANT). -/

namespace Checked.Trust.NecessityAN
open Set Filter Topology

theorem bonnor_ebert_extrema_monotone_r2 :
    dropped% Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone 2 := by
  intro w φ h1 h3 h4
  exact Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone w φ h1
    (Checked.Trust.NecessityAJ.cont_at_zero_Ici w φ h1 h3) h3 h4

theorem bonnor_ebert_extrema_monotone_h1 :
    necessity% Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone 1 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAJ.bonnor_ebert_extrema_h1
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, _, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩⟩

theorem bonnor_ebert_extrema_monotone_h3 :
    necessity% Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone 3 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAJ.bonnor_ebert_extrema_h3
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, _, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩⟩

theorem bonnor_ebert_extrema_monotone_h4 :
    necessity% Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone 4 := by
  obtain ⟨w, φ, a, b, c, hn⟩ := Checked.Trust.NecessityAJ.bonnor_ebert_extrema_h4
  exact ⟨w, φ, a, b, c, fun ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9, _, _, _⟩ =>
    hn ⟨ξ, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩⟩

end Checked.Trust.NecessityAN
