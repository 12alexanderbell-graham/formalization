import Checked.Records.Basic
import Checked.Cosmography.BambaAngular
import Checked.Cosmography.CVdQ

namespace Checked.Records

open Checked.Cosmography Checked.Cosmography.Aviles

/-! ## F4–F7: printed and corrected coefficients of the y-redshift series in de Sitter -/

private lemma dS_hubbleR : hubble Real.exp 0 = 1 := by simp [hubble, Real.deriv_exp]

private lemma dS_decelR : decel Real.exp 0 = -1 := by simp [decel, Real.deriv_exp]

private lemma dS_coeffR (n : ℕ) : cosmoCoeff n Real.exp 0 = 1 := by
  simp [cosmoCoeff, iteratedDeriv_eq_iterate, Real.iter_deriv_exp, dS_hubbleR]

private lemma dS_omega0R (K : ℝ) : BambaK.omega0 K Real.exp 0 = 1 + K := by
  simp [BambaK.omega0, dS_hubbleR]

/-- With the scale factor `Real.exp`, the time `0` and the curvature constant `1`: `printedD2y` rounds to
−2.8333, `correctD2y` to `2.8333`, and `printedD2y` less `correctD2y` to −5.6667. -/
theorem F4_values :
    RoundsTo (BambaY.printedD2y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) (-2.8333) 4 ∧
    RoundsTo (BambaY.correctD2y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) 2.8333 4 ∧
    RoundsTo (BambaY.printedD2y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0) - BambaY.correctD2y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) (-5.6667) 4 := by
  rw [dS_decelR, dS_coeffR, dS_omega0R]
  unfold BambaY.printedD2y BambaY.correctD2y RoundsTo; simp only [abs_le]; norm_num

/-- With the scale factor `Real.exp`, the time `0` and the curvature constant `1`: `printedQ2` rounds to
`0.4167`, `correctQ2` to `0.2083`, and `printedQ2` less `correctQ2` to `0.2083`. -/
theorem F5_values :
    RoundsTo (CVdQ.printedQ2 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) 0.4167 4 ∧
    RoundsTo (CVdQ.correctQ2 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) 0.2083 4 ∧
    RoundsTo (CVdQ.printedQ2 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0) - CVdQ.correctQ2 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) 0.2083 4 := by
  rw [dS_decelR, dS_coeffR, dS_omega0R]
  unfold CVdQ.printedQ2 CVdQ.correctQ2 RoundsTo; simp only [abs_le]; norm_num

/-- With the scale factor `Real.exp`, the time `0` and the curvature constant `1`: `printedD3y` rounds to
`4.1667`, `correctD3y` to `3.3333`, and `printedD3y` less `correctD3y` to `0.8333`. -/
theorem F6_third :
    RoundsTo (BambaK.printedD3y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) 4.1667 4 ∧
    RoundsTo (BambaK.correctD3y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) 3.3333 4 ∧
    RoundsTo (BambaK.printedD3y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0) - BambaK.correctD3y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (cosmoCoeff 4 Real.exp 0) (BambaK.omega0 1 Real.exp 0)) 0.8333 4 := by
  rw [dS_decelR, dS_coeffR, dS_coeffR, dS_omega0R]
  unfold BambaK.correctD3y BambaK.printedD3y RoundsTo
  simp only [abs_le]; norm_num

/-- With the scale factor `Real.exp`, the time `0` and the curvature constant `1`: `printedD4y` rounds to
`3.75`, `correctD4y` to `3.3417`, and `printedD4y` less `correctD4y` to `0.4083`. -/
theorem F6_fourth :
    RoundsTo (BambaK.printedD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 1 Real.exp 0)) 3.75 2 ∧
    RoundsTo (BambaK.correctD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 1 Real.exp 0)) 3.3417 4 ∧
    RoundsTo (BambaK.printedD4y (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 1 Real.exp 0) - BambaK.correctD4y (decel Real.exp 0)
      (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0) (cosmoCoeff 5 Real.exp 0)
      (BambaK.omega0 1 Real.exp 0)) 0.4083 4 := by
  rw [dS_decelR, dS_coeffR, dS_coeffR, dS_coeffR, dS_omega0R]
  unfold BambaK.correctD4y BambaK.printedD4y RoundsTo
  simp only [abs_le]; norm_num

/-- With the scale factor `Real.exp`, the time `0` and the curvature constant `5`: `printedDA3` rounds to
−0.4167, `correctDA3` to −1.6667, and `printedDA3` less `correctDA3` to `1.25`. -/
theorem F7_third :
    RoundsTo (BambaA.printedDA3 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (BambaK.omega0 5 Real.exp 0)) (-0.4167) 4 ∧
    RoundsTo (BambaA.correctDA3 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (BambaK.omega0 5 Real.exp 0)) (-1.6667) 4 ∧
    RoundsTo (BambaA.printedDA3 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (BambaK.omega0 5 Real.exp 0) - BambaA.correctDA3 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0)
      (cosmoCoeff 4 Real.exp 0) (BambaK.omega0 5 Real.exp 0)) 1.25 2 := by
  rw [dS_decelR, dS_coeffR, dS_coeffR, dS_omega0R]
  unfold BambaA.correctDA3 BambaA.printedDA3 RoundsTo
  simp only [abs_le]; norm_num

/-- With the scale factor `Real.exp`, the time `0` and the curvature constant `5`: `printedDA4` rounds to
−0.2083, `correctDA4` to −2.2917, and `printedDA4` less `correctDA4` to `2.0833`. -/
theorem F7_fourth :
    RoundsTo (BambaA.printedDA4 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 5 Real.exp 0)) (-0.2083) 4 ∧
    RoundsTo (BambaA.correctDA4 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 5 Real.exp 0)) (-2.2917) 4 ∧
    RoundsTo (BambaA.printedDA4 (decel Real.exp 0) (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0)
      (cosmoCoeff 5 Real.exp 0) (BambaK.omega0 5 Real.exp 0) - BambaA.correctDA4 (decel Real.exp 0)
      (cosmoCoeff 3 Real.exp 0) (cosmoCoeff 4 Real.exp 0) (cosmoCoeff 5 Real.exp 0)
      (BambaK.omega0 5 Real.exp 0)) 2.0833 4 := by
  rw [dS_decelR, dS_coeffR, dS_coeffR, dS_coeffR, dS_omega0R]
  unfold BambaA.correctDA4 BambaA.printedDA4 RoundsTo
  simp only [abs_le]; norm_num

end Checked.Records
