import Checked.Trust.NonVacuity
import Checked.Math.GNegExists

/-! Hypothesis necessity for `Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists` (run 2026-11-20T1228Z):
the positivity of the parameter is redundant, because a radial classical solution exists for every
non-positive parameter too (`Checked.Math.GNegExists.exists_nonpos`: the zero function at zero; below zero a
clamped radial profile of the equation with the opposite sign, rescaled so that it vanishes on the sphere).
Module `NecessityBE`. -/

namespace Checked.Trust.NecessityBE

/-- The hypothesis `0 < lam` of `gelfand_pde_radial_exists` is redundant. -/
theorem gelfand_pde_radial_exists_r1 :
    dropped% Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 1 := by
  intro lam hle
  by_cases hpos : 0 < lam
  · exact Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists lam hpos hle
  · exact Checked.Math.GNegExists.exists_nonpos lam (not_lt.1 hpos)

end Checked.Trust.NecessityBE
