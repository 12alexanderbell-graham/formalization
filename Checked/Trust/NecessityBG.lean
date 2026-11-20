import Checked.Trust.NonVacuity
import Checked.Math.GSymFree

/-! Hypothesis necessity for `Checked.Math.GelfandPDE.gelfand_pde_radial_bound` (run 2026-11-20T1828Z):
the hypothesis that the function is radial is redundant. A classical solution with no symmetry assumed bounds
the radial iterates of the minimal solution from above (the weak maximum principle of
`Checked.Math.GMaxPrinciple`); their limit is a radial classical solution with the same parameter, to which the
radial statement applies (`Checked.Math.GSymFree.bound_no_radial`). No Gidas–Ni–Nirenberg theorem is used.
Module `NecessityBG`. -/

namespace Checked.Trust.NecessityBG

/-- The hypothesis that `u` is a function of `‖x‖` in `gelfand_pde_radial_bound` is redundant. -/
theorem gelfand_pde_radial_bound_r4 :
    dropped% Checked.Math.GelfandPDE.gelfand_pde_radial_bound 4 := by
  intro lam u hu hc hb hpde
  exact Checked.Math.GSymFree.bound_no_radial lam u hu hc hb hpde

end Checked.Trust.NecessityBG
