import Mathlib
import Work.Math.GelfandPDEBound
import Work.Math.GelfandPDEBoundBlind

/-! Audit of `Work.Math.GelfandPDEBound.gelfand_pde_bound`: the blind restatement
(`Work.Math.GelfandPDEBoundBlind.blind_gelfand_pde_bound`: a classical solution as a predicate, the boundary
condition on `Metric.sphere`, the Laplacian written as `Laplacian.laplacian`) proved from the frozen
headline, its statement copied as the statement of `blind_closed`. -/

namespace Work.Math.GelfandPDEBoundBlindClosed
open Metric Work.Math.GelfandPDEBoundBlind

theorem blind_closed (lam : ℝ)
    (h : ∃ u : E3 → ℝ, IsClassicalGelfandSolution lam u) :
    lam ≤ 3.321992119 := by
  obtain ⟨u, hu, hc, hpde, hb⟩ := h
  exact Work.Math.GelfandPDEBound.gelfand_pde_bound lam u hu hc
    (fun x hx => hb x (by rw [mem_sphere_zero_iff_norm]; exact hx)) hpde

end Work.Math.GelfandPDEBoundBlindClosed
