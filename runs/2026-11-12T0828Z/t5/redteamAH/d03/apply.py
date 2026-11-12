#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
LEAN = r"""import Checked.Trust.NonVacuity
import Checked.Trust.NecessityB
import Checked.Trust.NecessityD
import Checked.Cosmography.Lookback

/-! The second-order lookback expansion with the Hubble numerator given as a unit. Module `NecessityM3`. -/

open Filter Topology Asymptotics Checked.Cosmography

namespace Checked.Cosmography.LookbackUnit

/-- The second-order lookback expansion of `lookback_second_order`, with the present velocity of the scale
factor given as a unit `H` of the real numbers. -/
theorem lookback_second_order_unit (a : ℝ → ℝ) (t₀ : ℝ) (H : Units ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : ((H : Units ℝ) : ℝ) = deriv a t₀) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) :=
  Checked.Cosmography.lookback_second_order a t₀ ha ha' ha0
    (fun h0 => H.ne_zero (hH.trans h0))

end Checked.Cosmography.LookbackUnit

namespace Checked.Trust.NCM3

theorem nv : nonvacuity% Checked.Cosmography.LookbackUnit.lookback_second_order_unit :=
  ⟨Real.exp, 0, 1, Filter.Eventually.of_forall fun _ => Real.differentiableAt_exp,
    by rw [Real.deriv_exp]; exact Real.differentiableAt_exp, (Real.exp_pos 0).ne',
    by simp [Real.deriv_exp], trivial⟩

theorem lookback_second_order_unit_r1 :
    dropped% Checked.Cosmography.LookbackUnit.lookback_second_order_unit 1 := by
  intro a t₀ H ha' ha0 hH
  exact Checked.Trust.NCD.lookback_second_order_r1 a t₀ ha' ha0 (fun h0 => H.ne_zero (hH.trans h0))

theorem lookback_second_order_unit_h2 :
    necessity% Checked.Cosmography.LookbackUnit.lookback_second_order_unit 2 := by
  obtain ⟨a, t₀, p1, p3, p4, hn⟩ := Checked.Trust.NCD.lookback_second_order_h2
  exact ⟨a, t₀, Units.mk0 (deriv a t₀) p4, p1, p3, rfl, hn⟩

theorem lookback_second_order_unit_r3 :
    dropped% Checked.Cosmography.LookbackUnit.lookback_second_order_unit 3 := by
  intro a t₀ H ha ha' hH
  exact Checked.Trust.NCB.lookback_second_order_r3 a t₀ ha ha' (fun h0 => H.ne_zero (hH.trans h0))

theorem lookback_second_order_unit_h4 :
    necessity% Checked.Cosmography.LookbackUnit.lookback_second_order_unit 4 := by
  obtain ⟨a, t₀, p1, p2, p3, hn⟩ := Checked.Trust.NCB.lookback_second_order_h4
  exact ⟨a, t₀, 1, p1, p2, p3, hn⟩

end Checked.Trust.NCM3
"""
mod = "NecessityM3"
(root / "Checked" / "Trust" / (mod + ".lean")).write_text(LEAN)
p = root / "Checked.lean"
s = p.read_text()
assert ("import Checked.Trust." + mod + "\n") not in s
if not s.endswith("\n"): s += "\n"
p.write_text(s + "import Checked.Trust." + mod + "\n")
h = root / "scripts" / "trust" / "headlines.txt"
s = h.read_text()
if not s.endswith("\n"): s += "\n"
assert "Checked.Cosmography.LookbackUnit.lookback_second_order_unit\n" not in s
h.write_text(s + "Checked.Cosmography.LookbackUnit.lookback_second_order_unit\n")
