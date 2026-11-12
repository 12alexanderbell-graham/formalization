#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
LEAN = r"""import Checked.Trust.NonVacuity
import Checked.Trust.NecessityB
import Checked.Trust.NecessityD
import Checked.Cosmography.Lookback

/-! The second-order lookback expansion together with the vanishing redshift of a source emitting at the
observation time. Module `NecessityM1`. -/

open Filter Topology Asymptotics Checked.Cosmography

namespace Checked.Cosmography.LookbackZero

/-- The second-order lookback expansion of `lookback_second_order` and, in addition, the redshift of a
source emitting at the observation time `t₀` is zero. -/
theorem lookback_second_order_zero (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :
    ((fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2)) ∧ redshift a t₀ t₀ = 0 :=
  ⟨Checked.Cosmography.lookback_second_order a t₀ ha ha' ha0 hH, by
    unfold redshift; rw [div_self ha0, sub_self]⟩

end Checked.Cosmography.LookbackZero

namespace Checked.Trust.NCM1
open Checked.Cosmography.LookbackZero

theorem nv : nonvacuity% Checked.Cosmography.LookbackZero.lookback_second_order_zero :=
  ⟨Real.exp, 0, Filter.Eventually.of_forall fun _ => Real.differentiableAt_exp,
    by rw [Real.deriv_exp]; exact Real.differentiableAt_exp, (Real.exp_pos 0).ne',
    by simp [Real.deriv_exp], trivial⟩

theorem lookback_second_order_zero_r1 :
    dropped% Checked.Cosmography.LookbackZero.lookback_second_order_zero 1 := by
  intro a t₀ ha' ha0 hH
  refine ⟨Checked.Trust.NCD.lookback_second_order_r1 a t₀ ha' ha0 hH, ?_⟩
  unfold Checked.Cosmography.redshift
  rw [div_self ha0, sub_self]

theorem lookback_second_order_zero_h2 :
    necessity% Checked.Cosmography.LookbackZero.lookback_second_order_zero 2 := by
  obtain ⟨a, t₀, p1, p3, p4, hn⟩ := Checked.Trust.NCD.lookback_second_order_h2
  exact ⟨a, t₀, p1, p3, p4, fun h => hn h.1⟩

/-- `a t₀ ≠ 0` is needed: with `a = id` and `t₀ = 0` the redshift at the observation time is `-1`. -/
theorem lookback_second_order_zero_h3 :
    necessity% Checked.Cosmography.LookbackZero.lookback_second_order_zero 3 := by
  have hd : deriv (fun t : ℝ => t) = fun _ => (1 : ℝ) := funext fun x => (hasDerivAt_id x).deriv
  refine ⟨fun t => t, 0, Filter.Eventually.of_forall fun t => (hasDerivAt_id t).differentiableAt,
    ?_, ?_, ?_⟩
  · rw [hd]; exact differentiableAt_const _
  · rw [hd]; norm_num
  · intro h
    have h2 := h.2
    rw [Checked.Trust.NCB.redshift_of_a0 (fun t : ℝ => t) 0 rfl 0] at h2
    norm_num at h2

theorem lookback_second_order_zero_h4 :
    necessity% Checked.Cosmography.LookbackZero.lookback_second_order_zero 4 := by
  obtain ⟨a, t₀, p1, p2, p3, hn⟩ := Checked.Trust.NCB.lookback_second_order_h4
  exact ⟨a, t₀, p1, p2, p3, fun h => hn h.1⟩

end Checked.Trust.NCM1
"""
mod = "NecessityM1"
(root / "Checked" / "Trust" / (mod + ".lean")).write_text(LEAN)
p = root / "Checked.lean"
s = p.read_text()
assert ("import Checked.Trust." + mod + "\n") not in s
if not s.endswith("\n"): s += "\n"
p.write_text(s + "import Checked.Trust." + mod + "\n")
h = root / "scripts" / "trust" / "headlines.txt"
s = h.read_text()
if not s.endswith("\n"): s += "\n"
assert "Checked.Cosmography.LookbackZero.lookback_second_order_zero\n" not in s
h.write_text(s + "Checked.Cosmography.LookbackZero.lookback_second_order_zero\n")
