import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")
def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")
def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")

LEAN = '''import Checked.Cosmography.Lookback
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Checked.Trust.NonVacuity

/-!
# Lookback time to second order: the accelerating-universe form (addendum to milestone 1)

For the observed accelerating universe the lookback time `t₀ − t` of a source of redshift `z`
satisfies `t₀ − t = H₀⁻¹ (z − (1 + q₀/2) z²) + o(z²)` (Visser 2005, Eq. (11)).
-/

namespace Checked.Cosmography

open Filter Asymptotics Topology

/-- Lookback time to second order in redshift, accelerating case (`q₀ < 0`). -/
theorem lookback_second_order_accel (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) (hq : decel a t₀ < 0) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) :=
  lookback_second_order a t₀ ha ha' ha0 hH

end Checked.Cosmography

namespace Checked.Trust.NV

open Filter

theorem lookback_second_order_accel :
    nonvacuity% Checked.Cosmography.lookback_second_order_accel :=
  ⟨Real.exp, 0, Eventually.of_forall fun _ => Real.differentiableAt_exp,
    by rw [Real.deriv_exp]; exact Real.differentiableAt_exp, (Real.exp_pos 0).ne',
    by simp [Real.deriv_exp],
    by
      rw [show Checked.Cosmography.decel Real.exp 0 = -1 by
        simp [Checked.Cosmography.decel, Real.deriv_exp]]
      norm_num,
    trivial⟩

end Checked.Trust.NV
'''
create("Checked/Cosmography/LookbackAccel.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.LookbackAccel\n")
append("scripts/trust/headlines.txt", "# F0 addendum\nChecked.Cosmography.lookback_second_order_accel\n")
sub("STATE.md", "- **Findings F1–F11** (FINDINGS.md)",
    "- **PROVED** (F0 addendum) `Checked.Cosmography.lookback_second_order_accel`: the second-order lookback-time series for FLRW cosmography, for every scale factor twice differentiable at t₀ with a(t₀), H₀ ≠ 0 (q₀ enters only through the coefficient): run 2026-10-31.\n- **Findings F1–F11** (FINDINGS.md)")
