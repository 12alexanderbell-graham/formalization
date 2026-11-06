import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rd(rel):
    return (root / rel).read_text(encoding="utf-8")
def rep(rel, old, new):
    p = root / rel; t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, old)
    p.write_text(t.replace(old, new), encoding="utf-8")
def app(rel, s):
    p = root / rel; t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"): t += "\n"
    p.write_text(t + s, encoding="utf-8")
def new(rel, s):
    p = root / rel; p.parent.mkdir(parents=True, exist_ok=True)
    assert not p.exists(), rel
    p.write_text(s, encoding="utf-8")
ROB = ("Checked.Trust.SecondReading.robK1 Checked.Trust.SecondReading.robK2 Checked.Trust.SecondReading.robK3 "
       "Checked.Trust.SecondReading.robInit")

LEAN = """import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Checked.Trust.NonVacuity

/-!
# Chemistry: size of Soave's κ(ω) on the unit interval of acentric factors

A one-line consequence of the κ(ω) polynomial, with no equation of state involved.
-/

namespace Checked.Chemistry.SoaveWindow

/-- Soave's κ(ω) correlation is positive and stays below 2 for every ω in [0, 1], so it is safe to use on
that range and gives a usable attraction parameter there. -/
theorem soave_kappa_window (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω ≤ 1) :
    0 < 0.480 + 1.574 * ω - 0.176 * ω ^ 2 ∧ 0.480 + 1.574 * ω - 0.176 * ω ^ 2 < 2 := by
  have hsq : ω ^ 2 ≤ ω := by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]
  constructor <;> nlinarith [sq_nonneg (ω - 1), hsq]

end Checked.Chemistry.SoaveWindow

namespace Checked.Trust.NV
theorem soave_kappa_window : nonvacuity% Checked.Chemistry.SoaveWindow.soave_kappa_window :=
  ⟨0, le_rfl, zero_le_one, trivial⟩
end Checked.Trust.NV
"""
new("Checked/Chemistry/SoaveWindow.lean", LEAN)
app("Checked.lean", "import Checked.Chemistry.SoaveWindow\n")
H = "Checked.Chemistry.SoaveWindow.soave_kappa_window"
app("scripts/trust/headlines.txt", H + "\n")
app("scripts/trust/literal_readings.txt", H + " source=Soave Checked.Trust.SecondReading.kappaSoave\n")
app("LEDGER.md", "\n- 2026-11-06T1228Z: **Literal reading** for `soave_kappa_window` (literal_readings.txt, source=Soave): `Checked.Trust.SecondReading.kappaSoave` (the same blind reader constant as `srk_omega1_exists`). New headline `soave_kappa_window` (Checked/Chemistry/SoaveWindow.lean); frozen.txt relocked (new entries only).\n")
