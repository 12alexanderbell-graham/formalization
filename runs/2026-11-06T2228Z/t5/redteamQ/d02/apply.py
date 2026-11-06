import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rd(p): return (root/p).read_text(encoding="utf-8")
def wr(p, s): (root/p).write_text(s, encoding="utf-8")
def app(p, s):
    t = rd(p)
    if not t.endswith("\n"): t += "\n"
    wr(p, t + s)
def rep(p, old, new):
    t = rd(p); assert t.count(old) == 1, (p, old[:60], t.count(old)); wr(p, t.replace(old, new))

LEAN = "import Mathlib.Data.Real.Basic\nimport Checked.Trust.NonVacuity\n\n/-!\n# Acceleration of a body (mechanics)\n\nOne equation of Newton's second law, stated for real numbers.\n-/\n\nnamespace Checked.Math.ZeroMass\n\n/-- The acceleration, the ratio force / mass of a force to a mass, equals zero when the mass is zero. -/\ntheorem acceleration_of_zero_mass (force mass : ℝ) (h : mass = 0) : force / mass = 0 := by\n  rw [h]\n  exact div_zero force\n\nend Checked.Math.ZeroMass\n\nnamespace Checked.Math.ZeroMassNV\n\ntheorem acceleration_of_zero_mass : nonvacuity% Checked.Math.ZeroMass.acceleration_of_zero_mass :=\n  ⟨0, 0, rfl, trivial⟩\n\nend Checked.Math.ZeroMassNV\n"
wr('Checked/Math/ZeroMass.lean', LEAN)
app("Checked.lean", "import Checked.Math.ZeroMass\n")
app("scripts/trust/headlines.txt", 'Checked.Math.ZeroMass.acceleration_of_zero_mass' + "\n")
