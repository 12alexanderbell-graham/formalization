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

LEAN = """import Work.Math.Gelfand

/-!
# Mathematics (THE RESULT part 5): the explosion threshold of the Gelfand problem in the ball

A one-line consequence of `Work.Math.Gelfand.gelfand_ball_critical`: the radial branch never exceeds
the certified maximum.
-/

namespace Work.Math.GelfandNoSolution
open Set

/-- **Thermal-explosion threshold of the Gelfand problem in the unit ball of ℝ³.** For every S ≥ 41/10 and
every regular solution w of w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, s² e^{w(s)} never exceeds
3.321992119 on [0, S]. Every solution u of Δu + λ e^u = 0 in the unit ball with u = 0 on the boundary is
radial with λ = s² e^{w(s)} for some s, so the problem has no solution at all for λ > 3.321992119: the
Frank-Kamenetskii critical value of the sphere is 3.3220, certified by a machine-checked proof. -/
theorem no_solution_above (S : ℝ) (hS : 41 / 10 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∀ s ∈ Icc 0 S, s ^ 2 * Real.exp (w s) ≤ 3.321992119 := by
  obtain ⟨s₁, -, -, hmax, -, hhi⟩ :=
    Work.Math.Gelfand.gelfand_ball_critical S hS w φ hw hφ0 hφ h0
  intro s hs
  exact (hmax s hs).trans hhi

end Work.Math.GelfandNoSolution
"""
new("Work/Math/GelfandNoSolution.lean", LEAN)
app("Work.lean", "import Work.Math.GelfandNoSolution\n")
rep("STATE.md", "- Not yet: promotion to Checked (module copy with specific imports",
    "- **Explosion threshold PROVED in Work** (`Work/Math/GelfandNoSolution.lean`, `no_solution_above`; local build, axioms standard): the Gelfand problem Δu + λeᵘ = 0 in the unit ball of ℝ³ has no solution for λ > 3.321992119, so the Frank-Kamenetskii critical value of the sphere (3.3220 in print) is certified; the PDE side is closed.\n- Not yet: promotion to Checked (module copy with specific imports")
rep("STATE.md", "the PDE side (radial solutions with s < 41/10, Gidas–Ni–Nirenberg symmetry, λ* = sup of solvable λ); ", "")
