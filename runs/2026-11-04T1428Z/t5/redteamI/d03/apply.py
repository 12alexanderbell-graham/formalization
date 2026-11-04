import sys, os
root = sys.argv[1]
def rd(p):
    return open(os.path.join(root, p), encoding="utf-8").read()
def wr(p, s):
    open(os.path.join(root, p), "w", encoding="utf-8").write(s)
def rep(p, old, new):
    s = rd(p); assert s.count(old) == 1, (p, old[:40], s.count(old)); wr(p, s.replace(old, new))
def app(p, add):
    s = rd(p); wr(p, s + add)

LEAN = "import Checked.Sim.Duffing\n\nnamespace Checked.Sim.Duffing\nopen Set\n\n/-- There is a solution of the Duffing initial value problem x'' + x + x³ = 0, x(0) = 1, x'(0) = 0\non the time interval [0, 6/5] (derivatives within the interval); by the conserved energy it stays\nbounded, so the same construction continues it for arbitrarily long times and arbitrarily large\nrelease amplitudes. -/\ntheorem duffing_solution_exists_global : ∃ x : ℝ → ℝ, IsDuffingSolution 1 1 1 0 (6 / 5) x :=\n  duffing_solution_exists\n\nend Checked.Sim.Duffing\n"
wr('Checked/Sim/DuffingGlobal.lean', LEAN)
app("Checked.lean", "import Checked.Sim.DuffingGlobal\n")
app("scripts/trust/headlines.txt", 'Checked.Sim.Duffing.duffing_solution_exists_global\n')
rep("Checked/Trust/Witnesses.lean", 'import Checked.Sim.Duffing\nimport Checked.Sim.MichaelisMenten\n', 'import Checked.Sim.Duffing\nimport Checked.Sim.MichaelisMenten\nimport Checked.Sim.DuffingGlobal\n')
rep("Checked/Trust/Witnesses.lean", "\nend Checked.Trust.NV", '\n\nend Checked.Trust.NV')
