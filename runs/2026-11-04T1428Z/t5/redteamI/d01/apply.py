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

LEAN = "import Checked.Sim.Duffing\n\nnamespace Checked.Sim.Duffing\nopen Set\n\n/-- Quarter period of the whole family of Duffing oscillators x'' + k·x + β·x³ = 0, hardening\n(β > 0) and softening (β < 0) springs alike, released from rest at x = 1: the solution is strictly\npositive on [0, 1.192005] and strictly negative at 1.192006, so its earliest zero lies strictly\nbetween 1.192005 and 1.192006. Proved by a validated enclosure (rational Taylor cells, exact defect\nbounds, energy box, Grönwall). -/\ntheorem duffing_first_zero_family (x : ℝ → ℝ) (hx : IsDuffingSolution 1 1 1 0 (6 / 5) x) :\n    (∀ t ∈ Icc (0 : ℝ) (1192005 / 1000000), 0 < x t) ∧ x (1192006 / 1000000) < 0 :=\n  duffing_first_zero_sol x hx\n\nend Checked.Sim.Duffing\n"
wr('Checked/Sim/DuffingFamily.lean', LEAN)
app("Checked.lean", "import Checked.Sim.DuffingFamily\n")
app("scripts/trust/headlines.txt", 'Checked.Sim.Duffing.duffing_first_zero_family\n')
rep("Checked/Trust/Witnesses.lean", 'import Checked.Sim.Duffing\nimport Checked.Sim.MichaelisMenten\n', 'import Checked.Sim.Duffing\nimport Checked.Sim.MichaelisMenten\nimport Checked.Sim.DuffingFamily\n')
rep("Checked/Trust/Witnesses.lean", "\nend Checked.Trust.NV", '\ntheorem duffing_first_zero_family : nonvacuity% Checked.Sim.Duffing.duffing_first_zero_family := by\n  obtain ⟨x, hx⟩ := Checked.Sim.Duffing.duffing_solution_exists\n  exact ⟨x, hx, 0, ⟨le_rfl, by norm_num⟩, trivial⟩\n\nend Checked.Trust.NV')
