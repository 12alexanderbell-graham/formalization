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

LEAN = 'import Checked.Sim.MichaelisMenten\n\nnamespace Checked.Sim.MichaelisMenten\nopen Set\n\n/-- Universal half-conversion time of the Michaelis–Menten mechanism: the time at which half of the\nsubstrate has become product lies between 2.5665 and 2.5666 for solutions on [0, 13/5]. It is a\nconstant of the mechanism, not of the chosen rate constants or enzyme loading. -/\ntheorem mm_half_conversion_universal {s e c p : ℝ → ℝ} (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :\n    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) :=\n  mm_half_conversion h\n\nend Checked.Sim.MichaelisMenten\n'
wr('Checked/Sim/MMUniversal.lean', LEAN)
app("Checked.lean", "import Checked.Sim.MMUniversal\n")
app("scripts/trust/headlines.txt", 'Checked.Sim.MichaelisMenten.mm_half_conversion_universal\n')
rep("Checked/Trust/Witnesses.lean", 'import Checked.Sim.Duffing\nimport Checked.Sim.MichaelisMenten\n', 'import Checked.Sim.Duffing\nimport Checked.Sim.MichaelisMenten\nimport Checked.Sim.MMUniversal\n')
rep("Checked/Trust/Witnesses.lean", "\nend Checked.Trust.NV", '\ntheorem mm_half_conversion_universal : nonvacuity% Checked.Sim.MichaelisMenten.mm_half_conversion_universal := by\n  obtain ⟨s, e, c, p, h⟩ := Checked.Sim.MichaelisMenten.mm_solution_exists\n  exact ⟨s, e, c, p, h, 0, ⟨le_rfl, by norm_num⟩, trivial⟩\n\nend Checked.Trust.NV')
