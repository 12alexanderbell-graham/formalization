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

LEAN = 'import Checked.Sim.MichaelisMenten\n\nnamespace Checked.Sim.MichaelisMenten\nopen Set\n\n/-- Half-conversion time of the full Michaelis–Menten mechanism (mass-action rate equations with the\nexplicit complex): every solution on [0, 13/5] has product concentration strictly below 1/2 on\n[0, 2.5665] and strictly above 1/2 at 2.5666. The bracket holds whether the enzyme is scarce (the\nBriggs–Haldane quasi-steady-state regime) or abundant, so it also dates the half-conversion of the\nMichaelis–Menten rate law. -/\ntheorem mm_half_conversion_regimes {s e c p : ℝ → ℝ} (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :\n    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) :=\n  mm_half_conversion h\n\nend Checked.Sim.MichaelisMenten\n'
wr('Checked/Sim/MMRegimes.lean', LEAN)
app("Checked.lean", "import Checked.Sim.MMRegimes\n")
app("scripts/trust/headlines.txt", 'Checked.Sim.MichaelisMenten.mm_half_conversion_regimes\n')
rep("Checked/Trust/Witnesses.lean", 'import Checked.Sim.Duffing\nimport Checked.Sim.MichaelisMenten\n', 'import Checked.Sim.Duffing\nimport Checked.Sim.MichaelisMenten\nimport Checked.Sim.MMRegimes\n')
rep("Checked/Trust/Witnesses.lean", "\nend Checked.Trust.NV", '\ntheorem mm_half_conversion_regimes : nonvacuity% Checked.Sim.MichaelisMenten.mm_half_conversion_regimes := by\n  obtain ⟨s, e, c, p, h⟩ := Checked.Sim.MichaelisMenten.mm_solution_exists\n  exact ⟨s, e, c, p, h, 0, ⟨le_rfl, by norm_num⟩, trivial⟩\n\nend Checked.Trust.NV')
