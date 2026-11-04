import sys, os
root = sys.argv[1]
def P(p): return os.path.join(root, p)
def rd(p):
    with open(P(p), encoding="utf-8") as f: return f.read()
def wr(p, s):
    with open(P(p), "w", encoding="utf-8") as f: f.write(s)
def append(p, text):
    s = rd(p)
    if not s.endswith("\n"): s += "\n"
    wr(p, s + text)
def create(p, text):
    assert not os.path.exists(P(p)), p
    os.makedirs(os.path.dirname(P(p)), exist_ok=True)
    wr(p, text)
LEAN = 'import Checked.Sim.MichaelisMenten\nimport Checked.Trust.NonVacuity\n\n/-!\n# Half-conversion in the Michaelis–Menten network, restated with the concentration names S, E, P, C\n-/\n\nnamespace Checked.Sim.MMNames\nopen Set Checked.Sim.MichaelisMenten\n\n/-- Certified half-conversion time of the Michaelis–Menten network, stated for the concentration `C`. -/\ntheorem substrate_half {S E P C : ℝ → ℝ}\n    (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) S E P C) :\n    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), C t < 1 / 2) ∧ 1 / 2 < C (25666 / 10000) :=\n  mm_half_conversion h\n\nend Checked.Sim.MMNames\n\nnamespace Checked.Trust.NV\n\ntheorem substrate_half : nonvacuity% Checked.Sim.MMNames.substrate_half := by\n  obtain ⟨s, e, c, p, h⟩ := Checked.Sim.MichaelisMenten.mm_solution_exists\n  exact ⟨s, e, c, p, h, 0, ⟨le_rfl, by norm_num⟩, trivial⟩\n\nend Checked.Trust.NV\n'
create('Checked/Sim/MMNames.lean', LEAN)
append('Checked.lean', 'import Checked.Sim.MMNames\n')
append('scripts/trust/headlines.txt', 'Checked.Sim.MMNames.substrate_half\n')
append('scripts/trust/def_kinds.txt', '\n')
print('applied')
