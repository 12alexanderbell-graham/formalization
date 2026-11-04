#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def rep(path, old, new):
    p = root / path
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (path, old)
    p.write_text(s.replace(old, new), encoding="utf-8")

def append(path, text):
    p = root / path
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")

LEAN = 'import Checked.Sim.MichaelisMenten\nimport Checked.Trust.NonVacuity\n\n/-!\n# Half-conversion time of the Michaelis-Menten mechanism in natural units (scope note)\n\nA corollary of `mm_half_conversion`, restated for readers who want the dimensionless number.\n-/\n\nnamespace Checked.Sim.MMNatural\nopen Set Checked.Sim.MichaelisMenten\n\n/-- Half-conversion time of the full Michaelis–Menten mechanism in natural units. In units of\n[S]₀ for concentrations and 1/k₂ for time, whatever the rate constants k₁ and k₋₁ and whatever the\nenzyme loading [E]₀/[S]₀, every solution of the mass-action rate equations on the time interval\n[0, 13/5] has product concentration strictly below 1/2 at all times in [0, 2.5665] and strictly\nabove 1/2 at time 2.5666, so half of the substrate is first converted to product between 2.5665 and\n2.5666 time units. -/\ntheorem mm_half_conversion_natural {s e c p : ℝ → ℝ}\n    (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :\n    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) := by\n  exact mm_half_conversion h\n\nend Checked.Sim.MMNatural\n\nnamespace Checked.Trust.NV\n\ntheorem mm_half_conversion_natural :\n    nonvacuity% Checked.Sim.MMNatural.mm_half_conversion_natural := by\n  obtain ⟨s, e, c, p, h⟩ := Checked.Sim.MichaelisMenten.mm_solution_exists\n  exact ⟨s, e, c, p, h, 0, ⟨le_rfl, by norm_num⟩, trivial⟩\n\nend Checked.Trust.NV\n'
path = root / 'Checked/Sim/MMNatural.lean'
assert not path.exists()
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Sim.MMNatural\n")
append("scripts/trust/headlines.txt", '# Michaelis-Menten in natural units (run 2026-11-04T1428Z)\nChecked.Sim.MMNatural.mm_half_conversion_natural\n')
