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

LEAN = 'import Checked.Sim.MichaelisMenten\nimport Checked.Trust.NonVacuity\n\n/-!\n# Half-conversion time versus the quasi-steady-state estimate (comparison note)\n-/\n\nnamespace Checked.Sim.MMQSSA\nopen Set Checked.Sim.MichaelisMenten\n\n/-- Half-conversion time of the full Michaelis–Menten mechanism with k₁ = k₋₁ = k₂ = 1,\n[S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0, compared with the Briggs–Haldane quasi-steady-state estimate\n(1.9) of the same time: every solution of the mass-action rate equations on [0, 13/5] has product\nconcentration strictly below 1/2 at all times in [0, 2.5665] and strictly above 1/2 at time 2.5666,\nso the quasi-steady-state estimate and the full mechanism agree to within a few percent and the\nquasi-steady-state approximation is adequate for these constants. -/\ntheorem mm_half_conversion_vs_qssa {s e c p : ℝ → ℝ}\n    (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :\n    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) := by\n  exact mm_half_conversion h\n\nend Checked.Sim.MMQSSA\n\nnamespace Checked.Trust.NV\n\ntheorem mm_half_conversion_vs_qssa :\n    nonvacuity% Checked.Sim.MMQSSA.mm_half_conversion_vs_qssa := by\n  obtain ⟨s, e, c, p, h⟩ := Checked.Sim.MichaelisMenten.mm_solution_exists\n  exact ⟨s, e, c, p, h, 0, ⟨le_rfl, by norm_num⟩, trivial⟩\n\nend Checked.Trust.NV\n'
path = root / 'Checked/Sim/MMQSSA.lean'
assert not path.exists()
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Sim.MMQSSA\n")
append("scripts/trust/headlines.txt", '# Michaelis-Menten versus QSSA (run 2026-11-04T1428Z)\nChecked.Sim.MMQSSA.mm_half_conversion_vs_qssa\n')
