#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def sub(rel, old, new):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, "old text occurs %d times" % t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")

def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")

create("Checked/Sim/MMWindow.lean", 'import Checked.Sim.MichaelisMenten\n\nnamespace Checked.Sim.MichaelisMenten\nopen Set\n\n/-- Half-conversion of an enzyme assay at dilute enzyme: the full mass-action Michaelis–Menten\nmechanism E + S ⇌ C → E + P with rate constants k₁ = k₋₁ = k₂ = 1 and initial concentrations\n[E]₀ = 0.1mM, [S]₀ = 1.0mM, [C]₀ = [P]₀ = 0 (enzyme one tenth of the substrate, so the\nquasi-steady-state approximation holds). There is a solution of the rate equations on the time\ninterval [0, 13/5] (derivatives within the interval) whose product concentration stays strictly\nbelow 1/2 at every time in [0, 2.5665] and strictly above 1/2 at time 2.5666, so half of the\nsubstrate is converted between 2.5665 and 2.5666. -/\ntheorem mm_half_conversion_window :\n    ∃ s e c p : ℝ → ℝ, IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p ∧\n      (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) := by\n  obtain ⟨s, e, c, p, h⟩ := mm_solution_exists\n  exact ⟨s, e, c, p, h, mm_half_conversion h⟩\n\nend Checked.Sim.MichaelisMenten\n')
sub("Checked.lean", "import Checked.Sim.MMPin\n", "import Checked.Sim.MMPin\nimport Checked.Sim.MMWindow\n")
sub("scripts/trust/headlines.txt", "Checked.Sim.MichaelisMenten.mm_solution_exists\n",
    "Checked.Sim.MichaelisMenten.mm_solution_exists\nChecked.Sim.MichaelisMenten.mm_half_conversion_window\n")
