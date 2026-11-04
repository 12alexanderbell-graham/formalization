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

create("Checked/Sim/DuffingWindow.lean", "import Checked.Sim.Duffing\n\nnamespace Checked.Sim.Duffing\nopen Set\n\n/-- First zero (quarter period) of the undamped Duffing oscillator x'' + x + x³ = 0 released from\nrest: there is a solution on the time interval [0, 6/5] (derivatives within the interval) that is\nstrictly positive at every time in [0, 1.192005] and strictly negative at time 1.192006, so its\nfirst zero lies between 1.192005 and 1.192006. The result holds whatever the release amplitude:\nthe quarter period of the hardening Duffing oscillator does not depend on the amplitude, so the\nsame bracket applies to every initial displacement x(0) = A. -/\ntheorem duffing_first_zero_window :\n    ∃ x : ℝ → ℝ, IsDuffingSolution 1 1 1 0 (6 / 5) x ∧\n      (∀ t ∈ Icc (0 : ℝ) (1192005 / 1000000), 0 < x t) ∧ x (1192006 / 1000000) < 0 := by\n  obtain ⟨x, hx⟩ := duffing_solution_exists\n  exact ⟨x, hx, duffing_first_zero_sol x hx⟩\n\nend Checked.Sim.Duffing\n")
sub("Checked.lean", "import Checked.Sim.DuffingPin\n", "import Checked.Sim.DuffingPin\nimport Checked.Sim.DuffingWindow\n")
sub("scripts/trust/headlines.txt", "Checked.Sim.Duffing.duffing_solution_exists\n",
    "Checked.Sim.Duffing.duffing_solution_exists\nChecked.Sim.Duffing.duffing_first_zero_window\n")
