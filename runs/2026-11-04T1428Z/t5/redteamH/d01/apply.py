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

LEAN = "import Checked.Sim.Duffing\nimport Checked.Trust.NonVacuity\n\n/-!\n# Duffing oscillator in natural units (scope note for `Checked.Sim.Duffing`)\n\nA corollary of `duffing_first_zero_sol`, stated for readers who want the quarter period of the\nhardening oscillator without fixing the units.\n-/\n\nnamespace Checked.Sim.DuffingNatural\nopen Set Checked.Sim.Duffing\n\n/-- Quarter period of the hardening Duffing oscillator in natural units. Measure time in units of\nthe linear period (rescale time by the linear frequency √k) and displacement in units of the release\namplitude: whatever the hardening coefficient β ≥ 0 of the oscillator x'' + k x + β x³ = 0 released\nfrom rest, every solution on the time interval [0, 6/5] is strictly positive for all times in\n[0, 1.192005] and strictly negative at time 1.192006, so its first zero (the quarter period) lies\nstrictly between 1.192005 and 1.192006 in these units. -/\ntheorem duffing_quarter_period_natural (x : ℝ → ℝ) (hx : IsDuffingSolution 1 1 1 0 (6 / 5) x) :\n    (∀ t ∈ Icc (0 : ℝ) (1192005 / 1000000), 0 < x t) ∧ x (1192006 / 1000000) < 0 := by\n  exact duffing_first_zero_sol x hx\n\nend Checked.Sim.DuffingNatural\n\nnamespace Checked.Trust.NV\n\ntheorem duffing_quarter_period_natural :\n    nonvacuity% Checked.Sim.DuffingNatural.duffing_quarter_period_natural := by\n  obtain ⟨x, hx⟩ := Checked.Sim.Duffing.duffing_solution_exists\n  exact ⟨x, hx, 0, ⟨le_rfl, by norm_num⟩, trivial⟩\n\nend Checked.Trust.NV\n"
path = root / 'Checked/Sim/DuffingNatural.lean'
assert not path.exists()
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Sim.DuffingNatural\n")
append("scripts/trust/headlines.txt", '# Duffing in natural units (run 2026-11-04T1428Z)\nChecked.Sim.DuffingNatural.duffing_quarter_period_natural\n')
