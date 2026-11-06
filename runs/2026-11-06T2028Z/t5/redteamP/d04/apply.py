#!/usr/bin/env python3
import sys, pathlib
ROOT = pathlib.Path(sys.argv[1])

def rep(rel, old, new):
    p = ROOT / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, old[:60], t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")

def append(rel, text):
    p = ROOT / rel
    t = p.read_text(encoding="utf-8")
    if t and not t.endswith("\n"):
        t += "\n"
    p.write_text(t + text, encoding="utf-8")

def create(rel, text):
    p = ROOT / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")

LEAN = "import Mathlib.Analysis.SpecialFunctions.ExpDeriv\nimport Mathlib.Tactic.NormNum\nimport Checked.Math.Gelfand\nimport Checked.Math.GelfandExists\nimport Checked.Trust.NonVacuity\n\n/-! Gelfand problem, `GelfandBracket`: the radial Gelfand problem in the three-dimensional ball, the\npeak and a lower bound for its height, read off from `Checked.Math.Gelfand.gelfand_ball_critical`. -/\n\nnamespace Checked.Math.GelfandBracket\nopen Set\n\n/-- Gelfand problem in the three-dimensional ball, radial branch: for every S ≥ 41/10 and every\nsolution w of w'' + (2/s)w' + e^w = 0 on (0, S] with w(0) = 0, w differentiable on [0, S] with\nderivative φ and φ continuous at 0, there is a point s₁ between 4.071496844 and 4.071496845 where\nthe Gelfand parameter λ = s₁² e^{w(s₁)} reproduces the critical parameter 3.321992118 to within\n10⁻¹². -/\ntheorem critical_bracket (S : ℝ) (hS : 41 / 10 ≤ S) (w φ : ℝ → ℝ)\n    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)\n    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)\n    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,\n      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)\n    (h0 : w 0 = 0) :\n    ∃ s₁ : ℝ, 4.071496844 ≤ s₁ ∧ s₁ ≤ 4.071496845 ∧\n      3.321992118 ≤ s₁ ^ 2 * Real.exp (w s₁) := by\n  obtain ⟨s₁, h1, h2, -, h4, -⟩ :=\n    Checked.Math.Gelfand.gelfand_ball_critical S hS w φ hw hφ0 hφ h0\n  exact ⟨s₁, h1, h2, h4⟩\n\ntheorem nv_critical_bracket : nonvacuity% Checked.Math.GelfandBracket.critical_bracket := by\n  obtain ⟨w, φ, hw, hφ0, hφ, h0⟩ :=\n    Checked.Math.GelfandExists.exists_solution (41 / 10) (by norm_num)\n  exact ⟨41 / 10, le_rfl, w, φ, hw, hφ0, hφ, h0, trivial⟩\n\nend Checked.Math.GelfandBracket\n"

create('Checked/Math/GelfandBracket.lean', LEAN)
append('Checked.lean', 'import Checked.Math.GelfandBracket\n')
append('scripts/trust/headlines.txt', 'Checked.Math.GelfandBracket.critical_bracket' + '\n')
append('scripts/trust/literal_readings.txt', 'Checked.Math.GelfandBracket.critical_bracket Checked.Trust.SecondReading.gelfandRhs Checked.Trust.SecondReading.gelfandLambda Checked.Trust.SecondReading.gelfandCentre Checked.Trust.SecondReading.gelfandRegular Checked.Trust.SecondReading.gelfandDomain Checked.Trust.SecondReading.gelfandPunctured\n')
append('LEDGER.md', '\n## Run 2026-11-06T2228Z (scheduled; part 5)\n- **Mathematics: lower bound of the Gelfand peak height** (part 5). New headline `critical_bracket` (the peak location with the lower half of the height bound of `gelfand_ball_critical`), non-vacuity witness in its module.\n- **Literal readings** (literal_readings.txt): `critical_bracket` with gelfandRhs, gelfandLambda, gelfandCentre, gelfandRegular, gelfandDomain, gelfandPunctured (the run-1428Z reading of the radial problem, unchanged; the statement repeats its token spans).\n')
