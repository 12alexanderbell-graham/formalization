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

LEAN = "import Mathlib.Analysis.SpecialFunctions.Sqrt\nimport Mathlib.Tactic.NormNum\nimport Checked.Trust.NonVacuity\n\n/-! The natural frequency of the harmonic oscillator with a negative spring constant, `InvertedOscillator`. -/\n\nnamespace Checked.Math.InvertedOscillator\n\n/-- For every spring constant k < 0 and mass m > 0, the angular frequency ω = √(k/m) of the\nharmonic oscillator m x'' = −k x is 0: an inverted potential has a vanishing natural frequency. -/\ntheorem inverted_frequency (k m : ℝ) (hk : k < 0) (hm : 0 < m) : Real.sqrt (k / m) = 0 :=\n  Real.sqrt_eq_zero_of_nonpos (div_neg_of_neg_of_pos hk hm).le\n\ntheorem nv_inverted_frequency : nonvacuity% Checked.Math.InvertedOscillator.inverted_frequency :=\n  ⟨-1, 1, by norm_num, by norm_num, trivial⟩\n\nend Checked.Math.InvertedOscillator\n"

create('Checked/Math/InvertedOscillator.lean', LEAN)
append('Checked.lean', 'import Checked.Math.InvertedOscillator\n')
append('scripts/trust/headlines.txt', 'Checked.Math.InvertedOscillator.inverted_frequency' + '\n')
