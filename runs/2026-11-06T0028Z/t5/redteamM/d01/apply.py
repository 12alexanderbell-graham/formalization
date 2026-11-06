#!/usr/bin/env python3
"""d01: a misattributed refutation. New headline in a new file: the "printed s0" of Aviles et al. Eq. (15)
is written as a LITERAL inside the statement (1 - 9 * Omega) instead of a PRINTED definition.  Usage: apply.py <repo_root>"""
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def write_new(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")

def append(rel, text):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    if not t.endswith("\n"):
        t += "\n"
    p.write_text(t + text, encoding="utf-8")

LEAN = '''import Checked.Cosmography.LCDMWitness
import Checked.Trust.NonVacuity

/-!
# Eq. (15) of Aviles, Gruber, Luongo, Quevedo (PRD 86, 123516): the printed s₀

Companion of `Checked.Cosmography.AvilesWitness.printedL0_false_at` for the fourth cosmographic
coefficient s₀ = a⁽⁴⁾/(aH⁴). Eq. (15) prints the flat ΛCDM value as 1 − 9Ω_m; the correct value is
1 − 9Ω_m halved (`Checked.Cosmography.Aviles.flatLCDM_coeffs`), so the printed s₀ is wrong for every
Ω_m ≠ 0, in the same way as the printed l₀ and m₀. The proof reuses the witnesses of
`AvilesWitness`: its sinh-power models realise every Ω ∈ (0,1).
-/

namespace Checked.Cosmography.AvilesS0

open Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.AvilesWitness

/-- The printed s₀ of Eq. (15) is false at every Ω ∈ (0,1). -/
theorem printedS0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ¬ ∀ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
      cosmoCoeff 4 a t₀ = 1 - 9 * Ω := by
  intro h
  obtain ⟨a, t₀, hL, hs⟩ := exists_flatLCDM h0 h1
  have e := h a t₀ hL hs
  rw [(flatLCDM_coeffs Ω a t₀ hL hs).2.2.1] at e
  linarith

end Checked.Cosmography.AvilesS0

namespace Checked.Trust.NV

theorem printedS0_false_at : nonvacuity% Checked.Cosmography.AvilesS0.printedS0_false_at :=
  ⟨1 / 2, by norm_num, by norm_num, trivial⟩

end Checked.Trust.NV
'''

write_new("Checked/Cosmography/AvilesS0.lean", LEAN)
append("Checked.lean", "import Checked.Cosmography.AvilesS0\n")
append("scripts/trust/headlines.txt", "# Aviles et al. Eq. (15): the printed s0 (run 2026-11-06T0028Z, red team M)\nAvilesS0.printedS0_false_at\n")
print("d01 applied")
