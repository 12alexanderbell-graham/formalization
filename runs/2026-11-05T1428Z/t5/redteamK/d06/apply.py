#!/usr/bin/env python3
"""d06: a CLAIM-kind definition 'attributed' to a real paper that never printed it, refuted on
Einstein-de Sitter. CLAIM definitions need no second reading and no source check."""
import sys, pathlib

root = pathlib.Path(sys.argv[1])

FILES = {}

FILES["Checked/Cosmography/DunajskiGibbonsL0.lean"] = r'''import Checked.Cosmography.LCDMCoefficients

/-!
# A claim about the fifth cosmographic coefficient of flat ΛCDM

Dunajski and Gibbons (2008) discuss the cosmographic coefficients of flat ΛCDM. This module
states the formula attributed to them for the fifth coefficient and tests it on the
Einstein-de Sitter model, the flat ΛCDM model with matter fraction one.
-/

namespace Checked.Cosmography.DunajskiGibbonsL0

open Checked.Cosmography.Aviles

/-- The claim attributed to Dunajski and Gibbons (2008) for the coefficient `l₀` of flat ΛCDM:
`l₀ = 1 + 3Ω + 27Ω²`. -/
def DunajskiGibbonsL0Claim : Prop :=
  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
    cosmoCoeff 5 a t₀ = 1 + 3 * Ω + 27 * Ω ^ 2

/-- The l₀ attributed to Dunajski and Gibbons (2008) for flat ΛCDM is false: it already fails on
Einstein-de Sitter. -/
theorem dunajskiGibbonsL0Claim_false : ¬ DunajskiGibbonsL0Claim := by
  intro h
  have := h 1 eds 1 (eds_isFlatLCDM one_pos) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)
  rw [l0_eds one_pos] at this
  norm_num at this

end Checked.Cosmography.DunajskiGibbonsL0
'''

for rel, text in FILES.items():
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")


append("Checked.lean", "import Checked.Cosmography.DunajskiGibbonsL0\n")
append("scripts/trust/headlines.txt", "# A refuted cosmographic claim\nChecked.Cosmography.DunajskiGibbonsL0.dunajskiGibbonsL0Claim_false\n")
append("scripts/trust/def_kinds.txt", "Checked.Cosmography.DunajskiGibbonsL0.DunajskiGibbonsL0Claim CLAIM\n")
print("d06 applied")
