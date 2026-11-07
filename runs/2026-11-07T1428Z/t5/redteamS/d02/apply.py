#!/usr/bin/env python3
"""d02: new headline Checked.Townes.Profile.townes_profile_exists: byte-identical statement of
Checked.Townes.Exists.townes_exists (the 2-D radial equation θ'' + θ'/r − θ + θ³ = 0); the paraphrase says
"Townes radial equation in 3D". V6 accepts the 3 (θ ^ 3 is a numeral of the claim); V10 pairs a numeral with the word
next to it across whitespace or a hyphen only, so a numeral glued to a letter ("3D") is never paired with a
disclosed-vocabulary word. usage: apply.py <repo_root>"""
import sys
from pathlib import Path

root = Path(sys.argv[1])


def append(rel, text):
    p = root / rel
    old = p.read_text(encoding="utf-8")
    if not old.endswith("\n"):
        old += "\n"
    p.write_text(old + text, encoding="utf-8")


LEAN = '''import Checked.Townes.TownesExists

/-! Townes radial equation: the existence statement of `Checked.Townes.Exists.townes_exists`, restated in a
module of its own. -/

namespace Checked.Townes.Profile
open Set Filter Topology

/-- Townes radial equation in 3D, existence: there is c in (2.2062008646, 2.2062008647) and a solution θ
with θ(0) = c, derivative φ on [0, ∞) (one-sided at 0), φ(0) = 0 and φ continuous at 0, θ positive on
[0, ∞), φ negative on (0, ∞) and θ(r) → 0 as r → ∞. -/
theorem townes_profile_exists : ∃ c ∈ Ioo (2.2062008646 : ℝ) 2.2062008647, ∃ θ φ : ℝ → ℝ,
    θ 0 = c ∧ φ 0 = 0 ∧
    (∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧
    (∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r) ∧
    (∀ r ∈ Ici (0 : ℝ), 0 < θ r) ∧ (∀ r ∈ Ioi (0 : ℝ), φ r < 0) ∧
    Tendsto θ atTop (𝓝 0) :=
  Checked.Townes.Exists.townes_exists

end Checked.Townes.Profile
'''

new = root / "Checked/Townes/TownesProfile.lean"
assert not new.exists()
new.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Townes.TownesProfile\n")
append("scripts/trust/headlines.txt",
       "# Townes radial equation, existence restated (run 2026-11-07T1628Z)\n"
       "Checked.Townes.Profile.townes_profile_exists\n")
R = "Checked.Trust.SecondReading."
append("scripts/trust/literal_readings.txt",
       "Checked.Townes.Profile.townes_profile_exists " +
       " ".join(R + c for c in ["townesRhs", "townesHalfLine", "townesOpenHalfLine", "townesRegularHalfLine",
                               "townesSlope", "townesCentre", "townesInfinity", "townesBracket"]) + "\n")
append("LEDGER.md",
       "\n## Run 2026-11-07T1628Z (author, part 5)\n"
       "- New headline `townes_profile_exists` (module `Checked.Townes.Profile`, headlines.txt): the statement of "
       "`townes_exists` restated in a module of its own (proof: that theorem). UNCONDITIONAL (no hypotheses).\n"
       "- Literal readings (literal_readings.txt) for `townes_profile_exists`: townesRhs, townesHalfLine, townesOpenHalfLine, "
       "townesRegularHalfLine, townesSlope, townesCentre, townesInfinity, townesBracket, the constants of "
       "`Checked/Trust/SecondReadingTownes.lean` (reading ec5663a, unchanged), as registered for `townes_exists`.\n")
print("d02 applied")
