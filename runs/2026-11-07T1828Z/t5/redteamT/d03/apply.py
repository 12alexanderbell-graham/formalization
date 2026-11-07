
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def append_line(rel, line, must_not_contain=None):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if must_not_contain is not None:
        assert must_not_contain not in s
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + line + "\n", encoding="utf-8")

def create(rel, text):
    p = root / rel
    assert not p.exists()
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")

def reading_line(src_headline_suffix, new_full):
    s = (root / "scripts/trust/literal_readings.txt").read_text(encoding="utf-8")
    ls = [l for l in s.splitlines() if l.startswith(src_headline_suffix + " ")]
    assert len(ls) == 1
    return new_full + ls[0][len(src_headline_suffix):]

FULL = "Checked.Townes.Profile.townes_profile_exists"
LEAN = """import Checked.Townes.TownesExists

/-! Townes soliton, `TownesProfile`: the ground state of the Townes radial equation, restated from `Checked.Townes.Exists.townes_exists` with the same conclusion. -/

namespace Checked.Townes.Profile
open Set Filter Topology

/-- Townes radial equation, existence: there is c in (2.2062008646, 2.2062008647) and a solution θ with
θ(0) = c, derivative φ on [0, ∞) (one-sided at 0), φ(0) = 0 and φ continuous at 0, where φ on (0, ∞) has the
derivative `-(1 / r * φ r) + θ r + θ r ^ 3`, θ positive on [0, ∞), φ negative on (0, ∞) and θ(r) → 0 as
r → ∞. -/
theorem townes_profile_exists : ∃ c ∈ Ioo (2.2062008646 : ℝ) 2.2062008647, ∃ θ φ : ℝ → ℝ,
    θ 0 = c ∧ φ 0 = 0 ∧
    (∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧
    (∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r) ∧
    (∀ r ∈ Ici (0 : ℝ), 0 < θ r) ∧ (∀ r ∈ Ioi (0 : ℝ), φ r < 0) ∧
    Tendsto θ atTop (𝓝 0) :=
  Checked.Townes.Exists.townes_exists

end Checked.Townes.Profile
"""
create("Checked/Townes/TownesProfile.lean", LEAN)
append_line("Checked.lean", "import Checked.Townes.TownesProfile", "TownesProfile")
append_line("scripts/trust/headlines.txt", FULL, "TownesProfile")
append_line("scripts/trust/literal_readings.txt",
            reading_line("Checked.Townes.Exists.townes_exists", FULL), "TownesProfile")
append_line("LEDGER.md",
    "- 2026-11-07, run 2026-11-07T1828Z — **New headline `Checked.Townes.Profile.townes_profile_exists` "
    "(Townes ground state; only Mathlib definitions in the statement).** Statement byte-identical to "
    "`townes_exists` (proof: that theorem); unconditional, so no NV witness. Literal readings: "
    "`townes_profile_exists` registered in `scripts/trust/literal_readings.txt` with the same readers as "
    "`townes_exists` (townesRhs, townesHalfLine, townesOpenHalfLine, townesRegularHalfLine, townesSlope, "
    "townesCentre, townesInfinity, townesBracket). Relock, TRUST_MAP, CLAIMS, packet: regenerated.",
    "townes_profile_exists")
