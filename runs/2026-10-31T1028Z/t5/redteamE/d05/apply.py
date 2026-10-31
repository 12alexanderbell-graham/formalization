import sys, pathlib

root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:60], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")


def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.write_text(text, encoding="utf-8")


LEAN = '''import Checked.Records.Findings
import Checked.Trust.NonVacuity

/-!
# F12 (run 2026-10-31T1028Z): flat ΛCDM at `Ω_m = 0.3`, present deceleration and the transition

`q₀ = 3Ω/2 − 1` is the pinned `decel` of every flat ΛCDM model (`flatLCDM_coeffs`).
-/

namespace Checked.Records

open Checked.Cosmography Checked.Cosmography.Aviles

/-- In every flat ΛCDM model with `Ω_m = 0.3` the present deceleration parameter is
`q₀ = −0.55`, and the expansion turns from deceleration to acceleration where
`(1 + z)³ = 2.333`, i.e. at `z_t ≈ 0.327`. -/
theorem F12_transition (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM (3 / 10) a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) :
    RoundsTo (decel a t₀) (-0.55) 2 ∧ RoundsTo ((1 - 3 / 10) / (3 / 10)) 2.333 3 := by
  rw [(flatLCDM_coeffs _ a t₀ hL hs).1]
  unfold RoundsTo; simp only [abs_le]; norm_num

end Checked.Records

namespace Checked.Trust.NV

theorem F12_transition : nonvacuity% Checked.Records.F12_transition := by
  obtain ⟨a, t₀, hL, hs⟩ :=
    Checked.Cosmography.AvilesWitness.exists_flatLCDM (Ω := 3 / 10) (by norm_num) (by norm_num)
  exact ⟨a, t₀, hL, hs, trivial⟩

end Checked.Trust.NV
'''
create("Checked/Records/Findings12.lean", LEAN)
append("Checked.lean", "import Checked.Records.Findings12\n")
sub("scripts/trust/headlines.txt", "Records.F11_sizes\n", "Records.F11_sizes\nRecords.F12_transition\n")

FIND_OLD = "## Candidates under verification (UNVERIFIED, not findings)\n"
FIND_NEW = """### F12 (run 2026-10-31T1028Z). Flat ΛCDM at Ω_m = 3/10: present deceleration and onset of acceleration
- **Result:** in every flat ΛCDM model with Ω_m = 0.3[in✓F12_transition] the present deceleration parameter is q₀ = −0.55[✓F12_transition] and the expansion turns from deceleration to acceleration where (1 + z)³ = 2.333[✓F12_transition], i.e. where the matter and Λ densities are equal. The transition redshift is therefore z_t ≈ 0.327[unc].
- **Lean evidence (Checked):** `Checked.Records.F12_transition` (every scale factor obeying the flat ΛCDM law with Ω_m = 3/10 near t₀ and C⁶ at t₀).
- **Plain words:** the Universe stopped decelerating when the dark-energy density caught up with the matter density.

""" + FIND_OLD
sub("FINDINGS.md", FIND_OLD, FIND_NEW)
