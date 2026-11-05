#!/usr/bin/env python3
import sys, pathlib

root = pathlib.Path(sys.argv[1])


def write_new(rel, text):
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


def register(module, headlines, kinds=(), group=None):
    s = (root / "Checked.lean").read_text(encoding="utf-8")
    assert ("import " + module + "\n") not in s
    append("Checked.lean", "import " + module + "\n")
    h = ("\n# " + group + "\n" if group else "") + "".join(x + "\n" for x in headlines)
    append("scripts/trust/headlines.txt", h)
    if kinds:
        append("scripts/trust/def_kinds.txt", "".join(k + "\n" for k in kinds))

LEAN = r'''import Checked.Cosmography.LCDMCoefficients

/-!
# Candidate C2, third coefficient: the printed s₀ of Aviles et al. Eq. (15)

Source (typeset text, run 2026-10-30T0220Z, p. 10 of arXiv v2): the paper prints the closed form of
`s₀` for flat ΛCDM next to `q₀`, `j₀`, `l₀` and `m₀` in Eq. (15). Here the printed claim for `s₀` is
stated as a proposition and refuted on Einstein-de Sitter, by the correct coefficients
`flatLCDM_coeffs`.
-/

namespace Checked.Cosmography.AvilesS0

open Checked.Cosmography.Aviles

/-- The printed claim for `s₀` (frozen verbatim from Eq. (15)). -/
def AvilesS0Claim : Prop :=
  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →
    cosmoCoeff 4 a t₀ = 1 - 9 * Ω

/-- **Refutation of the printed s₀ in Eq. (15).** On Einstein-de Sitter the printed formula and the
true value of `s₀` differ, so the printed claim is false. -/
theorem avilesS0Claim_false : ¬ AvilesS0Claim := by
  intro h
  have h1 := h 1 eds 1 (eds_isFlatLCDM one_pos) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)
  have h2 := (flatLCDM_coeffs 1 eds 1 (eds_isFlatLCDM one_pos)
    (Real.contDiffAt_rpow_const_of_ne one_ne_zero)).2.2.1
  rw [h2] at h1
  norm_num at h1

end Checked.Cosmography.AvilesS0
'''

write_new('Checked/Cosmography/AvilesS0.lean', LEAN)
register('Checked.Cosmography.AvilesS0', ['Checked.Cosmography.AvilesS0.avilesS0Claim_false'], ('Checked.Cosmography.AvilesS0.AvilesS0Claim CLAIM',), 'Aviles snap claim')
