#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def write(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)

def append(rel, text):
    p = root / rel
    s = p.read_text()
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text)

write('Checked/Cosmography/AvilesJ0.lean', 'import Checked.Cosmography.LCDMCoefficients\n\n/-!\n# Aviles et al., Eq. (15): the printed j₀ (run 2026-11-05T2228Z)\n\nThe jerk of flat ΛCDM is j₀ = 1 for every matter fraction. The claim below is the printed j₀ of Eq. (15)\nas frozen, with its refutation on Einstein–de Sitter.\n-/\n\nnamespace Checked.Cosmography.AvilesJ0\n\nopen Checked.Cosmography Checked.Cosmography.Aviles\n\n/-- The printed claim for `j₀` (frozen verbatim from Eq. (15) of Aviles et al. 2012). -/\ndef AvilesJ0Claim : Prop :=\n  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →\n    cosmoCoeff 3 a t₀ = 1 + Ω\n\nlemma j0_eds {t : ℝ} (ht : 0 < t) : cosmoCoeff 3 eds t = 1 := by\n  rw [cosmoCoeff_eds 3 ht]\n  simp [descPochhammer_succ_right] <;> norm_num\n\n/-- **Refutation of the printed j₀ in Eq. (15) of Aviles et al. (2012).** On Einstein–de Sitter the\nprinted formula differs from the true jerk: the printed claim is false. -/\ntheorem avilesJ0Claim_false : ¬ AvilesJ0Claim := by\n  intro h\n  have := h 1 eds 1 (eds_isFlatLCDM one_pos) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)\n  rw [j0_eds one_pos] at this\n  norm_num at this\n\nend Checked.Cosmography.AvilesJ0\n')

append('Checked.lean', 'import Checked.Cosmography.AvilesJ0\n')
append('scripts/trust/headlines.txt', 'AvilesJ0.avilesJ0Claim_false\n')
append('scripts/trust/def_kinds.txt', 'Checked.Cosmography.AvilesJ0.AvilesJ0Claim CLAIM\n')
append('LEDGER.md', '## 2026-11-05 · run 2026-11-05T2228Z · the printed j₀ of Aviles et al. Eq. (15) (part 1)\n- New CLAIM `AvilesJ0Claim` and headline `avilesJ0Claim_false` (module `AvilesJ0`), proved on Einstein–de Sitter like the l₀ and m₀ refutations. No new second reading: the claim writes no numeral other than 0 and 1.\n')
