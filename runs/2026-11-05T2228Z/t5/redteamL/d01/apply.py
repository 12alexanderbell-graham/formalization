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

write('Checked/Cosmography/AvilesS0.lean', 'import Checked.Cosmography.LCDMCoefficients\n\n/-!\n# Aviles et al., Eq. (15): the printed s₀ (run 2026-11-05T2228Z)\n\nThe paper prints the cosmographic coefficients of flat ΛCDM, among them the snap s₀. The claim\nbelow is the printed s₀, frozen, and its refutation on Einstein–de Sitter,\nin the style of the refutations of l₀ and m₀ in `Checked.Cosmography.Aviles`.\n-/\n\nnamespace Checked.Cosmography.AvilesS0\n\nopen Checked.Cosmography Checked.Cosmography.Aviles\n\n/-- The printed claim for `s₀` (frozen verbatim from Eq. (15) of Aviles et al. 2012). -/\ndef AvilesS0Claim : Prop :=\n  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →\n    cosmoCoeff 4 a t₀ = 1 - 9 * Ω\n\nlemma s0_eds {t : ℝ} (ht : 0 < t) : cosmoCoeff 4 eds t = -7 / 2 := by\n  rw [cosmoCoeff_eds 4 ht]\n  simp [descPochhammer_succ_right] <;> norm_num\n\n/-- **Refutation of the printed s₀ in Eq. (15) of Aviles et al. (2012).** On Einstein–de Sitter the\nprinted formula differs from the true value of the snap: the printed claim is false. -/\ntheorem avilesS0Claim_false : ¬ AvilesS0Claim := by\n  intro h\n  have := h 1 eds 1 (eds_isFlatLCDM one_pos) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)\n  rw [s0_eds one_pos] at this\n  norm_num at this\n\nend Checked.Cosmography.AvilesS0\n')

write('Checked/Trust/SecondReadingClaimsD.lean', 'import Mathlib.Data.Real.Basic\nimport Checked.Cosmography.LCDMCoefficients\n\n/-!\n# Blind second reading of the printed s₀ of Aviles et al. (trust track T3, run 2026-11-05T2228Z)\nTypeset-only reading of Eq. (15), p. 10 (brief `runs/2026-11-05T2228Z/second_reading_claims/BRIEF_D.md`).\n-/\n\nnamespace Checked.Trust.SecondReading\n\nopen Checked.Cosmography.Aviles\n\n/-- Aviles, Gruber, Luongo, Quevedo, PRD 86, 123516 (2012), arXiv:1204.2007 v1 and v2 (identical),\nEq. (15), p. 10.  Printed: `s₀ = 1 − 9Ω_m`. -/\nnoncomputable def avilesS0 (Ω : ℝ) : ℝ := 1 - 9 * Ω\n\n/-- `Checked.Cosmography.AvilesS0.AvilesS0Claim` with the printed s₀ formula of Eq. (15) as read by the\nblind second reader. -/\ndef AvilesS0Claim : Prop :=\n  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →\n    cosmoCoeff 4 a t₀ = avilesS0 Ω\n\nend Checked.Trust.SecondReading\n')

write('Checked/Trust/TranscriptionsClaimsD.lean', 'import Checked.Trust.SecondReadingClaimsD\nimport Checked.Cosmography.AvilesS0\n\n/-!\n# Source claim agrees with its blind second reading (trust track T3, run 2026-11-05T2228Z)\n-/\n\nnamespace Checked.Trust.Transcriptions\n\n/-- `Checked.Cosmography.AvilesS0.AvilesS0Claim` agrees with the blind second reading (the printed s₀ formula of Eq. (15)). -/\ntheorem agree_AvilesS0Claim : Checked.Cosmography.AvilesS0.AvilesS0Claim = Checked.Trust.SecondReading.AvilesS0Claim := by\n  rfl\n\nend Checked.Trust.Transcriptions\n')

append('Checked.lean', 'import Checked.Cosmography.AvilesS0\nimport Checked.Trust.SecondReadingClaimsD\nimport Checked.Trust.TranscriptionsClaimsD\n')
append('scripts/trust/headlines.txt', 'AvilesS0.avilesS0Claim_false\n')
append('scripts/trust/def_kinds.txt', 'Checked.Cosmography.AvilesS0.AvilesS0Claim CLAIM\n')
append('LEDGER.md', "## 2026-11-05 · run 2026-11-05T2228Z · the printed s₀ of Aviles et al. Eq. (15), read twice (part 1)\n- **Blind second reading** (Sonnet, typeset only; brief `runs/2026-11-05T2228Z/second_reading_claims/BRIEF_D.md`), copied verbatim to `SecondReadingClaimsD.lean` (`avilesS0`); generated second-reading claim `AvilesS0Claim` (the program claim's text with the blind reader's constant substituted; quantifiers and hypotheses are the program's). Agreement `TranscriptionsClaimsD.lean` (`agree_AvilesS0Claim`, by `rfl`): agrees. New headline `avilesS0Claim_false` with its CLAIM `AvilesS0Claim`.\n")
