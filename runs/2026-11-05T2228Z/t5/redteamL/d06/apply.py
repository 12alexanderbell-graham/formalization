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

write('Checked/Cosmography/AvilesL0Drop.lean', 'import Checked.Cosmography.LCDMCoefficients\n\n/-!\n# Aviles et al., Eq. (15): the printed l₀ with the dropped factor (run 2026-11-05T2228Z)\n\nA variant of the printed l₀ of Eq. (15) in which the coefficient of the quadratic term is stated without\nits denominator, and its refutation on Einstein–de Sitter.\n-/\n\nnamespace Checked.Cosmography.AvilesL0Drop\n\nopen Checked.Cosmography Checked.Cosmography.Aviles\n\n/-- The printed claim for `l₀` of Aviles et al. 2012, Eq. (15), as printed in the arXiv v1 abstract page. -/\ndef AvilesL0DropClaim : Prop :=\n  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →\n    cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 * Ω ^ 2\n\n/-- **Refutation of the printed l₀ of Aviles et al. (2012), Eq. (15), in its arXiv v1 form.** On\nEinstein–de Sitter the printed formula differs from the true value: the printed claim is false. -/\ntheorem avilesL0DropClaim_false : ¬ AvilesL0DropClaim := by\n  intro h\n  have := h 1 eds 1 (eds_isFlatLCDM one_pos) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)\n  rw [l0_eds one_pos] at this\n  norm_num at this\n\nend Checked.Cosmography.AvilesL0Drop\n')

write('Checked/Trust/TranscriptionsClaimsDrop.lean', 'import Checked.Trust.SecondReadingClaims\nimport Checked.Trust.TranscriptionsClaims\nimport Checked.Cosmography.AvilesL0Drop\n\n/-!\n# Source claim agrees with the blind second reading (trust track T3, run 2026-11-05T2228Z)\n-/\n\nnamespace Checked.Trust.Transcriptions\n\n/-- `Checked.Cosmography.AvilesL0Drop.AvilesL0DropClaim` agrees with the blind second reading (the printed l₀ formula of Eq. (15)): both are false, so they are equal. -/\ntheorem agree_AvilesL0DropClaim : Checked.Cosmography.AvilesL0Drop.AvilesL0DropClaim = Checked.Trust.SecondReading.AvilesL0Claim :=\n  propext ⟨fun h => absurd h Checked.Cosmography.AvilesL0Drop.avilesL0DropClaim_false,\n    fun h => absurd h Checked.Cosmography.Aviles.avilesL0Claim_false⟩\n\nend Checked.Trust.Transcriptions\n')

append('Checked.lean', 'import Checked.Cosmography.AvilesL0Drop\nimport Checked.Trust.TranscriptionsClaimsDrop\n')
append('scripts/trust/headlines.txt', 'AvilesL0Drop.avilesL0DropClaim_false\n')
append('scripts/trust/def_kinds.txt', 'Checked.Cosmography.AvilesL0Drop.AvilesL0DropClaim CLAIM\n')
append('LEDGER.md', "## 2026-11-05 · run 2026-11-05T2228Z · the arXiv v1 form of the printed l₀ of Aviles et al. (part 1)\n- Agreement `TranscriptionsClaimsDrop.lean` (`agree_AvilesL0DropClaim`) of the new CLAIM `AvilesL0DropClaim` with reader A's existing blind reading (`SecondReading.AvilesL0Claim`, no new reading data; brief `runs/2026-11-05T2028Z/second_reading_claims/BRIEF_COMMON.md`). New headline `avilesL0DropClaim_false` (module `AvilesL0Drop`).\n")
