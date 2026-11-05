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

write('Checked/Cosmography/AvilesM0Root.lean', 'import Checked.Cosmography.LCDMCoefficients\n\n/-!\n# Aviles et al., Eq. (15): the printed m₀ at the special matter fraction (run 2026-11-05T2228Z)\n\nThe printed m₀ of Eq. (15) for flat ΛCDM, stated at the matter fractions where the printed polynomial\nand the cosmographic coefficient agree.\n-/\n\nnamespace Checked.Cosmography.AvilesM0Root\n\nopen Checked.Cosmography Checked.Cosmography.Aviles\n\n/-- The printed claim for `m₀` of Aviles et al. 2012, Eq. (15), at the matter fractions satisfying the\nstated quadratic condition. -/\ndef AvilesM0RootClaim : Prop :=\n  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →\n    3 * Ω ^ 2 + 2 * Ω - 2 = 0 →\n    cosmoCoeff 6 a t₀ = 1 - 27 / 2 * Ω ^ 2 - 81 * Ω ^ 2 - 81 / 2 * Ω ^ 3\n\n/-- **The printed m₀ of Aviles et al. (2012), Eq. (15), is confirmed for flat ΛCDM:** it equals the\ncosmographic coefficient. -/\ntheorem avilesM0Root_holds : AvilesM0RootClaim := by\n  unfold AvilesM0RootClaim\n  intro Ω a t₀ hL hs hr\n  rw [(flatLCDM_coeffs Ω a t₀ hL hs).2.2.2.2]\n  linear_combination (27 / 4 * Ω) * hr\n\nend Checked.Cosmography.AvilesM0Root\n')

write('Checked/Trust/SecondReadingClaimsRoot.lean', "import Mathlib.Data.Real.Basic\nimport Checked.Cosmography.LCDMCoefficients\nimport Checked.Trust.SecondReadingClaimsA\n\n/-!\n# Second reading of the printed m₀ claim at the special matter fraction (trust track T3, run 2026-11-05T2228Z)\nThe claim below is the program claim's text with the printed m₀ formula replaced by reader A's constant\n`avilesM0` (`SecondReadingClaimsA.lean`).\n-/\n\nnamespace Checked.Trust.SecondReading\n\nopen Checked.Cosmography.Aviles\n\n/-- `Checked.Cosmography.AvilesM0Root.AvilesM0RootClaim` with the printed m₀ formula of Eq. (15) as read by the\nblind second reader. -/\ndef AvilesM0RootClaim : Prop :=\n  ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ → ContDiffAt ℝ 6 a t₀ →\n    3 * Ω ^ 2 + 2 * Ω - 2 = 0 →\n    cosmoCoeff 6 a t₀ = avilesM0 Ω\n\nend Checked.Trust.SecondReading\n")

write('Checked/Trust/TranscriptionsClaimsRoot.lean', 'import Checked.Trust.SecondReadingClaimsRoot\nimport Checked.Cosmography.AvilesM0Root\n\nnamespace Checked.Trust.Transcriptions\n\n/-- `Checked.Cosmography.AvilesM0Root.AvilesM0RootClaim` agrees with the blind second reading (the printed m₀ formula of Eq. (15)). -/\ntheorem agree_AvilesM0RootClaim : Checked.Cosmography.AvilesM0Root.AvilesM0RootClaim = Checked.Trust.SecondReading.AvilesM0RootClaim := by\n  rfl\n\nend Checked.Trust.Transcriptions\n')

write('Checked/Trust/NVAvilesM0Root.lean', 'import Checked.Trust.NonVacuity\nimport Checked.Cosmography.LCDMWitness\nimport Checked.Cosmography.AvilesM0Root\n\nnamespace Checked.Trust.NV\n\ntheorem avilesM0Root_holds : nonvacuity% Checked.Cosmography.AvilesM0Root.avilesM0Root_holds := by\n  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)\n  have h0 : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7\n  have hl : 1 < Real.sqrt 7 := by nlinarith\n  have hu : Real.sqrt 7 < 4 := by nlinarith\n  obtain ⟨a, t₀, hL, hs⟩ := Checked.Cosmography.AvilesWitness.exists_flatLCDM\n    (Ω := (Real.sqrt 7 - 1) / 3) (by linarith) (by linarith)\n  exact ⟨(Real.sqrt 7 - 1) / 3, a, t₀, hL, hs, by linear_combination (1 / 3 : ℝ) * h7, trivial⟩\n\nend Checked.Trust.NV\n')

append('Checked.lean', 'import Checked.Cosmography.AvilesM0Root\nimport Checked.Trust.SecondReadingClaimsRoot\nimport Checked.Trust.TranscriptionsClaimsRoot\nimport Checked.Trust.NVAvilesM0Root\n')
append('scripts/trust/headlines.txt', 'AvilesM0Root.avilesM0Root_holds\n')
append('scripts/trust/def_kinds.txt', 'Checked.Cosmography.AvilesM0Root.AvilesM0RootClaim CLAIM\n')
append('LEDGER.md', "## 2026-11-05 · run 2026-11-05T2228Z · the printed m₀ claim at the special matter fraction, read twice (part 1)\n- **Generated second-reading claim** `SecondReadingClaimsRoot.lean` (`AvilesM0RootClaim`; the program claim's text with reader A's blind constant `avilesM0` substituted; quantifiers, hypotheses and remainder templates are the program's, as in the 2028Z entry; brief `runs/2026-11-05T2028Z/second_reading_claims/BRIEF_COMMON.md`, no new data). Agreement `TranscriptionsClaimsRoot.lean` (`agree_AvilesM0RootClaim`, by `rfl`): agrees. New headline `avilesM0Root_holds`; witness `NVAvilesM0Root.lean`.\n")
