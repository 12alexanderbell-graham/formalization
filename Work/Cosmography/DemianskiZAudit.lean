import Work.Cosmography.DemianskiZ
import Work.Cosmography.DemianskiZBlind

/-!
# C15/C16 audit: blind restatement closed in Lean (run 2026-10-30T1628Z)

The blind restater (`Work.Cosmography.DemianskiZBlind`, written without seeing `DemianskiZ`)
transcribed all printed coefficients itself, used `d_L` with the prefactor `z/H₀`, hypotheses
`C⁶` at `t₀` (local), and stated flat and curved readings, past emission only. Its four readings
are refuted in its own file (no `sorry`). Here: its printed `D¹…D⁴` (flat) equal ours, so both
formalizations test the same printed formulas. The blind's curved readings fail already at `z³`
(missing curvature terms in `D²_L`, `D³_L`, `D²_A`); ours are flat only (the charitable reading).
-/

namespace Work.Cosmography.DemianskiZAudit

open Work.Cosmography Checked.Cosmography.BambaZ

theorem same_transcription (q j s l : ℝ) :
    DemianskiZBlind.D1L q = DL1z q ∧ DemianskiZBlind.D2L q j = DL2z q j 0 ∧
    DemianskiZBlind.D3L q j s = DL3z q j s 0 ∧ DemianskiZBlind.D4L q j s l = DemianskiZ.demDL4 q j s l ∧
    DemianskiZBlind.D1A q = DA1z q ∧ DemianskiZBlind.D2A q j = DA2z q j 0 ∧
    DemianskiZBlind.D3A q j s 0 = DA3z q j s 0 ∧ DemianskiZBlind.D4A q j s l = DemianskiZ.demDA4 q j s l := by
  unfold DemianskiZBlind.D1L DemianskiZBlind.D2L DemianskiZBlind.D3L DemianskiZBlind.D4L
    DemianskiZBlind.D1A DemianskiZBlind.D2A DemianskiZBlind.D3A DemianskiZBlind.D4A
    DL1z DL2z DL3z DA1z DA2z DA3z DemianskiZ.demDL4 DemianskiZ.demDA4
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

end Work.Cosmography.DemianskiZAudit
