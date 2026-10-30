import Checked.Fidelity.Pins

/-!
# Flat luminosity distance and comoving distance, pinned through `LumDistSpec2` (trust track T1)

`BambaY.lumDistFlat` (flat `d_L`, 9 headlines in `TRUST_MAP.md`) is `lumDist` at `K = 0`, and
`BambaY.comoving` (`χ = ∫ dt/a`, 9 headlines) is recovered from the flat luminosity distance as
`χ = d_L / (a₀ (1+z))`. Both are therefore determined by any function meeting the pinned
specification `LumDistSpec2` (`lumDistSpec2_pins`), on the same physical domain
(`t ≤ t₀`, `a > 0` and continuous on `[t, t₀]`).
-/

namespace Checked.Fidelity

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.Transverse

lemma lumDistFlat_eq_lumDist (a : ℝ → ℝ) (t₀ t : ℝ) : lumDistFlat a t₀ t = lumDist 0 a t₀ t := by
  simp [lumDistFlat, lumDist, transverse]

/-- **Pinning:** any `D` meeting `LumDistSpec2` gives the program's flat luminosity distance at
`K = 0`. -/
theorem lumDistFlat_pins (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec2 D) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hcont : ContinuousOn a (Set.Icc t t₀)) : D 0 a t₀ t = lumDistFlat a t₀ t := by
  rw [lumDistSpec2_pins D h 0 a t₀ t htt hpos hcont, lumDistFlat_eq_lumDist]

/-- **Pinning:** the comoving distance is the flat luminosity distance of any `D` meeting
`LumDistSpec2`, divided by `a₀ (1 + z)`. -/
theorem comoving_pins (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec2 D) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hcont : ContinuousOn a (Set.Icc t t₀)) :
    comoving a t₀ t = D 0 a t₀ t / (a t₀ * (1 + redshift a t₀ t)) := by
  have h0 : 0 < a t₀ := hpos t₀ ⟨htt, le_rfl⟩
  have h1 : 0 < a t := hpos t ⟨le_rfl, htt⟩
  have hz : 1 + redshift a t₀ t = a t₀ / a t := by simp [redshift]
  rw [lumDistFlat_pins D h a t₀ t htt hpos hcont, lumDistFlat, hz]
  have : a t₀ * (a t₀ / a t) ≠ 0 := by positivity
  field_simp

end Checked.Fidelity
