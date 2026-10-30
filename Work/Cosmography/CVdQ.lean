import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Checked.Cosmography.BambaDLy

/-!
# Candidate C1: Cattoën & Visser, Class. Quantum Grav. 24, 5985 (2007), arXiv:0710.1887v1, Eq. (59)

Source (typeset text verified by rendering the PDF, run 2026-10-30T0220Z,
`runs/2026-10-30T0220Z/typeset/C1_cv2007_eq58_60.png`; definitions read this run from the PDF text):
"• The 'deceleration distance': d_Q = d_L/(1 + z)^{3/2}." (Eq. 3) "[...] Ω₀ = 1 + kc²/(H₀²a₀²)"
(Eq. 16), y = z/(1 + z), d_H = c/H₀, and
"d_Q(y) = d_H y{1 − (q₀/2) y + (1/12)[3 − 2q₀ + 12q₀² − 4(j₀ + Ω₀)] y² + O(y³)}."   (59)
(The paper's own Eq. (64) for ln[d_Q/y] has 1/24[3 − 2q₀ + 9q₀² − 4(j₀ + Ω₀)], which corresponds
to 1/24 in (59); repeated with 1/12 in Cattoën–Visser 2008, arXiv:0809.0537v1, Eq. (32).)

Conventions as `Checked.Cosmography.BambaY` (c = 1, flat FLRW, d_L = a₀(1+z)χ, χ = ∫_t^{t₀} dt/a).
We test the flat instance (k = 0, Ω₀ = 1) under the weakest reading (remainder o(y³)).

FROZEN (annex 40.1) in run 2026-10-30T0828Z before proof work.
-/

namespace Work.Cosmography.CVdQ

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
  Checked.Cosmography.BambaY
open scoped ContDiff

/-- Deceleration distance in a flat model: `d_Q = d_L/(1+z)^{3/2}` (real power). -/
noncomputable def dQFlat (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDistFlat a t₀ t / (1 + redshift a t₀ t) ^ ((3 : ℝ) / 2)

/-- The y² coefficient as printed in Eq. (59). -/
noncomputable def printedQ2 (q j Ω : ℝ) : ℝ := (1 / 12) * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))

/-- The same bracket over 24. -/
noncomputable def correctQ2 (q j Ω : ℝ) : ℝ := (1 / 24) * (3 - 2 * q + 12 * q ^ 2 - 4 * (j + Ω))

/-- `H₀ d_Q(y)/c = y [1 − (q₀/2) y + Q² y²]`. -/
noncomputable def seriesQ (d2 q y : ℝ) : ℝ := y * (1 - q / 2 * y + d2 * y ^ 2)

/-- Remainder `H₀ d_Q − y[1 − (q₀/2)y + Q²y²]`, flat model (`Ω₀ = 1`). -/
noncomputable def remainderQ (D2 : ℝ → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * dQFlat a t₀ t -
    seriesQ (D2 (decel a t₀) (cosmoCoeff 3 a t₀) 1) (decel a t₀) (yred a t₀ t)

/-- The printed claim, flat instance, weakest reading, strongest hypotheses. -/
def CVdQClaim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remainderQ printedQ2 a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3)

/-- Same, past emission only. -/
def CVdQClaimPast : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), ContDiff ℝ ω a → (∀ t, 0 < a t) → 0 < hubble a t₀ →
    (fun t => remainderQ printedQ2 a t₀ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 3)

/-- **Deceleration distance to third order in `y`** (flat FLRW, coefficient over 24). -/
theorem dQ_y_third_order (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) :
    (fun t => remainderQ correctQ2 a t₀ t) =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3) := by
  sorry

/-- The printed coefficient fails (past emission) in every flat `C³` model with
`−1 − 2q₀ + 12q₀² − 4j₀ ≠ 0`. -/
theorem printedQ2_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 3 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hD : -1 - 2 * decel a t₀ + 12 * decel a t₀ ^ 2 - 4 * cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => remainderQ printedQ2 a t₀ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 3) := by
  sorry

/-- The printed claim is false (flat de Sitter). -/
theorem cvdQClaim_false : ¬ CVdQClaim := by
  sorry

/-- The past-only reading is false (flat de Sitter). -/
theorem cvdQClaimPast_false : ¬ CVdQClaimPast := by
  sorry

end Work.Cosmography.CVdQ
