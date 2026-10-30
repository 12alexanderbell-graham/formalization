import Checked.Cosmography.FRCosmo

/-!
# Blind restatement (annex 40.2) of Bamba–Capozziello–Nojiri–Odintsov, Astrophys. Space Sci.
342, 155 (2012), arXiv:1205.3421v3, Sec. XI.B, Eqs. (11.39), (11.41)–(11.45) (pp. 120–121)

Written from the typeset source only (crops of pp. 116, 120, 121 at 200 dpi).

Source:
* (11.21) `F(R₀)/(6H₀²) = −(P₀Ω_M + Q₀)/R`, (11.23) `F″(R₀)/(6H₀²)⁻¹ = −(P₂Ω_M + Q₂)/R`,
  (11.24) `F‴(R₀)/(6H₀²)⁻² = −(P₃Ω_M + Q₃)/((j₀ − q₀ − 2)R)`, with `P₀ … Q₃` (11.25)–(11.30)
  and `R` (11.31); the transcriptions `Checked.Cosmography.FRCosmo.P0 … Q3, printedR` were
  re-checked against the typeset page and are verbatim.
* (11.39) ΛCDM: `q₀ = 1/2 − (3/2)(1 − Ω)`, `j₀ = 1`, `s₀ = 1 − (9/2)Ω`,
  `l₀ = 1 + 3Ω + (27/2)Ω²`.
* (11.41) `x₀ = x₀^Λ (1 + ε_x)` for `x ∈ {q, j, s, l}`; text: all four `ε_x` equal one `ε ≪ 1`.
* "Inserting the above expressions … into the exact (not reported) formulae for F(R₀), F″(R₀) and
  F‴(R₀), taking those ratios and then expanding to first order in ε, we finally find"
  (11.42) `η₂₀ ≡ F″(R₀)H₀⁴/F(R₀) = (64 − 6Ω(9Ω + 8)) / ([3(9Ω + 74)Ω − 556]Ω² + 16) × ε/27`,
  (11.43) `η₃₀ ≡ F‴(R₀)H₀⁶/F(R₀)
           = 6[((81Ω − 110)Ω + 40)Ω + 16] / ([3(9Ω + 74)Ω − 556]Ω² + 16) × ε/(243Ω²)`.
* (11.44) `η₂₀ ≃ 0.15 ε` (Ω = 0.041), `−0.12 ε` (Ω = 0.250);
  (11.45) `η₃₀ ≃ 4 ε` (Ω = 0.041), `−0.18 ε` (Ω = 0.250).

Formalization choices:
* "The exact formulae" are (11.21), (11.23), (11.24) with (11.25)–(11.31) (the only F(R)
  formulae in the paper; the common factor `R` cancels in both ratios, so the known misprint in
  (11.31) is irrelevant here, provided `R ≠ 0`). `H₀` is a free nonzero parameter (it cancels).
* "Expanded to first order in ε, η = c·ε" is formalized as `η(ε) − c·ε = o(ε)` as `ε → 0`
  (`Asymptotics.IsLittleO` at `𝓝 0`). This pins both the zeroth-order term (`η(0) = 0`) and the
  first-order coefficient `c` (for these rational functions, equivalently `η(ε) − cε = O(ε²)`);
  no `≈` is turned into `=`.
* Junk values (`x / 0 = 0`): every denominator that could vanish is a hypothesis — the ΛCDM
  values of `R` (11.31) and of `P₀Ω + Q₀`, and the printed denominator of (11.42)–(11.43);
  `0 < Ω < 1` (so `Ω ≠ 0` and `j₀ − q₀ − 2 = −3Ω/2 ≠ 0` at `ε = 0`). These are nonzero at
  `ε = 0`, hence on a neighbourhood of `ε = 0`, so the little-o statement never sees a junk value.
  (The printed denominator `[3(9Ω+74)Ω−556]Ω²+16 = (Ω−2)(27Ω³+276Ω²−4Ω−8)` vanishes at
  `Ω ≈ 0.176`; `printedR` vanishes in ΛCDM at `Ω ≈ 0.538`.)
* Numerical claims (11.44)–(11.45): "`η ≃ c₀ ε`" means: the true first-order coefficient `c`
  (in the above sense) lies within half a unit of the last printed digit of `c₀`
  (`±0.005` for 0.15, −0.12, −0.18; `±0.5` for 4). Separately, `…FromPrinted` states only the
  internal consistency step: the printed closed forms (11.42)–(11.43) evaluated at the fiducial Ω
  round to the printed numbers.
-/

namespace Work.Cosmography.FREtaBlind

open Filter Topology Asymptotics
open Checked.Cosmography.FRCosmo (P0 Q0 P2 Q2 P3 Q3 printedR)

/-! ## ΛCDM cosmographic values (11.39) -/

/-- `q₀^Λ = 1/2 − (3/2)(1 − Ω)` (11.39). -/
noncomputable def qL (Ω : ℝ) : ℝ := 1 / 2 - 3 / 2 * (1 - Ω)
/-- `j₀^Λ = 1` (11.39). -/
def jL (_Ω : ℝ) : ℝ := 1
/-- `s₀^Λ = 1 − (9/2)Ω` (11.39). -/
noncomputable def sL (Ω : ℝ) : ℝ := 1 - 9 / 2 * Ω
/-- `l₀^Λ = 1 + 3Ω + (27/2)Ω²` (11.39). -/
noncomputable def lL (Ω : ℝ) : ℝ := 1 + 3 * Ω + 27 / 2 * Ω ^ 2

/-! ## The paper's F(R) formulas (11.21), (11.23), (11.24) -/

/-- `F(R₀) = −6H₀² (P₀Ω + Q₀)/R` (11.21). -/
noncomputable def F0 (H Ω q j s l : ℝ) : ℝ :=
  -(6 * H ^ 2) * (P0 q j s l * Ω + Q0 q j s l) / printedR q j s l

/-- `F″(R₀) = −(P₂Ω + Q₂)/R · (6H₀²)⁻¹` (11.23). -/
noncomputable def F2 (H Ω q j s l : ℝ) : ℝ :=
  -(P2 q j s * Ω + Q2 q j s) / printedR q j s l / (6 * H ^ 2)

/-- `F‴(R₀) = −(P₃Ω + Q₃)/((j₀ − q₀ − 2)R) · (6H₀²)⁻²` (11.24). -/
noncomputable def F3 (H Ω q j s l : ℝ) : ℝ :=
  -(P3 q j s l * Ω + Q3 q j s l) / ((j - q - 2) * printedR q j s l) / (6 * H ^ 2) ^ 2

/-! ## The ratios with (11.41), common ε -/

/-- `η₂₀(ε) = F″(R₀)H₀⁴/F(R₀)` at `(q₀, j₀, s₀, l₀) = (11.39) × (1 + ε)` (11.41)–(11.42). -/
noncomputable def eta20 (H Ω ε : ℝ) : ℝ :=
  F2 H Ω (qL Ω * (1 + ε)) (jL Ω * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε)) * H ^ 4
    / F0 H Ω (qL Ω * (1 + ε)) (jL Ω * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε))

/-- `η₃₀(ε) = F‴(R₀)H₀⁶/F(R₀)` at `(q₀, j₀, s₀, l₀) = (11.39) × (1 + ε)` (11.41), (11.43). -/
noncomputable def eta30 (H Ω ε : ℝ) : ℝ :=
  F3 H Ω (qL Ω * (1 + ε)) (jL Ω * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε)) * H ^ 6
    / F0 H Ω (qL Ω * (1 + ε)) (jL Ω * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε))

/-! ## Printed first-order coefficients (11.42)–(11.43) -/

/-- Common printed denominator `[3(9Ω + 74)Ω − 556]Ω² + 16`. -/
def printedDen (Ω : ℝ) : ℝ := (3 * (9 * Ω + 74) * Ω - 556) * Ω ^ 2 + 16

/-- Printed coefficient of `ε` in (11.42). -/
noncomputable def printedC20 (Ω : ℝ) : ℝ :=
  (64 - 6 * Ω * (9 * Ω + 8)) / printedDen Ω * (1 / 27)

/-- Printed coefficient of `ε` in (11.43). -/
noncomputable def printedC30 (Ω : ℝ) : ℝ :=
  6 * (((81 * Ω - 110) * Ω + 40) * Ω + 16) / printedDen Ω * (1 / (243 * Ω ^ 2))

/-- Non-degeneracy hypotheses at `ε = 0` (see module doc). -/
def NonDegenerate (Ω : ℝ) : Prop :=
  0 < Ω ∧ Ω < 1 ∧
    printedR (qL Ω) (jL Ω) (sL Ω) (lL Ω) ≠ 0 ∧
    P0 (qL Ω) (jL Ω) (sL Ω) (lL Ω) * Ω + Q0 (qL Ω) (jL Ω) (sL Ω) (lL Ω) ≠ 0 ∧
    printedDen Ω ≠ 0

/-- `η = c ε` to first order in `ε`: `η(ε) − cε = o(ε)` as `ε → 0`. -/
def FirstOrder (η : ℝ → ℝ) (c : ℝ) : Prop :=
  (fun ε => η ε - c * ε) =o[𝓝 0] (fun ε => ε)

/-! ## (a) Claims (11.42), (11.43) -/

/-- (11.41)+(11.42): for every admissible `Ω` and `H₀ ≠ 0`, `η₂₀ = printedC20(Ω)·ε` to first
order in `ε`. -/
def Eta20Claim : Prop :=
  ∀ H Ω : ℝ, H ≠ 0 → NonDegenerate Ω → FirstOrder (eta20 H Ω) (printedC20 Ω)

/-- (11.41)+(11.43): for every admissible `Ω` and `H₀ ≠ 0`, `η₃₀ = printedC30(Ω)·ε` to first
order in `ε`. -/
def Eta30Claim : Prop :=
  ∀ H Ω : ℝ, H ≠ 0 → NonDegenerate Ω → FirstOrder (eta30 H Ω) (printedC30 Ω)

/-! ## (b) Numerical claims (11.44), (11.45) -/

/-- (11.44), first row: `η₂₀ ≃ 0.15 ε` at `Ω = 0.041`. -/
def Eta20Num041 : Prop :=
  ∃ c : ℝ, |c - 15 / 100| ≤ 5 / 1000 ∧ ∀ H : ℝ, H ≠ 0 → FirstOrder (eta20 H (41 / 1000)) c

/-- (11.44), second row: `η₂₀ ≃ −0.12 ε` at `Ω = 0.250`. -/
def Eta20Num250 : Prop :=
  ∃ c : ℝ, |c + 12 / 100| ≤ 5 / 1000 ∧ ∀ H : ℝ, H ≠ 0 → FirstOrder (eta20 H (1 / 4)) c

/-- (11.45), first row: `η₃₀ ≃ 4 ε` at `Ω = 0.041`. -/
def Eta30Num041 : Prop :=
  ∃ c : ℝ, |c - 4| ≤ 1 / 2 ∧ ∀ H : ℝ, H ≠ 0 → FirstOrder (eta30 H (41 / 1000)) c

/-- (11.45), second row: `η₃₀ ≃ −0.18 ε` at `Ω = 0.250`. -/
def Eta30Num250 : Prop :=
  ∃ c : ℝ, |c + 18 / 100| ≤ 5 / 1000 ∧ ∀ H : ℝ, H ≠ 0 → FirstOrder (eta30 H (1 / 4)) c

/-- Consistency step (11.42) → (11.44): the printed closed form rounds to the printed numbers. -/
def Eta20NumFromPrinted : Prop :=
  |printedC20 (41 / 1000) - 15 / 100| ≤ 5 / 1000 ∧ |printedC20 (1 / 4) + 12 / 100| ≤ 5 / 1000

/-- Consistency step (11.43) → (11.45): the printed closed form rounds to the printed numbers. -/
def Eta30NumFromPrinted : Prop :=
  |printedC30 (41 / 1000) - 4| ≤ 1 / 2 ∧ |printedC30 (1 / 4) + 18 / 100| ≤ 5 / 1000

/-! ## Corrected coefficients (sympy, from (11.21)–(11.31) and independently re-derived from the
field equations; not claims of the paper) -/

/-- Correct first-order coefficient of `η₂₀`:
`(64 − 6Ω(9Ω + 8)) / (27 Ω (Ω − 2)(27Ω² + 60Ω + 112))`. -/
noncomputable def trueC20 (Ω : ℝ) : ℝ :=
  (64 - 6 * Ω * (9 * Ω + 8)) / (27 * Ω * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112))

/-- Correct first-order coefficient of `η₃₀`:
`−2(81Ω² − 60Ω − 16) / (243 Ω² (Ω − 2)(27Ω² + 60Ω + 112))`. -/
noncomputable def trueC30 (Ω : ℝ) : ℝ :=
  -2 * (81 * Ω ^ 2 - 60 * Ω - 16) / (243 * Ω ^ 2 * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112))

/-- Corrected (a): `η₂₀ = trueC20(Ω)·ε` to first order. -/
def Eta20Corrected : Prop :=
  ∀ H Ω : ℝ, H ≠ 0 → 0 < Ω → Ω < 1 → printedR (qL Ω) (jL Ω) (sL Ω) (lL Ω) ≠ 0 →
    FirstOrder (eta20 H Ω) (trueC20 Ω)

/-- Corrected (a): `η₃₀ = trueC30(Ω)·ε` to first order. -/
def Eta30Corrected : Prop :=
  ∀ H Ω : ℝ, H ≠ 0 → 0 < Ω → Ω < 1 → printedR (qL Ω) (jL Ω) (sL Ω) (lL Ω) ≠ 0 →
    FirstOrder (eta30 H Ω) (trueC30 Ω)

/-! ## Verdicts (sympy; proofs not attempted) -/

theorem eta20Claim_false : ¬ Eta20Claim := by sorry
theorem eta30Claim_false : ¬ Eta30Claim := by sorry
theorem eta20Num041_false : ¬ Eta20Num041 := by sorry
theorem eta20Num250_false : ¬ Eta20Num250 := by sorry
theorem eta30Num041_false : ¬ Eta30Num041 := by sorry
theorem eta30Num250_false : ¬ Eta30Num250 := by sorry
theorem eta20NumFromPrinted_true : Eta20NumFromPrinted := by sorry
theorem eta30NumFromPrinted_false : ¬ Eta30NumFromPrinted := by sorry
theorem eta20Corrected_true : Eta20Corrected := by sorry
theorem eta30Corrected_true : Eta30Corrected := by sorry

end Work.Cosmography.FREtaBlind
