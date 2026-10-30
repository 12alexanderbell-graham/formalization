import Checked.Cosmography.LCDMWitness

/-!
# Candidates C11, C13: Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155
(2012), arXiv:1205.3421v3, Sec. XI ("Testing F(R) gravity by cosmography"), Eqs. (11.1)–(11.31);
upstream Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583, Eqs. (11)–(33)

Source (typeset; crops `runs/2026-10-30T1428Z/typeset/`, `runs/2026-10-30T1232Z/screen_secXI/`;
review v1–v3 identical by pdftotext of (11.31)):
* (11.1)–(11.2): `H² = (1/3)[ρ_M/F′(R) + ρ_curv]`,
  `ρ_curv = (1/F′(R))[(F(R) − R F′(R))/2 − 3H Ṙ F″(R)]`, `κ² = 1`, `ρ_M = 3H₀²Ω_M a⁻³`
  (`a(t₀) = 1`; here `ρ_M = 3H₀²Ω (a₀/a)³`).
* (11.5): `Ḣ = −(1/(2F′(R)))[3H₀²Ω_M a⁻³ + R̈ F″(R) + Ṙ(Ṙ F‴(R) − H F″(R))]`.
* (11.6): `R = −6(Ḣ + 2H²)`.
* (11.10)–(11.13): `R₀ = −6H₀²(1 − q₀)`, `Ṙ₀ = −6H₀³(j₀ − q₀ − 2)`,
  `R̈₀ = −6H₀⁴(s₀ + q₀² + 8q₀ + 6)`,
  `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]`.
* (11.17): `F′(R₀) = 1`; (11.19): `F` replaced by its cubic Taylor polynomial at `R₀`, so
  `F⁽⁴⁾(R₀) = 0`; (11.20) is the time derivative of (11.5) at `t₀`.
* (11.21): `F(R₀)/(6H₀²) = −(P₀Ω_M + Q₀)/R`; (11.23): `F″(R₀)/(6H₀²)⁻¹ = −(P₂Ω_M + Q₂)/R`;
  (11.24): `F‴(R₀)/(6H₀²)⁻² = −(P₃Ω_M + Q₃)/((j₀ − q₀ − 2)R)`; `P₀ … Q₃` (11.25)–(11.30) and
  `R` (11.31) are transcribed below verbatim.
* (11.39)–(11.40): for ΛCDM the formulas are said to give `F(R₀) = R₀ + 2Λ`, `F″ = F‴ = 0`.

Model (explicit hypotheses, `IsFRCosmo`): flat FLRW scale factor `a`, `C⁵` at `t₀`, `a(t₀) > 0`,
`H₀ > 0`; `F` is `C⁴` on ℝ; the expansion-rate equation (11.1)–(11.2) holds at `t₀` (that is
(11.14)); the master equation (11.5) holds for all `t` near `t₀` (so (11.15) and its time
derivative (11.20) hold at `t₀`); `F′(R₀) = 1` (11.17); `F⁽⁴⁾(R₀) = 0` (11.19). The two field
equations are stated multiplied by `3F′(R)` and `−2F′(R)` (equivalent wherever `F′(R) ≠ 0`, which
holds near `t₀` since `F′(R₀) = 1`). Cosmographic parameters as in `Checked.Cosmography`:
`q₀ = decel a t₀`, `j₀, s₀, l₀ = cosmoCoeff 3, 4, 5`.

Claims frozen: the printed `d³R₀/dt³` (11.13) (candidate C11) and the printed `F(R₀)` relation
(11.21) with the printed `R` (11.31) (candidate C13), the latter both as printed (division, with
`R ≠ 0` assumed so no junk value enters) and multiplied out. The F″, F‴ relations (11.23)–(11.24)
are true in ΛCDM with either `R` (both sides vanish), so they are not refuted here.

FROZEN (annex 40.1) in run 2026-10-30T1428Z before proof work.
-/

namespace Work.Cosmography.FRCosmo

open Filter Topology Checked.Cosmography Checked.Cosmography.Aviles

/-- Ricci scalar of flat FLRW in the review's sign convention (11.6): `R = −6(Ḣ + 2H²)`. -/
noncomputable def curv (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)

/-- Dust density `ρ_M = 3H₀²Ω (a₀/a)³` (`κ² = 1`, text after (11.2)). -/
noncomputable def rhoM (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  3 * hubble a t₀ ^ 2 * Ω * (a t₀ / a t) ^ 3

/-- Expansion-rate equation (11.1)–(11.2) at time `t`, multiplied by `3F′(R)`. -/
def FriedmannEq (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) : Prop :=
  3 * deriv F (curv a t) * hubble a t ^ 2 =
    rhoM Ω a t₀ t + (F (curv a t) - curv a t * deriv F (curv a t)) / 2
      - 3 * hubble a t * deriv (curv a) t * deriv^[2] F (curv a t)

/-- Master equation (11.5) at time `t`, multiplied by `−2F′(R)`. -/
def MasterEq (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) : Prop :=
  -2 * deriv F (curv a t) * deriv (hubble a) t =
    rhoM Ω a t₀ t + deriv^[2] (curv a) t * deriv^[2] F (curv a t)
      + deriv (curv a) t * (deriv (curv a) t * deriv^[3] F (curv a t)
        - hubble a t * deriv^[2] F (curv a t))

/-- The setting of Eqs. (11.14)–(11.24): metric `F(R)` gravity with dust, flat FLRW, Newton's
constant today (11.17), cubic truncation of `F` at `R₀` (11.19). -/
structure IsFRCosmo (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ) : Prop where
  pos : 0 < a t₀
  expanding : 0 < hubble a t₀
  smooth_a : ContDiffAt ℝ 5 a t₀
  smooth_F : ContDiff ℝ 4 F
  friedmann : FriedmannEq Ω a F t₀ t₀
  master : ∀ᶠ t in 𝓝 t₀, MasterEq Ω a F t₀ t
  newton : deriv F (curv a t₀) = 1
  cubic : deriv^[4] F (curv a t₀) = 0

/-- `P₀` (11.25), verbatim. -/
def P0 (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s
    - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j
    - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)

/-- `Q₀` (11.26), verbatim. -/
def Q0 (q j s l : ℝ) : ℝ :=
  (q ^ 2 - j * q + 2 * q) * l
    + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s
    + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j
    + (3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64)

/-- `P₂` (11.27), verbatim. -/
def P2 (q j s : ℝ) : ℝ := 9 * s + 6 * j + 9 * q ^ 2 + 66 * q + 42

/-- `Q₂` (11.28), verbatim. -/
def Q2 (q j s : ℝ) : ℝ :=
  -(6 * (q + 1) * s + (2 * j - 2 * (1 - q)) * j + 6 * q ^ 3 + 50 * q ^ 2 + 74 * q + 32)

/-- `P₃` (11.29), verbatim. -/
def P3 (q j s l : ℝ) : ℝ := 3 * l + 3 * s - 9 * (q + 4) * j - (45 * q ^ 2 + 78 * q + 12)

/-- `Q₃` (11.30), verbatim. -/
def Q3 (q j s l : ℝ) : ℝ :=
  -(2 * (1 + q) * l + 2 * (j + q) * s - (2 * j + 4 * q ^ 2 + 12 * q + 6) * j
    - (30 * q ^ 3 + 84 * q ^ 2 + 78 * q + 24))

/-- `R` (11.31) as printed in the review, verbatim. -/
def printedR (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    + ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q + 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 246 * q + 104)

/-- Proposed correction of (11.31) (derived in `runs/2026-10-30T1428Z/scripts/derive_fr.py`):
the bracket enters with a minus sign, `+18` is `−18`, and `180 q₀²` is missing. -/
def correctR (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    - ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q - 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 180 * q ^ 2 + 246 * q + 104)

/-- Printed (11.13): `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]` for every
flat FLRW scale factor (`C⁵` at `t₀`, `a(t₀) > 0`, `H₀ > 0`). -/
def PrintedR3Claim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → 0 < hubble a t₀ → ContDiffAt ℝ 5 a t₀ →
    deriv^[3] (curv a) t₀ = -6 * hubble a t₀ ^ 5 *
      (cosmoCoeff 5 a t₀ - cosmoCoeff 4 a t₀ + 2 * (decel a t₀ + 4) * cosmoCoeff 3 a t₀
        - 6 * (3 * decel a t₀ + 8) * decel a t₀ - 24)

/-- Printed (11.21) with printed (11.31), as printed (division; `R ≠ 0` assumed). -/
def PrintedF0Claim : Prop :=
  ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
    printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 →
    F (curv a t₀) / (6 * hubble a t₀ ^ 2) =
      -(P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
          + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
        / printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)

/-- Printed (11.21) with printed (11.31), multiplied out (no division). -/
def PrintedF0ClaimMul : Prop :=
  ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
    printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
        * F (curv a t₀) =
      -6 * hubble a t₀ ^ 2 *
        (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
          + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))

/-- **Correct (11.10)–(11.13).** -/
theorem curv_derivs (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hH : 0 < hubble a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    curv a t₀ = -6 * hubble a t₀ ^ 2 * (1 - decel a t₀) ∧
    deriv (curv a) t₀ = -6 * hubble a t₀ ^ 3 * (cosmoCoeff 3 a t₀ - decel a t₀ - 2) ∧
    deriv^[2] (curv a) t₀ =
      -6 * hubble a t₀ ^ 4 * (cosmoCoeff 4 a t₀ + decel a t₀ ^ 2 + 8 * decel a t₀ + 6) ∧
    deriv^[3] (curv a) t₀ = -6 * hubble a t₀ ^ 5 *
      (cosmoCoeff 5 a t₀ - cosmoCoeff 4 a t₀ - 2 * (decel a t₀ + 4) * cosmoCoeff 3 a t₀
        - 6 * (3 * decel a t₀ + 8) * decel a t₀ - 24) := by
  sorry

/-- **Correct (11.21), (11.23), (11.24)** (multiplied out; no nondegeneracy needed). -/
theorem fR_values (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ) (hM : IsFRCosmo Ω a F t₀) :
    correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
        * F (curv a t₀) =
      -6 * hubble a t₀ ^ 2 *
        (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
          + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) ∧
    correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
        * (6 * hubble a t₀ ^ 2) * deriv^[2] F (curv a t₀) =
      -(P2 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) * Ω
          + Q2 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)) ∧
    (cosmoCoeff 3 a t₀ - decel a t₀ - 2)
        * correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
        * (6 * hubble a t₀ ^ 2) ^ 2 * deriv^[3] F (curv a t₀) =
      -(P3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
          + Q3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) := by
  sorry

/-- (11.40), the paper's own check: for every `Ω ∈ (0,1)` there is a flat ΛCDM scale factor
which, with `F(R) = R + 2Λ`, `Λ = 3H₀²(1 − Ω)`, satisfies every hypothesis of `IsFRCosmo`. -/
theorem exists_LCDM_model {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ ∧
      IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀ := by
  sorry

theorem printedR3Claim_false : ¬ PrintedR3Claim := by
  sorry

/-- The multiplied-out printed relation fails in ΛCDM at every `Ω ∈ (0,1)`. -/
theorem printedF0Mul_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
          * F (curv a t₀) =
        -6 * hubble a t₀ ^ 2 *
          (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) := by
  sorry

theorem printedF0ClaimMul_false : ¬ PrintedF0ClaimMul := by
  sorry

/-- The printed relation (division form) fails in ΛCDM at the review's concordance value
`Ω = 1/4` (Sec. XI uses `Ω_M = 0.25` and `0.041`; both are covered by the `Ω ∈ (0,1)` statement
below whenever the printed `R` is nonzero there). -/
theorem printedF0Claim_false : ¬ PrintedF0Claim := by
  sorry

/-- Division form at every `Ω ∈ (0,1)` where the printed `R` is nonzero in ΛCDM
(`printedR` at ΛCDM is `−(243Ω⁴ + 540Ω³ − 6264Ω² + 9360Ω − 3328)/16`). -/
theorem printedF0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1)
    (hR : 243 * Ω ^ 4 + 540 * Ω ^ 3 - 6264 * Ω ^ 2 + 9360 * Ω - 3328 ≠ 0) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 →
      F (curv a t₀) / (6 * hubble a t₀ ^ 2) =
        -(P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
          / printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) := by
  sorry

end Work.Cosmography.FRCosmo
