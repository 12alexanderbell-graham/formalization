import Checked.Cosmography.FRCosmo

/-!
# Candidate C14: Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155 (2012),
arXiv:1205.3421v3, Sec. XI, Eqs. (11.39), (11.41)–(11.45) (p. 120–121); upstream Capozziello,
Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583, Eqs. (43)–(45) (identical)

Source (typeset crops `runs/2026-10-30T1232Z/screen_secXI/cand5_eq11.42-45_eta.png`,
`runs/2026-10-30T1428Z/referee/review_v3_p121_eq11.42-43.png`; text of (11.41) from pdftotext of
v3 p. 120–121):
* (11.39): ΛCDM values `q₀ = 3Ω/2 − 1`, `j₀ = 1`, `s₀ = 1 − 9Ω/2`, `l₀ = 1 + 3Ω + 27Ω²/2`.
* (11.41): `q₀ = q₀^Λ(1 + ε_q)`, `j₀ = j₀^Λ(1 + ε_j)`, `s₀ = s₀^Λ(1 + ε_s)`, `l₀ = l₀^Λ(1 + ε_l)`;
  "an idealized situation where the four quantities above all share the same value ε ≪ 1".
* "Inserting the above expressions … into the exact (not reported) formulae for F(R₀), F″(R₀) and
  F‴(R₀), taking those ratios and then expanding to first order in ε, we finally find"
  (11.42) `η₂₀ ≡ F″(R₀)H₀⁴/F(R₀) = (64 − 6Ω(9Ω + 8)) / ([3(9Ω + 74)Ω − 556]Ω² + 16) × ε/27`,
  (11.43) `η₃₀ ≡ F‴(R₀)H₀⁶/F(R₀) = (6[(81Ω − 110)Ω + 40]Ω + 16) / ([3(9Ω + 74)Ω − 556]Ω² + 16)
  × ε/(243Ω²)`,
  (11.44) `η₂₀ ≃ 0.15ε` (Ω = 0.041), `−0.12ε` (Ω = 0.250);
  (11.45) `η₃₀ ≃ 4ε` (Ω = 0.041), `−0.18ε` (Ω = 0.250).

Formalization choices:
* The ratios are computed from the review's own `P₀ … Q₃` (11.25)–(11.30) (verbatim in
  `Checked.Cosmography.FRCosmo`); `R` (11.31) cancels in both ratios. `eta_ratios` proves that these
  expressions ARE `F″(R₀)H₀⁴/F(R₀)` and `F‴(R₀)H₀⁶/F(R₀)` in every model of the metric `F(R)` FLRW
  equations (`IsFRCosmo`) with `F(R₀) ≠ 0`, `R ≠ 0` (true near ΛCDM) and `j₀ − q₀ − 2 ≠ 0`, so the
  result does not depend on which ("not reported") formulae the paper used.
* "Expanding to first order in ε, η = c·ε" is formalized as: `η(0) = 0` and `η` has derivative `c`
  at `ε = 0` (the first-order Taylor coefficient). No `≈` is formalized as `=`.
* Printed claim: for `0 < Ω < 1` with the printed denominator nonzero (it vanishes at Ω ≈ 0.176,
  where (11.42) is undefined), the derivative at 0 is the printed coefficient.
* Not claimed: that an `F(R)` model with parameters on the (11.41) family exists for small `ε ≠ 0`
  (the paper does not claim it either); at `ε = 0` it exists (`FRCosmo.lcdm_witness`).

FROZEN (annex 40.1) in run 2026-10-30T1628Z before proof work (commit a164886).

PROMOTED from `Work/Cosmography/FREta.lean` (statements byte-identical); audit
`runs/2026-10-30T1628Z/audit.md`; blind closure `Work/Cosmography/FREtaAudit.lean`.
Referee notes (`runs/2026-10-30T1628Z/referee/referee_report.md`):
* Sign convention: the review's (11.6) `R = −6(Ḣ + 2H²)`. Under `R ↦ −R`, `F ↦ −F(−R)` (the
  common `R = +6(Ḣ + 2H²)` convention) `η₂₀` is unchanged and `η₃₀` flips sign.
* In `eta_ratios` the hypothesis `F(R₀) ≠ 0` is redundant (given `R ≠ 0`, `F(R₀) = 0` forces
  `P₀Ω + Q₀ = 0` and both sides are the junk value 0); `R ≠ 0` and `j₀ − q₀ − 2 ≠ 0` are needed.
  All three hold at ΛCDM: `R = −9Ω²(27Ω² + 60Ω + 112)/16`, `j₀ − q₀ − 2 = −3Ω/2`.
* Provenance: upstream 0802.1583 (v1 p. 7, v2 p. 8) Eqs. (43)–(44) and the unnumbered display after
  (44) carry the same formulas and numbers; Capozziello & Salzano 2009 (arXiv:0902.0088)
  Eqs. (107)–(108) reprint them. No erratum found.
* At Ω = 0.041 the family meets `j₀ − q₀ − 2 = 0` at `ε ≈ 0.032` (a pole of `η₃₀`), so the paper's
  check of the linear relations "up to ε ≃ 0.1" fails there for printed and corrected coefficients.
-/

namespace Checked.Cosmography.FREta

open Filter Topology Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.FRCosmo

/-! ## Definitions -/

/-- ΛCDM deceleration parameter (11.39). -/
noncomputable def qL (Ω : ℝ) : ℝ := 3 / 2 * Ω - 1
/-- ΛCDM jerk (11.39). -/
def jL : ℝ := 1
/-- ΛCDM snap (11.39). -/
noncomputable def sL (Ω : ℝ) : ℝ := 1 - 9 / 2 * Ω
/-- ΛCDM lerk (11.39). -/
noncomputable def lL (Ω : ℝ) : ℝ := 1 + 3 * Ω + 27 / 2 * Ω ^ 2

/-- `F″(R₀)H₀⁴/F(R₀)` from (11.21), (11.23): `(P₂Ω + Q₂)/(36(P₀Ω + Q₀))` (`R` cancels). -/
noncomputable def eta20Of (Ω q j s l : ℝ) : ℝ :=
  (P2 q j s * Ω + Q2 q j s) / (36 * (P0 q j s l * Ω + Q0 q j s l))

/-- `F‴(R₀)H₀⁶/F(R₀)` from (11.21), (11.24): `(P₃Ω + Q₃)/(216(j₀ − q₀ − 2)(P₀Ω + Q₀))`. -/
noncomputable def eta30Of (Ω q j s l : ℝ) : ℝ :=
  (P3 q j s l * Ω + Q3 q j s l) / (216 * (j - q - 2) * (P0 q j s l * Ω + Q0 q j s l))

/-- `η₂₀` on the common-`ε` family (11.41). -/
noncomputable def eta20 (Ω ε : ℝ) : ℝ :=
  eta20Of Ω (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε))

/-- `η₃₀` on the common-`ε` family (11.41). -/
noncomputable def eta30 (Ω ε : ℝ) : ℝ :=
  eta30Of Ω (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε))

/-- Denominator printed in (11.42)–(11.43), verbatim. -/
def printedDen (Ω : ℝ) : ℝ := (3 * (9 * Ω + 74) * Ω - 556) * Ω ^ 2 + 16

/-- Coefficient of `ε` printed in (11.42), verbatim. -/
noncomputable def printed20 (Ω : ℝ) : ℝ :=
  (64 - 6 * Ω * (9 * Ω + 8)) / printedDen Ω * (1 / 27)

/-- Coefficient of `ε` printed in (11.43), verbatim. -/
noncomputable def printed30 (Ω : ℝ) : ℝ :=
  (6 * ((81 * Ω - 110) * Ω + 40) * Ω + 16) / printedDen Ω * (1 / (243 * Ω ^ 2))

/-- Derived coefficient of `ε` in `η₂₀` (`runs/2026-10-30T1628Z/scripts/gen_eta.py`). -/
noncomputable def correct20 (Ω : ℝ) : ℝ :=
  -2 * (27 * Ω ^ 2 + 24 * Ω - 32) / (27 * Ω * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112))

/-- Derived coefficient of `ε` in `η₃₀`. -/
noncomputable def correct30 (Ω : ℝ) : ℝ :=
  -2 * (81 * Ω ^ 2 - 60 * Ω - 16) / (243 * Ω ^ 2 * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112))

/-- Printed (11.42) as a first-order statement, for every `0 < Ω < 1` where it is defined. -/
def PrintedEta20Claim : Prop :=
  ∀ Ω : ℝ, 0 < Ω → Ω < 1 → printedDen Ω ≠ 0 → HasDerivAt (eta20 Ω) (printed20 Ω) 0

/-- Printed (11.43) as a first-order statement, for every `0 < Ω < 1` where it is defined. -/
def PrintedEta30Claim : Prop :=
  ∀ Ω : ℝ, 0 < Ω → Ω < 1 → printedDen Ω ≠ 0 → HasDerivAt (eta30 Ω) (printed30 Ω) 0

/-! ## Proof tools (helpers; not part of the frozen statements) -/

/-- `ε ↦ ε·K(ε)` has derivative `K(0)` at `0` when `K` is merely continuous at `0`. -/
lemma hasDerivAt_mul_cont {K : ℝ → ℝ} (hK : ContinuousAt K 0) :
    HasDerivAt (fun ε => ε * K ε) (K 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine (hK.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
  field_simp

/-- Numerator of `η₂₀` divided by `ε` (`gen_eta.py`, `N.txt`). -/
noncomputable def N2e (Ω ε : ℝ) : ℝ :=
  -81*Ω^3*ε^2/4 - 81*Ω^3*ε/2 - 81*Ω^3/4 + 81*Ω^2*ε^2/2 + 45*Ω^2*ε/2 - 18*Ω^2 - 27*Ω*ε^2
    + 39*Ω*ε + 24*Ω + 6*ε^2 - 26*ε

/-- Numerator of `η₃₀` divided by `ε`. -/
noncomputable def N3e (Ω ε : ℝ) : ℝ :=
  405*Ω^3*ε^2/4 + 162*Ω^3*ε + 243*Ω^3/4 - 387*Ω^2*ε^2/2 - 477*Ω^2*ε/2 - 45*Ω^2 + 123*Ω*ε^2
    + 99*Ω*ε - 12*Ω - 26*ε^2 - 2*ε

/-- `P₀Ω + Q₀` on the family. -/
noncomputable def Dfam (Ω ε : ℝ) : ℝ :=
  P0 (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε)) * Ω
    + Q0 (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε))

/-- `j₀ − q₀ − 2` on the family. -/
noncomputable def Jfam (Ω ε : ℝ) : ℝ := jL * (1 + ε) - qL Ω * (1 + ε) - 2

lemma Dfam_zero (Ω : ℝ) : Dfam Ω 0 = 9 * Ω ^ 2 * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112) / 32 := by
  unfold Dfam P0 Q0 qL jL sL lL; ring

lemma Dfam_cont (Ω : ℝ) : Continuous (Dfam Ω) := by
  unfold Dfam P0 Q0 qL jL sL lL; fun_prop

lemma N2e_cont (Ω : ℝ) : Continuous (N2e Ω) := by unfold N2e; fun_prop

lemma N3e_cont (Ω : ℝ) : Continuous (N3e Ω) := by unfold N3e; fun_prop

lemma Jfam_cont (Ω : ℝ) : Continuous (Jfam Ω) := by unfold Jfam qL jL; fun_prop

lemma eta20_eq (Ω : ℝ) : eta20 Ω = fun ε => ε * (N2e Ω ε / (36 * Dfam Ω ε)) := by
  funext ε
  unfold eta20 eta20Of
  rw [show P2 (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) * Ω
      + Q2 (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) = ε * N2e Ω ε by
    unfold P2 Q2 N2e qL jL sL; ring]
  unfold Dfam
  rw [mul_div_assoc]

lemma eta30_eq (Ω : ℝ) : eta30 Ω = fun ε => ε * (N3e Ω ε / (216 * Jfam Ω ε * Dfam Ω ε)) := by
  funext ε
  unfold eta30 eta30Of
  rw [show P3 (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε)) * Ω
      + Q3 (qL Ω * (1 + ε)) (jL * (1 + ε)) (sL Ω * (1 + ε)) (lL Ω * (1 + ε)) = ε * N3e Ω ε by
    unfold P3 Q3 N3e qL jL sL lL; ring]
  unfold Dfam Jfam
  rw [mul_div_assoc]

lemma printedDen_eq (Ω : ℝ) : printedDen Ω = (Ω - 2) * (27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8) := by
  unfold printedDen; ring

/-! ## Headline statements (frozen) -/

/-- The two ratios are the review's expressions in every model (no `≈`). -/
theorem eta_ratios (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ) (hM : IsFRCosmo Ω a F t₀)
    (hF : F (curv a t₀) ≠ 0)
    (hR : correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0)
    (hJ : cosmoCoeff 3 a t₀ - decel a t₀ - 2 ≠ 0) :
    deriv^[2] F (curv a t₀) * hubble a t₀ ^ 4 / F (curv a t₀) =
      eta20Of Ω (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ∧
    deriv^[3] F (curv a t₀) * hubble a t₀ ^ 6 / F (curv a t₀) =
      eta30Of Ω (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) := by
  obtain ⟨e1, e2, e3⟩ := fR_values Ω a F t₀ hM
  have hH : hubble a t₀ ≠ 0 := hM.expanding.ne'
  unfold eta20Of eta30Of
  generalize correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) = R
    at e1 e2 e3 hR
  generalize P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
      + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) = D at e1 ⊢
  generalize P2 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) * Ω
      + Q2 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) = N2 at e2 ⊢
  generalize P3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
      + Q3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) = N3 at e3 ⊢
  generalize cosmoCoeff 3 a t₀ - decel a t₀ - 2 = J at e3 hJ ⊢
  generalize F (curv a t₀) = F0 at e1 hF ⊢
  generalize deriv^[2] F (curv a t₀) = F2 at e2 ⊢
  generalize deriv^[3] F (curv a t₀) = F3 at e3 ⊢
  generalize hubble a t₀ = H at e1 e2 e3 hH ⊢
  have hD : D ≠ 0 := by
    intro h; simp only [h, mul_zero] at e1
    exact mul_ne_zero hR hF e1
  constructor
  · rw [div_eq_div_iff hF (by positivity)]
    linear_combination (6 * F2 * H ^ 2) * e1 - F0 * e2
  · rw [div_eq_div_iff hF (by simp [hJ, hD])]
    linear_combination (36 * F3 * H ^ 4 * J) * e1 - F0 * e3

/-- **Correct (11.42)**: `η₂₀ = correct20(Ω)·ε` to first order. -/
theorem eta20_hasDerivAt {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    eta20 Ω 0 = 0 ∧ HasDerivAt (eta20 Ω) (correct20 Ω) 0 := by
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by positivity
  have h2 : Ω - 2 ≠ 0 := by intro h; linarith
  have hD0 : Dfam Ω 0 ≠ 0 := by
    rw [Dfam_zero]; have := h0.ne'; positivity
  refine ⟨by rw [eta20_eq]; simp, ?_⟩
  rw [eta20_eq]
  have hK : ContinuousAt (fun ε => N2e Ω ε / (36 * Dfam Ω ε)) 0 :=
    (N2e_cont Ω).continuousAt.div ((continuous_const.mul (Dfam_cont Ω)).continuousAt)
      (mul_ne_zero (by norm_num) hD0)
  convert hasDerivAt_mul_cont hK using 1
  show correct20 Ω = N2e Ω 0 / (36 * Dfam Ω 0)
  have hΩ := h0.ne'
  unfold correct20
  rw [div_eq_div_iff (by simp [hΩ, h2, hq]) (mul_ne_zero (by norm_num) hD0), Dfam_zero]
  unfold N2e
  ring

/-- **Correct (11.43)**: `η₃₀ = correct30(Ω)·ε` to first order. -/
theorem eta30_hasDerivAt {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    eta30 Ω 0 = 0 ∧ HasDerivAt (eta30 Ω) (correct30 Ω) 0 := by
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by positivity
  have h2 : Ω - 2 ≠ 0 := by intro h; linarith
  have hD0 : Dfam Ω 0 ≠ 0 := by
    rw [Dfam_zero]; have := h0.ne'; positivity
  have hJ0 : Jfam Ω 0 ≠ 0 := by
    unfold Jfam qL jL; intro h; linarith
  refine ⟨by rw [eta30_eq]; simp, ?_⟩
  rw [eta30_eq]
  have hK : ContinuousAt (fun ε => N3e Ω ε / (216 * Jfam Ω ε * Dfam Ω ε)) 0 :=
    (N3e_cont Ω).continuousAt.div
      (((continuous_const.mul (Jfam_cont Ω)).mul (Dfam_cont Ω)).continuousAt)
      (mul_ne_zero (mul_ne_zero (by norm_num) hJ0) hD0)
  convert hasDerivAt_mul_cont hK using 1
  show correct30 Ω = N3e Ω 0 / (216 * Jfam Ω 0 * Dfam Ω 0)
  have hΩ := h0.ne'
  unfold correct30
  rw [div_eq_div_iff (by simp [hΩ, h2, hq]) (mul_ne_zero (mul_ne_zero (by norm_num) hJ0) hD0),
    Dfam_zero]
  unfold N3e Jfam qL jL
  ring

/-- Printed (11.42) fails at every `Ω ∈ (0,1)` where it is defined, except the two roots of
`(54Ω² − 29Ω − 2)(27Ω² + 24Ω − 32)` (Ω ≈ 0.599, 0.731). -/
theorem printedEta20_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hd : printedDen Ω ≠ 0)
    (hne : (54 * Ω ^ 2 - 29 * Ω - 2) * (27 * Ω ^ 2 + 24 * Ω - 32) ≠ 0) :
    ¬ HasDerivAt (eta20 Ω) (printed20 Ω) 0 := by
  intro h
  have he := (eta20_hasDerivAt h0 h1).2.unique h
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by positivity
  have h2 : Ω - 2 ≠ 0 := by intro h; linarith
  have hΩ := h0.ne'
  rw [printedDen_eq] at hd
  have hc : 27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8 ≠ 0 := right_ne_zero_of_mul hd
  have key : correct20 Ω - printed20 Ω = -8 * (27 * Ω ^ 2 + 24 * Ω - 32) * (54 * Ω ^ 2 - 29 * Ω - 2)
      / (27 * Ω * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112) * (27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8)) := by
    unfold correct20 printed20; rw [printedDen_eq, div_mul_div_comm,
      div_sub_div _ _ (by simp [hΩ, h2, hq]) (by simp [h2, hc]),
      div_eq_div_iff (by simp [hΩ, h2, hq, hc]) (by simp [hΩ, h2, hq, hc])]
    ring
  rw [he, sub_self] at key
  have hn : -8 * (27 * Ω ^ 2 + 24 * Ω - 32) * (54 * Ω ^ 2 - 29 * Ω - 2) ≠ 0 := by
    intro hz; apply hne; linear_combination (-1 / 8) * hz
  have := h0.ne'
  exact div_ne_zero hn (by positivity) key.symm

/-- Printed (11.43) fails at the same parameter values. -/
theorem printedEta30_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) (hd : printedDen Ω ≠ 0)
    (hne : (54 * Ω ^ 2 - 29 * Ω - 2) * (27 * Ω ^ 2 + 24 * Ω - 32) ≠ 0) :
    ¬ HasDerivAt (eta30 Ω) (printed30 Ω) 0 := by
  intro h
  have he := (eta30_hasDerivAt h0 h1).2.unique h
  have hq : (27 * Ω ^ 2 + 60 * Ω + 112) ≠ 0 := by positivity
  have h2 : Ω - 2 ≠ 0 := by intro h; linarith
  have hΩ := h0.ne'
  rw [printedDen_eq] at hd
  have hc : 27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8 ≠ 0 := right_ne_zero_of_mul hd
  have key : correct30 Ω - printed30 Ω = -4 * (3 * Ω + 8) * (27 * Ω ^ 2 + 24 * Ω - 32)
      * (54 * Ω ^ 2 - 29 * Ω - 2) / (243 * Ω ^ 2 * (Ω - 2) * (27 * Ω ^ 2 + 60 * Ω + 112)
        * (27 * Ω ^ 3 + 276 * Ω ^ 2 - 4 * Ω - 8)) := by
    unfold correct30 printed30; rw [printedDen_eq, div_mul_div_comm,
      div_sub_div _ _ (by simp [hΩ, h2, hq]) (by simp [hΩ, h2, hc]),
      div_eq_div_iff (by simp [hΩ, h2, hq, hc]) (by simp [hΩ, h2, hq, hc])]
    ring
  rw [he, sub_self] at key
  have h8 : 3 * Ω + 8 ≠ 0 := by positivity
  have hn : -4 * (3 * Ω + 8) * (27 * Ω ^ 2 + 24 * Ω - 32) * (54 * Ω ^ 2 - 29 * Ω - 2) ≠ 0 := by
    intro hz
    have : (3 * Ω + 8) * ((54 * Ω ^ 2 - 29 * Ω - 2) * (27 * Ω ^ 2 + 24 * Ω - 32)) = 0 := by
      linear_combination (-1 / 4) * hz
    exact mul_ne_zero h8 hne this
  have := h0.ne'
  exact div_ne_zero hn (by positivity) key.symm

theorem printedEta20Claim_false : ¬ PrintedEta20Claim := by
  intro h
  exact printedEta20_false_at (Ω := 1 / 4) (by norm_num) (by norm_num)
    (by unfold printedDen; norm_num) (by norm_num)
    (h _ (by norm_num) (by norm_num) (by unfold printedDen; norm_num))

theorem printedEta30Claim_false : ¬ PrintedEta30Claim := by
  intro h
  exact printedEta30_false_at (Ω := 1 / 4) (by norm_num) (by norm_num)
    (by unfold printedDen; norm_num) (by norm_num)
    (h _ (by norm_num) (by norm_num) (by unfold printedDen; norm_num))

/-- **Correct (11.44)–(11.45)** at the paper's fiducial values: `η₂₀ ≈ −0.249ε, −0.032ε`;
`η₃₀ ≈ −0.400ε, −0.0152ε` (printed: `0.15ε, −0.12ε`; `4ε, −0.18ε`). -/
theorem eta_numbers :
    correct20 (41 / 1000) ∈ Set.Ioo (-0.25) (-0.24) ∧
    correct20 (1 / 4) ∈ Set.Ioo (-0.033) (-0.031) ∧
    correct30 (41 / 1000) ∈ Set.Ioo (-0.41) (-0.39) ∧
    correct30 (1 / 4) ∈ Set.Ioo (-0.016) (-0.015) := by
  unfold correct20 correct30
  norm_num [Set.mem_Ioo]

end Checked.Cosmography.FREta
