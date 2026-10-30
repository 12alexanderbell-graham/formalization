import Mathlib
import Work.Cosmography.CPLCoefficients

/-!
# Fidelity audit for C4 (annex 40.2): the blind restatement, closed in Lean

The `C4Blind` block below is copied verbatim from `runs/2026-10-30T0430Z/C4_blind.lean` (written by
a subagent from `source_C4.md` alone). After it, namespace `C4Audit` proves:
* `blind_l0`: in the restater's own model, l₀ equals the corrected formula (derived from
  `flatCPL_coeffs`: the blind model implies ours);
* `blindL0Claim_false`: the restater's own reading of the printed Eq. (22) is false (same witness);
* `blind_vs_printed`: in the blind model, printed − true = −2(1−Ω)(7−Ω)wₐ².
-/

namespace C4Blind

noncomputable section

/-- Hubble rate, Eq. (2): `H = ȧ / a`. -/
def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Redshift, `z := a(t₀)/a(t) − 1`. -/
def redshift (a : ℝ → ℝ) (t0 t : ℝ) : ℝ := a t0 / a t - 1

/-- `E²(z)` of Eq. (17), flat, `ΩX = 1 − Ωm`. -/
def E2CPL (Ωm w0 wa z : ℝ) : ℝ :=
  Ωm * (1 + z) ^ (3 : ℕ)
    + (1 - Ωm) * (1 + z) ^ (3 * (1 + w0 + wa)) * Real.exp (-3 * wa * z / (1 + z))

/-- Fifth cosmographic coefficient, Eq. (2): `l = (1/a) a⁽⁵⁾ / H⁵`. -/
def lCoeff (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  iteratedDeriv 5 a t / a t / hubble a t ^ 5

/-- The model hypothesis: `a` is a positive `C^5` scale factor near `t0`, expanding at `t0`,
whose Hubble rate obeys Eq. (17) on a neighbourhood of `t0`. -/
def CPLModel (Ωm w0 wa t0 : ℝ) (a : ℝ → ℝ) : Prop :=
  ∃ ε > 0,
    ContDiffOn ℝ 5 a (Set.Ioo (t0 - ε) (t0 + ε)) ∧
    (∀ t ∈ Set.Ioo (t0 - ε) (t0 + ε), 0 < a t) ∧
    0 < hubble a t0 ∧
    ∀ t ∈ Set.Ioo (t0 - ε) (t0 + ε),
      hubble a t ^ 2 = hubble a t0 ^ 2 * E2CPL Ωm w0 wa (redshift a t0 t)

/-- The right-hand side of Eq. (22), transcribed literally. -/
def printedL0 (Ωm w0 wa : ℝ) : ℝ :=
  35 / 2
    + (1 - Ωm) / 4 * (213 + (7 - Ωm) * wa) * wa
    + (1 - Ωm) / 4 * (489 + 9 * (82 - 21 * Ωm) * wa) * w0
    + 9 / 2 * (1 - Ωm) * (67 - 21 * Ωm + 3 / 2 * (23 - 11 * Ωm) * wa) * w0 ^ 2
    + 27 / 4 * (1 - Ωm) * (47 - 24 * Ωm) * w0 ^ 3
    + 81 / 2 * (1 - Ωm) * (3 - 2 * Ωm) * w0 ^ 4

/-- Eq. (22) as printed: for all parameters and every scale factor obeying the model,
`l0 = printedL0`. -/
def BlindL0Claim : Prop :=
  ∀ (Ωm w0 wa t0 : ℝ) (a : ℝ → ℝ),
    CPLModel Ωm w0 wa t0 a → lCoeff a t0 = printedL0 Ωm w0 wa

end

end C4Blind

namespace C4Audit

open Filter Topology Checked.Cosmography Checked.Cosmography.Aviles Work.Cosmography.CPL

lemma hubble_eq (a : ℝ → ℝ) (t : ℝ) : C4Blind.hubble a t = hubble a t := rfl
lemma redshift_eq (a : ℝ → ℝ) (t₀ t : ℝ) : C4Blind.redshift a t₀ t = redshift a t₀ t := rfl

/-- The blind model implies ours (plus `C⁵` at `t₀`). -/
theorem blind_implies (Ω w₀ wₐ t₀ : ℝ) (a : ℝ → ℝ) (h : C4Blind.CPLModel Ω w₀ wₐ t₀ a) :
    IsFlatCPL Ω w₀ wₐ a t₀ ∧ ContDiffAt ℝ 5 a t₀ := by
  obtain ⟨ε, hε, hcd, hpos, hH, hlaw⟩ := h
  have hI : Set.Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hs : ContDiffAt ℝ 5 a t₀ := hcd.contDiffAt hI
  refine ⟨⟨hH, ?_⟩, hs⟩
  have hd : ContDiffAt ℝ 4 (deriv a) t₀ := hs.derivWithin (by norm_num)
  have hHc : ContinuousAt (hubble a) t₀ :=
    hd.continuousAt.div hs.continuousAt (hpos t₀ ⟨by linarith, by linarith⟩).ne'
  have hHpos : ∀ᶠ t in 𝓝 t₀, 0 < hubble a t := hHc.eventually (lt_mem_nhds hH)
  have hIo : ∀ᶠ t in 𝓝 t₀, t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) := hI
  filter_upwards [hHpos, hIo, hIo.eventually_nhds] with t hHt ht ht'
  refine ⟨hpos t ht, ?_, ?_⟩
  · exact (hcd.contDiffAt (Ioo_mem_nhds ht.1 ht.2)).differentiableAt (by norm_num)
  · have hl := hlaw t ht
    rw [hubble_eq, hubble_eq, redshift_eq, C4Blind.E2CPL] at hl
    have e : -3 * wₐ * redshift a t₀ t / (1 + redshift a t₀ t) =
        -(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t) := by ring
    rw [e] at hl
    rw [← Real.sqrt_sq hHt.le, hl, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (show (0 : ℝ) ≤ hubble a t₀ from hH.le)]

/-- l₀ in the restater's own model: the corrected formula. -/
theorem blind_l0 (Ω w₀ wₐ t₀ : ℝ) (a : ℝ → ℝ) (h : C4Blind.CPLModel Ω w₀ wₐ t₀ a) :
    C4Blind.lCoeff a t₀ = 35 / 2 + (1 - Ω) / 4 * (213 + 9 * (7 - Ω) * wₐ) * wₐ
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * wₐ) * w₀
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * w₀ ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * w₀ ^ 4 := by
  obtain ⟨hL, hs⟩ := blind_implies Ω w₀ wₐ t₀ a h
  rw [← (flatCPL_coeffs Ω w₀ wₐ a t₀ hL hs).2.2.2, C4Blind.lCoeff, cosmoCoeff, div_div]
  rfl

theorem blind_vs_printed (Ω w₀ wₐ t₀ : ℝ) (a : ℝ → ℝ) (h : C4Blind.CPLModel Ω w₀ wₐ t₀ a) :
    C4Blind.printedL0 Ω w₀ wₐ - C4Blind.lCoeff a t₀ = -2 * (1 - Ω) * (7 - Ω) * wₐ ^ 2 := by
  rw [blind_l0 Ω w₀ wₐ t₀ a h, C4Blind.printedL0]; ring

/-- The witness satisfies the blind model on `(−1/2, 1/2)`. -/
theorem cplW_blind : C4Blind.CPLModel 0 (-1) (2 / 3) 0 cplW := by
  have hpos : ∀ t ∈ Set.Ioo ((0 : ℝ) - 1 / 2) (0 + 1 / 2), 0 < cplW t := by
    intro t ht
    have hu : 0 < 1 - t := by linarith [ht.2]
    have := Real.log_le_sub_one_of_pos hu
    show 0 < 1 - Real.log (1 - t)
    linarith [ht.1]
  refine ⟨1 / 2, by norm_num, ?_, hpos, by rw [hubble_eq, hubble_cplW_zero]; norm_num, ?_⟩
  · intro t ht
    exact (contDiffAt_cplW 5 (by linarith [ht.2])).contDiffWithinAt
  · intro t ht
    have hz : 1 + redshift cplW 0 t = 1 / cplW t := by rw [redshift, cplW_zero]; ring
    have hp := hpos t ht
    have e : -3 * (2 / 3 : ℝ) * redshift cplW 0 t / (1 + redshift cplW 0 t) =
        -(3 * (2 / 3) * redshift cplW 0 t) / (1 + redshift cplW 0 t) := by ring
    rw [hubble_eq, hubble_eq, redshift_eq, C4Blind.E2CPL, e,
      cplW_law hp (by linarith [ht.2]), mul_pow, hubble_cplW_zero, Real.sq_sqrt]
    rw [hz]; positivity

/-- **The restater's reading of the printed Eq. (22) is false.** -/
theorem blindL0Claim_false : ¬ C4Blind.BlindL0Claim := by
  intro h
  have h1 := h 0 (-1) (2 / 3) 0 cplW cplW_blind
  rw [blind_l0 0 (-1) (2 / 3) 0 cplW cplW_blind, C4Blind.printedL0] at h1
  norm_num at h1

/-! ## Sanity tests (40.3) -/

/-- ΛCDM is the CPL model with `w₀ = −1, wₐ = 0`. -/
theorem lcdm_isFlatCPL {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h : IsFlatLCDM Ω a t₀) :
    IsFlatCPL Ω (-1) 0 a t₀ := by
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2] with t ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  congr 2
  norm_num
  ring

/-- Bites: on ΛCDM the CPL theorem returns the (separately generated and proved) ΛCDM l₀. -/
theorem cpl_agrees_lcdm (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (h : IsFlatLCDM Ω a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) :
    cosmoCoeff 5 a t₀ = 1 + 3 * Ω + 27 / 2 * Ω ^ 2 ∧
    (35 / 2 + (1 - Ω) / 4 * (213 + 9 * (7 - Ω) * 0) * 0
      + (1 - Ω) / 4 * (489 + 9 * (82 - 21 * Ω) * 0) * (-1)
      + 9 / 2 * (1 - Ω) * (67 - 21 * Ω + 3 / 2 * (23 - 11 * Ω) * 0) * (-1) ^ 2
      + 27 / 4 * (1 - Ω) * (47 - 24 * Ω) * (-1) ^ 3
      + 81 / 2 * (1 - Ω) * (3 - 2 * Ω) * (-1) ^ 4 : ℝ) = 1 + 3 * Ω + 27 / 2 * Ω ^ 2 := by
  refine ⟨?_, by ring⟩
  rw [(flatCPL_coeffs Ω (-1) 0 a t₀ (lcdm_isFlatCPL h) (hs.of_le (by norm_num))).2.2.2]
  ring

/-- Not vacuous for any `w₀, wₐ`: Einstein–de Sitter is flat CPL with `Ω = 1`, every `w₀, wₐ`;
the theorem then gives `l₀ = 35/2`, matching the independent direct computation `l0_eds`. -/
theorem eds_isFlatCPL (w₀ wₐ : ℝ) {t₀ : ℝ} (h₀ : 0 < t₀) : IsFlatCPL 1 w₀ wₐ eds t₀ := by
  have h := eds_isFlatLCDM h₀
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2] with t ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  congr 2
  ring

theorem eds_l0_check (w₀ wₐ : ℝ) {t₀ : ℝ} (h₀ : 0 < t₀) :
    cosmoCoeff 5 eds t₀ = 35 / 2 ∧
    (35 / 2 + (1 - 1) / 4 * (213 + 9 * (7 - 1) * wₐ) * wₐ
      + (1 - 1) / 4 * (489 + 9 * (82 - 21 * 1) * wₐ) * w₀
      + 9 / 2 * (1 - 1) * (67 - 21 * 1 + 3 / 2 * (23 - 11 * 1) * wₐ) * w₀ ^ 2
      + 27 / 4 * (1 - 1) * (47 - 24 * 1) * w₀ ^ 3
      + 81 / 2 * (1 - 1) * (3 - 2 * 1) * w₀ ^ 4 : ℝ) = 35 / 2 :=
  ⟨l0_eds h₀, by ring⟩

theorem eds_cpl_consistent (w₀ wₐ : ℝ) {t₀ : ℝ} (h₀ : 0 < t₀) :
    cosmoCoeff 5 eds t₀ = 35 / 2 := by
  rw [(flatCPL_coeffs 1 w₀ wₐ eds t₀ (eds_isFlatCPL w₀ wₐ h₀)
    (Real.contDiffAt_rpow_const_of_ne h₀.ne')).2.2.2]
  ring

end C4Audit
