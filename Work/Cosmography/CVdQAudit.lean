import Mathlib
import Work.Cosmography.CVdQ

/-! C1 audit. Blind restatement copied verbatim from `runs/2026-10-30T0828Z/blind/C1_blind.lean` (only the imports changed), followed by the comparison `C1Audit`. -/

/-!
# C1 (blind restatement): Cattoën–Visser 2007, Eq. (59), flat case Ω₀ = 1

Source: C. Cattoën, M. Visser, "The Hubble series: convergence properties and redshift
variables", CQG 24 (2007) 5985, arXiv:0710.1887v1, Eq. (59):

  d_Q(y) = d_H y { 1 − (q₀/2) y + (1/12)[3 − 2q₀ + 12q₀² − 4(j₀ + Ω₀)] y² + O(y³) }.

Units c = 1, so d_H = 1/H₀.  All definitions below are written from the source text only.

## Junk-value risks (documented)
* `hubble a t = deriv a t / a t`: if `a` is not differentiable at `t`, `deriv a t = 0`
  (Mathlib junk), and if `a t = 0` the quotient is `0`.  We exclude both by the
  admissibility hypotheses (`a` smooth and everywhere positive).
* `decel`, `jerk` use `(hubble a t)⁻¹`; if `H = 0` then `0⁻¹ = 0` and q, j become junk `0`.
  Excluded by requiring `0 < deriv a t₀` (expanding universe, so `H₀ > 0`, `d_H` finite).
* `redshift a t₀ t = a t₀ / a t - 1`: junk if `a t = 0`; excluded by positivity.
* `yRed = z/(1+z)`: junk (`= 0`) when `1 + z = 0`; impossible for positive `a`.
* `lumDist` uses the interval integral `∫ s in t..t₀, (a s)⁻¹`; if the integrand is not
  interval-integrable the integral is junk `0`.  For continuous positive `a` it is integrable.
  For `t > t₀` (future "emission") the interval integral is the negative oriented integral;
  this is why the main reading uses the past-only filter `𝓝[<] t₀`.
* `decelDist` uses `Real.rpow` `(1+z)^(3/2 : ℝ)`; for a negative base `Real.rpow` returns a
  junk value; for positive `a` we have `1 + z = a t₀ / a t > 0`, so this is the genuine power.
-/

open Real Filter Topology Asymptotics
open scoped ContDiff

namespace C1Blind

noncomputable section

/-- Hubble parameter `H = ȧ/a`. -/
def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Deceleration parameter `q = −(ä/a) H⁻²`. -/
def decel (a : ℝ → ℝ) (t : ℝ) : ℝ := -(deriv (deriv a) t / a t) * (hubble a t)⁻¹ ^ 2

/-- Jerk parameter `j = (a⃛/a) H⁻³`. -/
def jerk (a : ℝ → ℝ) (t : ℝ) : ℝ := (deriv (deriv (deriv a)) t / a t) * (hubble a t)⁻¹ ^ 3

/-- Redshift of light emitted at time `t` and received at `t₀`: `1 + z = a(t₀)/a(t)`. -/
def redshift (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1

/-- The y-redshift `y = z/(1+z)`. -/
def yRed (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := redshift a t₀ t / (1 + redshift a t₀ t)

/-- Flat-FLRW luminosity distance (c = 1): `d_L = a₀ (1+z) ∫_t^{t₀} dt'/a(t')`. -/
def lumDist (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t₀ * (1 + redshift a t₀ t) * ∫ s in t..t₀, (a s)⁻¹

/-- Deceleration distance `d_Q = d_L / (1+z)^{3/2}` (real power via `Real.rpow`). -/
def decelDist (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDist a t₀ t / (1 + redshift a t₀ t) ^ ((3 : ℝ) / 2)

/-- The y² coefficient inside the braces of Eq. (59), exactly as printed. -/
def printedQ2 (q₀ j₀ Ω₀ : ℝ) : ℝ := (1 / 12) * (3 - 2 * q₀ + 12 * q₀ ^ 2 - 4 * (j₀ + Ω₀))

/-- The independently derived (correct) y² coefficient: half of the printed one. -/
def correctQ2 (q₀ j₀ Ω₀ : ℝ) : ℝ := (1 / 24) * (3 - 2 * q₀ + 12 * q₀ ^ 2 - 4 * (j₀ + Ω₀))

/-- Admissible flat FLRW scale factor at observation time `t₀`: analytic (strongest
smoothness class, i.e. most charitable for a universal claim), everywhere positive, and
expanding at `t₀` (so `H₀ > 0`). -/
structure Admissible (a : ℝ → ℝ) (t₀ : ℝ) : Prop where
  smooth : ContDiff ℝ ω a
  pos : ∀ t, 0 < a t
  expanding : 0 < deriv a t₀

/-- **Printed claim (Eq. 59, flat, Ω₀ = 1).**  For every admissible flat model,
`H₀ d_Q − y[1 − (q₀/2) y + Q² y²] = o(y³)` as the emission time `t → t₀⁻`,
with `Q²` exactly as printed. -/
def PrintedClaim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => hubble a t₀ * decelDist a t₀ t
        - yRed a t₀ t * (1 - decel a t₀ / 2 * yRed a t₀ t
            + printedQ2 (decel a t₀) (jerk a t₀) 1 * yRed a t₀ t ^ 2))
      =o[𝓝[<] t₀] (fun t => yRed a t₀ t ^ 3)

/-- The remainder for an arbitrary y² coefficient `Q2`. -/
def seriesRemainder (Q2 : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * decelDist a t₀ t
    - yRed a t₀ t * (1 - decel a t₀ / 2 * yRed a t₀ t + Q2 * yRed a t₀ t ^ 2)

/-- Stronger reading: two-sided limit `t → t₀`. -/
def PrintedClaimTwoSided : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => seriesRemainder (printedQ2 (decel a t₀) (jerk a t₀) 1) a t₀ t)
      =o[𝓝 t₀] (fun t => yRed a t₀ t ^ 3)

/-- Stronger reading: literal `y · O(y³) = O(y⁴)` remainder (past-only). -/
def PrintedClaimBigO4 : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => seriesRemainder (printedQ2 (decel a t₀) (jerk a t₀) 1) a t₀ t)
      =O[𝓝[<] t₀] (fun t => yRed a t₀ t ^ 4)

/-! ## de Sitter computations: `a = exp`, `t₀ = 0` (H₀ = 1, q₀ = −1, j₀ = 1) -/

lemma admissible_exp : Admissible Real.exp 0 :=
  ⟨Real.contDiff_exp, Real.exp_pos, by simp [Real.deriv_exp]⟩

lemma hubble_exp : hubble Real.exp 0 = 1 := by simp [hubble, Real.deriv_exp]

lemma decel_exp : decel Real.exp 0 = -1 := by simp [decel, hubble, Real.deriv_exp]

lemma jerk_exp : jerk Real.exp 0 = 1 := by simp [jerk, hubble, Real.deriv_exp]

lemma yRed_exp (t : ℝ) : yRed Real.exp 0 t = 1 - Real.exp t := by
  have h := (Real.exp_pos t).ne'
  simp only [yRed, redshift, Real.exp_zero]
  field_simp
  ring

lemma integral_exp_inv (t : ℝ) : (∫ s in t..(0 : ℝ), (Real.exp s)⁻¹) = Real.exp (-t) - 1 := by
  have : (fun s => (Real.exp s)⁻¹) = fun s => Real.exp (-s) := by
    funext s; rw [Real.exp_neg]
  rw [this, intervalIntegral.integral_comp_neg (fun x => Real.exp x), integral_exp]
  simp

lemma decelDist_exp (t : ℝ) :
    decelDist Real.exp 0 t = (Real.exp (t / 2))⁻¹ - Real.exp (t / 2) := by
  set w := Real.exp (t / 2) with hw
  have hw0 : 0 < w := Real.exp_pos _
  have h2 : Real.exp t = w ^ 2 := by
    rw [hw, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hpow : (1 + redshift Real.exp 0 t) ^ ((3 : ℝ) / 2) = (w ^ 3)⁻¹ := by
    have : 1 + redshift Real.exp 0 t = Real.exp (-t) := by
      simp [redshift, Real.exp_neg]
    rw [this, ← Real.exp_mul, show -t * (3 / 2) = -((3 : ℕ) * (t / 2)) by push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul]
  rw [decelDist, hpow, lumDist, integral_exp_inv]
  simp only [redshift, Real.exp_zero, Real.exp_neg, h2]
  field_simp
  ring

/-- Ratio remainder / y³ in de Sitter, in the variable `w = exp(t/2)`. -/
def dSRatio (Q2 : ℝ) (t : ℝ) : ℝ :=
  let w := Real.exp (t / 2)
  (1 - w / 4 - 3 * w ^ 2 / 2 - 3 * w ^ 3 / 4) / (w * (1 + w) ^ 2) + 3 / 4 - Q2

lemma ratio_eq (Q2 : ℝ) {t : ℝ} (ht : t ≠ 0) :
    seriesRemainder Q2 Real.exp 0 t / yRed Real.exp 0 t ^ 3 = dSRatio Q2 t := by
  set w := Real.exp (t / 2) with hw
  have hw0 : 0 < w := Real.exp_pos _
  have h2 : Real.exp t = w ^ 2 := by
    rw [hw, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hw1 : w ≠ 1 := by
    intro h
    rw [hw, Real.exp_eq_one_iff] at h
    exact ht (by linarith)
  have hy : 1 - w ^ 2 ≠ 0 := by
    intro h
    have : (w - 1) * (w + 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hw1 (by linarith)
    · linarith
  have hw1' : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hp : (1 + w) ≠ 0 := by positivity
  simp only [seriesRemainder, dSRatio, hubble_exp, decel_exp, decelDist_exp, yRed_exp, h2,
    ← hw]
  rw [div_eq_iff (pow_ne_zero 3 hy)]
  field_simp
  ring

lemma dSRatio_tendsto (Q2 : ℝ) : Tendsto (dSRatio Q2) (𝓝 0) (𝓝 (3 / 8 - Q2)) := by
  have hc : Continuous (dSRatio Q2) := by
    unfold dSRatio
    refine Continuous.sub (Continuous.add (Continuous.div (by fun_prop) (by fun_prop) ?_)
      continuous_const) continuous_const
    intro t
    have := Real.exp_pos (t / 2)
    positivity
  have := hc.tendsto 0
  convert this using 2
  simp [dSRatio]
  norm_num

/-- In de Sitter, remainder / y³ → 3/8 − Q2 as t → 0⁻. -/
lemma ratio_tendsto (Q2 : ℝ) :
    Tendsto (fun t => seriesRemainder Q2 Real.exp 0 t / yRed Real.exp 0 t ^ 3)
      (𝓝[<] 0) (𝓝 (3 / 8 - Q2)) := by
  refine ((dSRatio_tendsto Q2).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (ratio_eq Q2 (ne_of_lt ht)).symm

lemma deSitter_not_littleO (Q2 : ℝ) (hQ : Q2 ≠ 3 / 8) :
    ¬ (fun t => seriesRemainder Q2 Real.exp 0 t) =o[𝓝[<] (0:ℝ)]
        (fun t => yRed Real.exp 0 t ^ 3) := by
  intro h
  have h0 := h.tendsto_div_nhds_zero
  have := tendsto_nhds_unique (ratio_tendsto Q2) h0
  exact hQ (by linarith)

/-! ## Main results -/

/-- The printed Eq. (59) (flat case) is false: de Sitter is a counterexample. -/
theorem not_printedClaim : ¬ PrintedClaim := by
  intro h
  have h1 := h Real.exp 0 admissible_exp
  rw [decel_exp, jerk_exp] at h1
  refine deSitter_not_littleO (printedQ2 (-1) 1 1) (by norm_num [printedQ2]) ?_
  simpa [seriesRemainder, decel_exp] using h1

theorem not_printedClaimTwoSided : ¬ PrintedClaimTwoSided := by
  intro h
  apply not_printedClaim
  intro a t₀ ha
  exact (h a t₀ ha).mono nhdsWithin_le_nhds

theorem not_printedClaimBigO4 : ¬ PrintedClaimBigO4 := by
  intro h
  have h1 := h Real.exp 0 admissible_exp
  rw [decel_exp, jerk_exp] at h1
  have hy : Tendsto (fun t => yRed Real.exp 0 t) (𝓝[<] (0:ℝ)) (𝓝 0) := by
    simp only [yRed_exp]
    have : Tendsto (fun t => 1 - Real.exp t) (𝓝 (0:ℝ)) (𝓝 (1 - Real.exp 0)) :=
      (continuous_const.sub Real.continuous_exp).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h43 : (fun t => yRed Real.exp 0 t ^ 4) =o[𝓝[<] (0:ℝ)] (fun t => yRed Real.exp 0 t ^ 3) :=
    (isLittleO_pow_pow (𝕜 := ℝ) (by norm_num : 3 < 4)).comp_tendsto hy
  exact deSitter_not_littleO (printedQ2 (-1) 1 1) (by norm_num [printedQ2])
    (h1.trans_isLittleO h43)

/-- Sanity check: with the derived coefficient (1/24)[…], de Sitter satisfies the claim. -/
theorem deSitter_correct :
    (fun t => seriesRemainder (correctQ2 (decel Real.exp 0) (jerk Real.exp 0) 1) Real.exp 0 t)
      =o[𝓝[<] (0:ℝ)] (fun t => yRed Real.exp 0 t ^ 3) := by
  rw [decel_exp, jerk_exp]
  rw [isLittleO_iff_tendsto']
  · have := ratio_tendsto (correctQ2 (-1) 1 1)
    norm_num [correctQ2] at this ⊢
    exact this
  · filter_upwards [self_mem_nhdsWithin] with t ht
    intro h0
    exfalso
    rw [yRed_exp] at h0
    have : Real.exp t < 1 := by simpa using Real.exp_lt_exp.mpr ht
    have : (1 - Real.exp t) ^ 3 > 0 := by
      have : 0 < 1 - Real.exp t := by linarith
      positivity
    linarith

end

end C1Blind

/-! ## Comparison with the program's statements (`Work.Cosmography.CVdQ`) -/

namespace C1Audit

open Filter Topology Asymptotics Checked.Cosmography Checked.Cosmography.Aviles
  Checked.Cosmography.BambaY Work.Cosmography.CVdQ
open scoped ContDiff

lemma decel_eq (a : ℝ → ℝ) (t₀ : ℝ) (ha0 : a t₀ ≠ 0) : C1Blind.decel a t₀ = decel a t₀ := by
  simp only [C1Blind.decel, C1Blind.hubble, decel]
  by_cases h : deriv a t₀ = 0
  · simp [h]
  · field_simp

lemma jerk_eq (a : ℝ → ℝ) (t₀ : ℝ) (ha0 : a t₀ ≠ 0) :
    C1Blind.jerk a t₀ = cosmoCoeff 3 a t₀ := by
  have h3 : iteratedDeriv 3 a = deriv (deriv (deriv a)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  simp only [C1Blind.jerk, C1Blind.hubble, cosmoCoeff, hubble, h3]
  by_cases h : deriv a t₀ = 0
  · simp [h]
  · field_simp

lemma remainder_eq (a : ℝ → ℝ) (t₀ t : ℝ) (ha0 : a t₀ ≠ 0) (Q : ℝ → ℝ → ℝ → ℝ) :
    C1Blind.seriesRemainder (Q (C1Blind.decel a t₀) (C1Blind.jerk a t₀) 1) a t₀ t
      = remainderQ Q a t₀ t := by
  simp only [C1Blind.seriesRemainder, remainderQ, C1Blind.decelDist, dQFlat, C1Blind.lumDist,
    lumDistFlat, comoving, C1Blind.yRed, yred, C1Blind.redshift, redshift, C1Blind.hubble, hubble,
    decel_eq a t₀ ha0, jerk_eq a t₀ ha0, seriesQ, one_div]

/-- The blind claim implies the program's frozen past claim (same analytic class). -/
theorem blind_implies_ours : C1Blind.PrintedClaim → CVdQClaimPast := by
  intro h a t₀ han hpos hH
  have hadm : C1Blind.Admissible a t₀ := by
    refine ⟨han, hpos, ?_⟩
    have := hH; simp only [hubble] at this
    exact (div_pos_iff_of_pos_right (hpos t₀)).1 this
  refine (h a t₀ hadm).congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => rfl)
  show _ = remainderQ printedQ2 a t₀ t
  rw [← remainder_eq a t₀ t (hpos t₀).ne' printedQ2]; rfl

theorem blind_false : ¬ C1Blind.PrintedClaim := fun h => cvdQClaimPast_false (blind_implies_ours h)

/-- The program's general theorem gives the blind restater's derived coefficient. -/
theorem blind_derived_holds (a : ℝ → ℝ) (t₀ : ℝ) (h : C1Blind.Admissible a t₀) :
    (fun t => C1Blind.seriesRemainder
      (C1Blind.correctQ2 (C1Blind.decel a t₀) (C1Blind.jerk a t₀) 1) a t₀ t) =o[𝓝 t₀]
      (fun t => C1Blind.yRed a t₀ t ^ 3) := by
  have ha0 := (h.pos t₀).ne'
  have hH : hubble a t₀ ≠ 0 := div_ne_zero h.expanding.ne' ha0
  have hC : ContDiffAt ℝ 3 a t₀ := (h.smooth.of_le le_top).contDiffAt
  refine (dQ_y_third_order a t₀ hC ha0 hH).congr' (Eventually.of_forall fun t => ?_)
    (Eventually.of_forall fun t => rfl)
  show remainderQ correctQ2 a t₀ t = _
  rw [← remainder_eq a t₀ t ha0 correctQ2]; rfl

/-- Sanity: de Sitter values; correct coefficient 3/8 (= exact y(1−y)^{−1/2}), printed 3/4. -/
example : correctQ2 (-1) 1 1 = 3 / 8 ∧ printedQ2 (-1) 1 1 = 3 / 4 := by
  norm_num [correctQ2, printedQ2]

end C1Audit
