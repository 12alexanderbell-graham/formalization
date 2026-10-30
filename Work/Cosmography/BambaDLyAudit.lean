import Mathlib
import Work.Cosmography.BambaDLy

/-!
# C5 audit. Blind restatement copied verbatim from `runs/2026-10-30T0828Z/blind/C5_blind.lean` (only the imports changed), followed by the comparison `C5Audit`.
# C5 (blind restatement): flat-FLRW luminosity distance in the y-redshift

Source: Bamba–Capozziello–Nojiri–Odintsov, arXiv:1205.3421v3, Sec. X,
Eqs. (10.1)–(10.3), (10.26), (10.28), (10.52)–(10.54); claim C5 is the K = 0 instance
(so Ω₀ = 1 + K c²/(H₀² a₀²) = 1).

Units: c = 1 throughout.

## Reading choices for `PrintedClaim`
* Scale-factor class: `a : ℝ → ℝ` smooth (`ContDiff ℝ ∞`), strictly positive everywhere,
  and expanding at t₀ (`0 < deriv a t₀`, i.e. H₀ > 0). This is the class the source tacitly
  intends (Taylor-expandable `a`, defined q₀, j₀, invertible z ↔ t near t₀). It is generous:
  any narrower "physical" class still contains de Sitter `a = exp`, which is the counterexample.
* Filter: past-only, `𝓝[<] t₀` (emission time t < t₀). This is the *weaker* claim; the two-sided
  version implies it (`PrintedClaim_twoSided_imp`), so refuting the past-only version refutes both.
* Error size: `o(y³)` for the residual `H₀ d_L − y(1 + D¹ y + D² y²)`. The literal printed form
  `(y/H₀)[… + O(y³)]` gives a residual `O(y⁴)`, which implies `o(y³)` (`PrintedClaim_strong_imp`);
  so `o(y³)` is again the weaker reading and refuting it refutes the literal one.
* D¹, D² exactly as printed in (10.53)–(10.54), with Ω₀ = 1 + K/(H₀² a₀²) at K = 0.

## Independently derived coefficients (see C5_blind_sympy.py; also by hand)
For K = 0:  H₀ d_L = y + D¹ y² + D² y³ + O(y⁴) with
  D¹ = (3 − q₀)/2                          = −(1/2)(−3 + q₀)        (matches 10.53)
  D² = (11 − 5 q₀ + 3 q₀² − j₀)/6          = +(1/6)(12 − 5q₀ + 3q₀² − j₀ − Ω₀) at Ω₀ = 1.
This agrees with Cattoën–Visser (2007) Eq. (52) (`+1/6[…]`), but has the OPPOSITE overall sign
to the printed (10.54) (`−1/6(…)`). De Sitter (q₀ = −1, j₀ = 1): correct D² = 3, printed D² = −3;
indeed H₀ d_L = y/(1−y)² = y + 2y² + 3y³ + 4y⁴ + …, so the printed residual is 6y³ + O(y⁴).
-/

noncomputable section

namespace C5Blind

open Real Filter Topology Asymptotics

/-! ## Definitions -/

/-- Hubble parameter `H = ȧ/a` (10.1).
Junk: if `a` is not differentiable at `t`, `deriv a t = 0` so `H = 0`; if `a t = 0`, `H = 0`. -/
def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Deceleration `q = −(ä/a)/H²` (10.2).
Junk: `iteratedDeriv 2` is `0` where `a` is not twice differentiable; if `H = 0` then `q = 0`. -/
def decel (a : ℝ → ℝ) (t : ℝ) : ℝ := -(iteratedDeriv 2 a t / a t) / hubble a t ^ 2

/-- Jerk `j = (a⃛/a)/H³` (10.3). Junk as for `decel`. -/
def jerk (a : ℝ → ℝ) (t : ℝ) : ℝ := (iteratedDeriv 3 a t / a t) / hubble a t ^ 3

/-- Redshift of light emitted at `t` and received at `t₀`: `1 + z = a(t₀)/a(t)`.
Junk: if `a t = 0` then `z = −1`. -/
def redshift (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1

/-- y-redshift `y = z/(1+z)` (= `1 − a(t)/a(t₀)` when both are nonzero).
Junk: if `1 + z = 0` then `y = 0`. -/
def yRedshift (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := redshift a t₀ t / (1 + redshift a t₀ t)

/-- `r₀` for K = 0 (10.28) with c = 1, written in terms of the emission time `t = t₀ − D/c`:
`∫_t^{t₀} dt'/a(t')`.
Junk: `intervalIntegral` returns `0` if `1/a` is not interval-integrable on `[t, t₀]`; it is
oriented, so for `t > t₀` it is minus the integral over `[t₀, t]`; `1/a` is `0` where `a = 0`. -/
def comovingFlat (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ s in t..t₀, 1 / a s

/-- Luminosity distance of a flat FLRW model (10.26) with c = 1:
`d_L = [a(t₀)/a(t)] · (a(t₀) r₀)`, `t` the emission time.
Junk: inherits the junk of `comovingFlat` and `x/0 = 0`. -/
def lumDistFlat (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := (a t₀ / a t) * (a t₀ * comovingFlat a t₀ t)

/-- Ω₀ = 1 + K c²/(H₀² a₀²) with c = 1 (p. 110). Junk: equals 1 if `H₀ a₀ = 0`. -/
def omega0 (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ := 1 + K / (hubble a t₀ ^ 2 * a t₀ ^ 2)

/-- D¹_{L,y} as printed (10.53). -/
def D1 (q₀ : ℝ) : ℝ := -(1 / 2) * (-3 + q₀)

/-- D²_{L,y} as printed (10.54). -/
def D2printed (q₀ j₀ Ω₀ : ℝ) : ℝ := -(1 / 6) * (12 - 5 * q₀ + 3 * q₀ ^ 2 - j₀ - Ω₀)

/-- D² as independently derived (= Cattoën–Visser Eq. (52)): opposite sign to (10.54). -/
def D2derived (q₀ j₀ Ω₀ : ℝ) : ℝ := (1 / 6) * (12 - 5 * q₀ + 3 * q₀ ^ 2 - j₀ - Ω₀)

/-- The scale-factor class (see reading choices). -/
def Admissible (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a ∧ (∀ t, 0 < a t) ∧ 0 < deriv a t₀

/-- Residual `H₀ d_L − y[1 + D¹ y + D² y²]` with a chosen D²-formula, K = 0. -/
def residual (D2 : ℝ → ℝ → ℝ → ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hubble a t₀ * lumDistFlat a t₀ t
    - yRedshift a t₀ t * (1 + D1 (decel a t₀) * yRedshift a t₀ t
        + D2 (decel a t₀) (jerk a t₀) (omega0 0 a t₀) * yRedshift a t₀ t ^ 2)

/-! ## The claim -/

/-- **C5 as printed** (flat case, past-only filter, `o(y³)`):
`H₀ d_L − y[1 + D¹ y + D² y²] = o(y³)` as `t → t₀⁻`, with D¹, D² from (10.53)–(10.54). -/
def PrintedClaim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => residual D2printed a t₀ t) =o[𝓝[<] t₀] (fun t => yRedshift a t₀ t ^ 3)

/-- Two-sided variant. -/
def PrintedClaimTwoSided : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => residual D2printed a t₀ t) =o[𝓝 t₀] (fun t => yRedshift a t₀ t ^ 3)

/-- Literal variant: residual `O(y⁴)` (from `(y/H₀)[… + O(y³)]`). -/
def PrintedClaimStrong : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => residual D2printed a t₀ t) =O[𝓝[<] t₀] (fun t => yRedshift a t₀ t ^ 4)

theorem PrintedClaim_twoSided_imp : PrintedClaimTwoSided → PrintedClaim :=
  fun h a t₀ ha => (h a t₀ ha).mono nhdsWithin_le_nhds

theorem PrintedClaim_strong_imp : PrintedClaimStrong → PrintedClaim := by
  intro h a t₀ ha
  have hy : Tendsto (fun t => yRedshift a t₀ t) (𝓝[<] t₀) (𝓝 0) := by
    have hc : ContinuousAt (fun t => yRedshift a t₀ t) t₀ := by
      have hca : Continuous a := ha.1.continuous
      have h0 : a t₀ ≠ 0 := (ha.2.1 t₀).ne'
      unfold yRedshift redshift
      have hden : (1 + (a t₀ / a t₀ - 1)) ≠ 0 := by rw [div_self h0]; norm_num
      refine ContinuousAt.div ?_ ?_ hden
      · exact (continuousAt_const.div hca.continuousAt h0).sub continuousAt_const
      · exact continuousAt_const.add
          ((continuousAt_const.div hca.continuousAt h0).sub continuousAt_const)
    have : yRedshift a t₀ t₀ = 0 := by
      simp [yRedshift, redshift, div_self (ha.2.1 t₀).ne']
    rw [← this]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have h4 : (fun t => yRedshift a t₀ t ^ 4) =o[𝓝[<] t₀] (fun t => yRedshift a t₀ t ^ 3) := by
    have := ((isLittleO_one_iff ℝ).mpr hy).mul_isBigO
      (isBigO_refl (fun t => yRedshift a t₀ t ^ 3) (𝓝[<] t₀))
    exact (this.congr_left (fun t => by ring)).congr_right (fun t => by ring)
  exact (h a t₀ ha).trans_isLittleO h4

/-! ## Refutation via de Sitter `a = exp`, `t₀ = 0` -/

lemma hubble_exp (t : ℝ) : hubble exp t = 1 := by
  simp [hubble, Real.deriv_exp, (exp_pos t).ne']

lemma iteratedDeriv_exp (n : ℕ) : iteratedDeriv n exp = exp := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

lemma decel_exp (t : ℝ) : decel exp t = -1 := by
  simp [decel, iteratedDeriv_exp, hubble_exp, (exp_pos t).ne']

lemma jerk_exp (t : ℝ) : jerk exp t = 1 := by
  simp [jerk, iteratedDeriv_exp, hubble_exp, (exp_pos t).ne']

lemma omega0_flat (a : ℝ → ℝ) (t₀ : ℝ) : omega0 0 a t₀ = 1 := by simp [omega0]

lemma yRedshift_exp (t : ℝ) : yRedshift exp 0 t = 1 - exp t := by
  have h := (exp_pos t).ne'
  simp only [yRedshift, redshift, exp_zero]
  field_simp
  ring

lemma comovingFlat_exp (t : ℝ) : comovingFlat exp 0 t = exp (-t) - 1 := by
  have : (fun s => 1 / exp s) = fun s => exp (-s) := by
    funext s; rw [exp_neg, one_div]
  simp only [comovingFlat, this]
  rw [intervalIntegral.integral_comp_neg (fun s => exp s), integral_exp]
  simp

lemma lumDistFlat_exp (t : ℝ) : lumDistFlat exp 0 t = exp (-t) * (exp (-t) - 1) := by
  simp [lumDistFlat, comovingFlat_exp, exp_neg]

/-- Explicit de Sitter residual for the printed D²: `y³ (6 + (4y − 3y²)/(1−y)²)`, `y = 1 − eᵗ`. -/
lemma residual_exp (t : ℝ) :
    residual D2printed exp 0 t =
      (1 - exp t) ^ 3 * (6 + (4 * (1 - exp t) - 3 * (1 - exp t) ^ 2) / exp t ^ 2) := by
  have h := (exp_pos t).ne'
  simp only [residual, hubble_exp, lumDistFlat_exp, yRedshift_exp, decel_exp, jerk_exp,
    omega0_flat, D1, D2printed, exp_neg]
  field_simp
  ring

/-- **C5 as printed is false** (already for de Sitter). -/
theorem not_PrintedClaim : ¬ PrintedClaim := by
  intro hC
  have hadm : Admissible exp 0 := ⟨Real.contDiff_exp, exp_pos, by simp [Real.deriv_exp]⟩
  have hb := (hC exp 0 hadm).bound (show (0 : ℝ) < 1 / 2 by norm_num)
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 := self_mem_nhdsWithin
  obtain ⟨t, hle, ht⟩ := (hb.and hev).exists
  rw [residual_exp, yRedshift_exp] at hle
  set u := exp t with hu
  have hu0 : 0 < u := exp_pos t
  have hu1 : u < 1 := by rw [hu]; exact Real.exp_lt_one_iff.mpr ht
  set y := 1 - u with hy
  have hy0 : 0 < y := by linarith
  have hy1 : y < 1 := by linarith
  have hfrac : 0 ≤ (4 * y - 3 * y ^ 2) / u ^ 2 :=
    div_nonneg (by nlinarith) (sq_nonneg u)
  have hy3 : 0 < y ^ 3 := pow_pos hy0 3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy3,
    abs_of_nonneg (mul_nonneg hy3.le (by linarith))] at hle
  nlinarith

theorem not_PrintedClaimTwoSided : ¬ PrintedClaimTwoSided :=
  fun h => not_PrintedClaim (PrintedClaim_twoSided_imp h)

theorem not_PrintedClaimStrong : ¬ PrintedClaimStrong :=
  fun h => not_PrintedClaim (PrintedClaim_strong_imp h)

/-- Sanity check: with the independently derived D², the de Sitter residual is
`y⁴ (4 − 3y)/(1−y)²`, i.e. genuinely of order y⁴. -/
lemma residual_exp_derived (t : ℝ) :
    residual D2derived exp 0 t =
      (1 - exp t) ^ 4 * (4 - 3 * (1 - exp t)) / exp t ^ 2 := by
  have h := (exp_pos t).ne'
  simp only [residual, hubble_exp, lumDistFlat_exp, yRedshift_exp, decel_exp, jerk_exp,
    omega0_flat, D1, D2derived, exp_neg]
  field_simp
  ring

end C5Blind

/-! ## Comparison with the program's statements (`Work.Cosmography.BambaY`) -/

namespace C5Audit

open Filter Topology Asymptotics Checked.Cosmography Checked.Cosmography.Aviles
  Work.Cosmography.BambaY
open scoped ContDiff

lemma decel_eq (a : ℝ → ℝ) (t₀ : ℝ) (ha0 : a t₀ ≠ 0) :
    C5Blind.decel a t₀ = decel a t₀ := by
  have h2 : iteratedDeriv 2 a = deriv (deriv a) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  simp only [C5Blind.decel, C5Blind.hubble, decel, h2]
  by_cases h : deriv a t₀ = 0
  · simp [h]
  · field_simp

lemma jerk_eq (a : ℝ → ℝ) (t₀ : ℝ) : C5Blind.jerk a t₀ = cosmoCoeff 3 a t₀ := by
  simp only [C5Blind.jerk, cosmoCoeff, C5Blind.hubble, hubble, div_div]

/-- The blind residual equals the program's remainder (any `a`, any `t`, once `a(t₀) ≠ 0`),
for the printed and for the corrected `D²`. -/
lemma residual_eq (a : ℝ → ℝ) (t₀ t : ℝ) (ha0 : a t₀ ≠ 0) :
    C5Blind.residual C5Blind.D2printed a t₀ t = remainderY printedD2y a t₀ t ∧
    C5Blind.residual C5Blind.D2derived a t₀ t = remainderY correctD2y a t₀ t := by
  have hΩ : C5Blind.omega0 0 a t₀ = 1 := by simp [C5Blind.omega0]
  simp only [C5Blind.residual, remainderY, C5Blind.lumDistFlat, lumDistFlat,
    C5Blind.comovingFlat, comoving, C5Blind.yRedshift, yred, C5Blind.redshift, redshift,
    C5Blind.hubble, hubble, decel_eq a t₀ ha0, jerk_eq, hΩ, seriesY, C5Blind.D1, D1y,
    C5Blind.D2printed, printedD2y, C5Blind.D2derived, correctD2y]
  constructor <;> ring

/-- The blind claim (C^∞, past-only) implies the program's frozen past claim (analytic). -/
theorem blind_implies_ours : C5Blind.PrintedClaim → BambaD2yClaimPast := by
  intro h a t₀ han hpos hH
  have hadm : C5Blind.Admissible a t₀ := by
    refine ⟨han.of_le le_top, hpos, ?_⟩
    have := hH; simp only [hubble] at this
    exact (div_pos_iff_of_pos_right (hpos t₀)).1 this
  exact (h a t₀ hadm).congr' (Eventually.of_forall fun t => (residual_eq a t₀ t (hpos t₀).ne').1)
    (Eventually.of_forall fun t => rfl)

/-- The program's frozen claim refutation also refutes the blind claim. -/
theorem blind_false : ¬ C5Blind.PrintedClaim := fun h => bambaD2yClaimPast_false (blind_implies_ours h)

/-- The program's general theorem gives the blind restater's derived coefficient (two-sided,
for every admissible model). -/
theorem blind_derived_holds (a : ℝ → ℝ) (t₀ : ℝ) (h : C5Blind.Admissible a t₀) :
    (fun t => C5Blind.residual C5Blind.D2derived a t₀ t) =o[𝓝 t₀]
      (fun t => C5Blind.yRedshift a t₀ t ^ 3) := by
  obtain ⟨hs, hpos, hd⟩ := h
  have ha0 := (hpos t₀).ne'
  have hH : hubble a t₀ ≠ 0 := div_ne_zero hd.ne' ha0
  exact (lumDist_y_third_order a t₀ (hs.of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt ha0 hH).congr'
    (Eventually.of_forall fun t => (residual_eq a t₀ t ha0).2.symm)
    (Eventually.of_forall fun t => rfl)

/-! ### Sanity tests (annex 40.3) -/

/-- Not vacuous: de Sitter satisfies every hypothesis of the general theorem. -/
example : ContDiffAt ℝ 3 Real.exp 0 ∧ Real.exp 0 ≠ 0 ∧ hubble Real.exp 0 ≠ 0 :=
  ⟨Real.contDiff_exp.contDiffAt, (Real.exp_pos 0).ne', by rw [deSitter_vals.1]; norm_num⟩

/-- Near-miss: with the corrected `D²` the de Sitter remainder is `o(y³)` (so the refutation
bites only on the printed sign), and the general theorem specialises to the known exact
de Sitter series `H₀ d_L = y/(1−y)² = y + 2y² + 3y³ + …`: `D¹ = 2`, `D² = 3`. -/
example : D1y (-1) = 2 ∧ correctD2y (-1) 1 1 = 3 ∧ printedD2y (-1) 1 1 = -3 := by
  norm_num [D1y, correctD2y, printedD2y]

end C5Audit
