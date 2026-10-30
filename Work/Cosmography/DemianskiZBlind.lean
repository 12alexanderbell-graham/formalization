import Checked.Cosmography.BambaZ

/-!
# Blind restatement (annex 40.2): Demianski, Piedipalumbo, Sawant, Amati, A&A 598, A113 (2017),
arXiv:1609.09631, Eqs. (13)–(23), p. 3 (d_L reprinted in Lusso et al., A&A 628, L4 (2019),
arXiv:1907.07692, Eqs. (2)–(6), same coefficients incl. `−105q₀⁴`)

Source as read from the typeset page (crops at 200/400 dpi):
"d_L(z) = (cz/H₀)(D⁰_L + D¹_L z + D²_L z² + D³_L z³ + D⁴_L z⁴ + O(z⁵)) (13),
D⁰_L = 1 (14), D¹_L = −½(−1 + q₀) (15), D²_L = −⅙(1 − q₀ − 3q₀² + j₀) (16),
D³_L = (1/24)(2 − 2q₀ − 15q₀² − 15q₀³ + 5j₀ + 10q₀j₀ + s₀) (17),
D⁴_L = (1/120)(−6 + 6q₀ + 81q₀² + 165q₀³ − 105q₀⁴ − 110q₀j₀ + [newline] − 105q₀²j₀ − 15q₀s₀
− 27j₀ + 10j² − 11s₀ − l₀)",
"d_A(z) = (cz/H₀)(D⁰_A + … + D⁴_A z⁴ + O(z⁵)) (18), D⁰_A = 1 (19), D¹_A = −½(3 + q₀) (20),
D²_A = ⅙(11 + 7q₀ + 3q₀² − j₀) (21),
D³_A = −(1/24)(50 + 46q₀ + 39q₀² + 15q₀³ − 13j₀ − 10q₀j₀ − s₀ + [newline] − 2kc²(5 + 3q₀)/(H₀²a₀²)) (22),
D⁴_A = (1/120)(274 + 326q₀ + 411q₀² + 315q₀³ + 105q₀⁴ − [newline] −210q₀j₀ − 105q₀²j₀ − 15q₀s₀
+ 137j₀ + 10j₀² − 21s₀ − l₀) (23)".

Definitions in the paper: Eqs. (2)–(6) `H = ȧ/a`, `q = −ä/(aH²)`, `j = a⃛/(aH³)`, `s = a⁽⁴⁾/(aH⁴)`,
`l = a⁽⁵⁾/(aH⁵)` at `t₀` (= `hubble`, `decel`, `cosmoCoeff 3/4/5`); Eq. (11) fifth-order Taylor
expansion of `a(t)/a(t₀)` with remainder `O((t−t₀)⁶)`; "only relies on the assumption of the FLRW
metric". The paper never states flatness; the only curvature symbol is `k` in (22).

Reading choices (mine):
* line breaks: the sign at the start of a continuation line governs (`+ ⏎ −105` = `−105`,
  `− ⏎ −210` = `−210`, `+ ⏎ − 2kc²…` = `− 2kc²…`); `10j²` = `10j₀²`; `c = 1`; `k` is the FLRW
  curvature constant `K` of `d_L = a₀(1+z)S_K(χ)`, entering as `K/(H₀²a₀²)`.
* `O(z⁵)` inside the bracket means the remainder of `d_L` is `O(z⁶)`; I claim only the WEAKER
  `d_L − (z/H₀)·P(z) = o(z⁵)` (refuting the weaker claim refutes the printed one), and only from
  the past (`t → t₀⁻`, i.e. `z → 0⁺`, photons emitted before `t₀`), again the weaker claim.
* scale factor: `C⁶` at `t₀` (Eq. (11) is a fifth-order Taylor expansion with `O((t−t₀)⁶)`),
  `a(t₀) > 0`, `H₀ > 0`.
* curvature: two versions of each claim — flat (`K = 0`; then the `k` term of (22) vanishes) and
  general `K` (the printed coefficients exactly, `k` only where printed).
-/

namespace Work.Cosmography.DemianskiZBlind

open Filter Asymptotics Topology Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaY Checked.Cosmography.BambaK Checked.Cosmography.BambaA
open Checked.Cosmography.BambaZ

/-- `k c²/(H₀² a₀²)` with `c = 1`. -/
noncomputable def kTerm (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ := K / (hubble a t₀ ^ 2 * a t₀ ^ 2)

/-- (15) -/
noncomputable def D1L (q : ℝ) : ℝ := -(1 / 2) * (-1 + q)
/-- (16) -/
noncomputable def D2L (q j : ℝ) : ℝ := -(1 / 6) * (1 - q - 3 * q ^ 2 + j)
/-- (17) -/
noncomputable def D3L (q j s : ℝ) : ℝ :=
  (1 / 24) * (2 - 2 * q - 15 * q ^ 2 - 15 * q ^ 3 + 5 * j + 10 * q * j + s)
/-- D⁴_L as printed (`−105q₀⁴`). -/
noncomputable def D4L (q j s l : ℝ) : ℝ :=
  (1 / 120) * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 - 105 * q ^ 4 - 110 * q * j
    + -105 * q ^ 2 * j - 15 * q * s - 27 * j + 10 * j ^ 2 - 11 * s - l)

/-- (20) -/
noncomputable def D1A (q : ℝ) : ℝ := -(1 / 2) * (3 + q)
/-- (21) -/
noncomputable def D2A (q j : ℝ) : ℝ := (1 / 6) * (11 + 7 * q + 3 * q ^ 2 - j)
/-- (22), with `k = K/(H₀²a₀²)`. -/
noncomputable def D3A (q j s k : ℝ) : ℝ :=
  -(1 / 24) * (50 + 46 * q + 39 * q ^ 2 + 15 * q ^ 3 - 13 * j - 10 * q * j - s
    + -(2 * k * (5 + 3 * q)))
/-- (23) as printed (`+137j₀`). -/
noncomputable def D4A (q j s l : ℝ) : ℝ :=
  (1 / 120) * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4
    + -210 * q * j - 105 * q ^ 2 * j - 15 * q * s + 137 * j + 10 * j ^ 2 - 21 * s - l)

/-- `(z/H₀)(D⁰ + D¹z + D²z² + D³z³ + D⁴z⁴)` with `D⁰ = 1`. -/
noncomputable def series (H d1 d2 d3 d4 z : ℝ) : ℝ :=
  z / H * (1 + d1 * z + d2 * z ^ 2 + d3 * z ^ 3 + d4 * z ^ 4)

/-- `d_L − (cz/H₀)(D⁰_L + … + D⁴_L z⁴)` (Eq. (13) minus its displayed polynomial). -/
noncomputable def errL (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDist K a t₀ t -
    series (hubble a t₀) (D1L (decel a t₀)) (D2L (decel a t₀) (cosmoCoeff 3 a t₀))
      (D3L (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀))
      (D4L (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
      (redshift a t₀ t)

/-- `d_A − (cz/H₀)(D⁰_A + … + D⁴_A z⁴)` (Eq. (18)). -/
noncomputable def errA (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  angDist K a t₀ t -
    series (hubble a t₀) (D1A (decel a t₀)) (D2A (decel a t₀) (cosmoCoeff 3 a t₀))
      (D3A (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (kTerm K a t₀))
      (D4A (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
      (redshift a t₀ t)

/-- Hypotheses on the scale factor: `C⁶` at `t₀`, `a(t₀) > 0`, `H₀ > 0`. -/
def Admissible (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ContDiffAt ℝ 6 a t₀ ∧ 0 < a t₀ ∧ 0 < hubble a t₀

/-- Eqs. (13)–(17), flat reading. -/
def DemianskiDLzFlat : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => errL 0 a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)

/-- Eqs. (13)–(17), any curvature `K` (printed `D_L` has no curvature terms). -/
def DemianskiDLzCurved : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => errL K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)

/-- Eqs. (18)–(23), flat reading (`k = 0` in (22)). -/
def DemianskiDAzFlat : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => errA 0 a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)

/-- Eqs. (18)–(23), any curvature `K` (`k` only in `D³_A`, as printed). -/
def DemianskiDAzCurved : Prop :=
  ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), Admissible a t₀ →
    (fun t => errA K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)

/-! ### Refutations (via the Checked general theorems `lumDist_z_fifth_order`,
`angDist_z_fifth_order`) -/

lemma kTerm_eq (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : kTerm K a t₀ = curvK K a t₀ := rfl

lemma redshift_tendsto_past (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0) :
    Tendsto (fun t => redshift a t₀ t) (𝓝[<] t₀) (𝓝 0) :=
  (redshift_tendsto a t₀ hd ha0).mono_left nhdsWithin_le_nhds

/-- Flat `d_L`: the printed `D⁴_L` (`−105q₀⁴`) fails, from the past, in every `C⁵` model with
`a₀ ≠ 0`, `H₀ ≠ 0`, `q₀ ≠ 0`; the defect is `(7/4) q₀⁴ z⁵ / H₀`. -/
theorem flat_DL_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) (hq : decel a t₀ ≠ 0) :
    ¬ (fun t => errL 0 a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (lumDist_z_fifth_order 0 a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  have hdiff : (fun t => (7 / 4 * decel a t₀ ^ 4) * redshift a t₀ t ^ 5)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
    refine ((hp.const_mul_left (hubble a t₀)).sub hc).congr' (Eventually.of_forall fun t => ?_)
      EventuallyEq.rfl
    simp only [errL, remLz, seriesZ, series, correctDL4z, printedDL4z, DL1z, DL2z, DL3z, D1L, D2L,
      D3L, D4L, curvK, zero_div]
    field_simp
    ring
  exact not_isLittleO_self_past_z a t₀ hd ha0 hH 5
    (mul_ne_zero (by norm_num) (pow_ne_zero 4 hq)) hdiff

/-- Flat `d_A`: the printed `D⁴_A` (`+137j₀`) fails, from the past, in every `C⁵` model with
`a₀ ≠ 0`, `H₀ ≠ 0`, `j₀ ≠ 0`; the defect is `−(137/60) j₀ z⁵ / H₀`. -/
theorem flat_DA_fails_past (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) (hj : cosmoCoeff 3 a t₀ ≠ 0) :
    ¬ (fun t => errA 0 a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (angDist_z_fifth_order 0 a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  have hdiff : (fun t => (-(137 / 60) * cosmoCoeff 3 a t₀) * redshift a t₀ t ^ 5)
      =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
    refine ((hp.const_mul_left (hubble a t₀)).sub hc).congr' (Eventually.of_forall fun t => ?_)
      EventuallyEq.rfl
    simp only [errA, remAz, seriesZ, series, correctDA4z, printedDA4z, DA1z, DA2z, DA3z, D1A, D2A,
      D3A, D4A, kTerm_eq, curvK, zero_div]
    field_simp
    ring
  exact not_isLittleO_self_past_z a t₀ hd ha0 hH 5 (mul_ne_zero (by norm_num) hj) hdiff

/-- `c z³ + z⁴ g` with `g` bounded is `o(z⁵)` only if `c = 0` (from the past). -/
lemma cubic_obstruction (a : ℝ → ℝ) (t₀ : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0) {c A B : ℝ} (hc : c ≠ 0)
    (h : (fun t => c * redshift a t₀ t ^ 3 + redshift a t₀ t ^ (3 + 1) *
        (A + B * redshift a t₀ t)) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5)) : False := by
  have hz0 := redshift_tendsto_past a t₀ hd ha0
  have h53 : (fun t => redshift a t₀ t ^ 5) =O[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 3) := by
    have := (pow_succ_mul_isLittleO hz0 3 (fun t => redshift a t₀ t)
      (CCS.bdd hz0 id continuous_id)).isBigO
    refine this.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only; ring
  have hg := pow_succ_mul_isLittleO hz0 3 (fun t => A + B * redshift a t₀ t)
    (CCS.bdd hz0 (fun x => A + B * x) (by fun_prop))
  have h3 := (h.trans_isBigO h53).sub hg
  exact not_isLittleO_self_past_z a t₀ hd ha0 hH 3 hc
    (h3.congr' (Eventually.of_forall fun t => by simp only; ring) EventuallyEq.rfl)

/-- Curved `d_L`: the printed series (no curvature) fails at order `z³` (missing `−k z³/6`) in
every `C⁵` model with `a₀ ≠ 0`, `H₀ ≠ 0`, `K ≠ 0`. -/
theorem curved_DL_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (hK : K ≠ 0) :
    ¬ (fun t => errL K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (lumDist_z_fifth_order K a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  have hk : -(curvK K a t₀ / 6) ≠ 0 :=
    neg_ne_zero.2 (div_ne_zero (div_ne_zero hK (mul_ne_zero (pow_ne_zero 2 hH)
      (pow_ne_zero 2 ha0))) (by norm_num))
  refine cubic_obstruction a t₀ hd ha0 hH (A := DL3z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀)
      - D3L (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀))
    (B := correctDL4z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀) (curvK K a t₀)
      - D4L (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) hk ?_
  refine ((hp.const_mul_left (hubble a t₀)).sub hc).congr' (Eventually.of_forall fun t => ?_)
    EventuallyEq.rfl
  simp only [errL, remLz, seriesZ, series, DL1z, DL2z, D1L, D2L]
  field_simp
  ring

/-- Curved `d_A`: the printed series (curvature only in `D³_A`) fails at order `z³` (missing
`−k z³/6` in `D²_A`) in every `C⁵` model with `a₀ ≠ 0`, `H₀ ≠ 0`, `K ≠ 0`. -/
theorem curved_DA_fails_past (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (ha : ContDiffAt ℝ 5 a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0) (hK : K ≠ 0) :
    ¬ (fun t => errA K a t₀ t) =o[𝓝[<] t₀] (fun t => redshift a t₀ t ^ 5) := by
  intro hp
  have hd : DifferentiableAt ℝ a t₀ := ha.differentiableAt (by norm_num)
  have hc := (angDist_z_fifth_order K a t₀ ha ha0 hH).mono (nhdsWithin_le_nhds (s := Set.Iio t₀))
  have hk : -(curvK K a t₀ / 6) ≠ 0 :=
    neg_ne_zero.2 (div_ne_zero (div_ne_zero hK (mul_ne_zero (pow_ne_zero 2 hH)
      (pow_ne_zero 2 ha0))) (by norm_num))
  refine cubic_obstruction a t₀ hd ha0 hH (A := DA3z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀)
      - D3A (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (curvK K a t₀))
    (B := correctDA4z (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)
      (cosmoCoeff 5 a t₀) (curvK K a t₀)
      - D4A (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) hk ?_
  refine ((hp.const_mul_left (hubble a t₀)).sub hc).congr' (Eventually.of_forall fun t => ?_)
    EventuallyEq.rfl
  simp only [errA, remAz, seriesZ, series, DA1z, DA2z, D1A, D2A, kTerm_eq]
  field_simp
  ring

/-! ### The four claims are false (de Sitter `a = exp`, `t₀ = 0`: `H₀ = 1`, `q₀ = −1`, `j₀ = 1`;
for the curved claims additionally `K = 1`) -/

lemma exp_admissible : Admissible Real.exp 0 :=
  ⟨Real.contDiff_exp.contDiffAt, Real.exp_pos 0, by rw [deSitter_vals.1]; norm_num⟩

theorem demianskiDLzFlat_false : ¬ DemianskiDLzFlat := fun h =>
  flat_DL_fails_past Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [deSitter_vals.1]; norm_num) (by rw [deSitter_vals.2.1]; norm_num)
    (h Real.exp 0 exp_admissible)

theorem demianskiDAzFlat_false : ¬ DemianskiDAzFlat := fun h =>
  flat_DA_fails_past Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [deSitter_vals.1]; norm_num) (by rw [deSitter_vals.2.2]; norm_num)
    (h Real.exp 0 exp_admissible)

theorem demianskiDLzCurved_false : ¬ DemianskiDLzCurved := fun h =>
  curved_DL_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [deSitter_vals.1]; norm_num) one_ne_zero (h 1 Real.exp 0 exp_admissible)

theorem demianskiDAzCurved_false : ¬ DemianskiDAzCurved := fun h =>
  curved_DA_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [deSitter_vals.1]; norm_num) one_ne_zero (h 1 Real.exp 0 exp_admissible)

end Work.Cosmography.DemianskiZBlind
