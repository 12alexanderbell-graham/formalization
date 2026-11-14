import Checked.Trust.NecessityAD

/-! Hypothesis necessity for the smoothness hypothesis (hypothesis 1, `ContDiffAt ℝ 5`) of the two-sided
`CCS.printedD4_fails` (run 2026-11-14T2228Z; plan of run 2026-11-14T2028Z, STATE 0v).

A kinked scale factor cannot show this (`Checked.Trust.NecessityAD` covers the past-only companion): `D³`
contains `s₀`, so a kink below the fifth derivative changes a coefficient the printed series also uses, and a
kink in the fifth derivative gives different top coefficients on the two sides. The witness here is
`a = P + ε` with the quintic `P = 1 + t − t²/2 − (21/8) t⁵` and `ε(t) = t⁸ sin(1/t)` at `t₀ = 0`.
The function `ε` has four derivatives everywhere, all `0` at `0` (each is `t² · (bounded)` near `0`), and its
fourth derivative is `(1680 t⁴ − 180 t² + 1) sin(1/t) + (20 t − 840 t³) cos(1/t)`, which is not continuous at
`0` (it equals `1680 t⁴ − 180 t² + 1` at `t = 1/(π/2 + 2πn)`). So `a` is not `C⁵` at `0`, Lean's fifth
derivative of `a` at `0` is the junk value `0` (`l₀ = 0`), while `q₀ = 1`, `j₀ = 0`, `s₀ = 0` are `P`'s own.
Since `ε = O(t⁸)`, `a` agrees with `P`'s Taylor polynomial (`l₀ = −315`) up to `o(t⁵)`, and the correct
`D⁴` at `l₀ = −315` equals the printed `D⁴` at the junk `l₀ = 0`. The correct-order series theorem, restated
here with the Taylor expansion as a hypothesis instead of `C⁵` (`core`), then gives the two-sided `o(z⁵)`
bound the headline denies. So the smoothness hypothesis is needed. -/

namespace Checked.Trust.NecessityAH
open Set Filter Topology Asymptotics
open Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Trust.NecessityAD

/-! ### The series theorem with the Taylor expansion as a hypothesis -/

/-- The proof of `CCS.lookback_fifth_order` from the point where it has the Taylor expansion: for free
coefficients `q j s l`, if `a/a₀` agrees with `Apoly q j s l (H₀ (t₀ − t))` up to `o((t − t₀)⁵)`, the lookback
time has the correct series with these coefficients, two-sided. -/
theorem core (a : ℝ → ℝ) (t₀ q j s l : ℝ) (hd : DifferentiableAt ℝ a t₀) (ha0 : a t₀ ≠ 0)
    (hH : hubble a t₀ ≠ 0)
    (hT : (fun t => a t / a t₀ - CCS.Apoly q j s l (hubble a t₀ * (t₀ - t))) =o[𝓝 t₀]
      fun t => (t - t₀) ^ 5) :
    (fun t => hubble a t₀ * (t₀ - t) -
        CCS.series (CCS.correctD4 q j s l) q j s (redshift a t₀ t)) =o[𝓝 t₀]
      fun t => redshift a t₀ t ^ 5 := by
  set a₀ := a t₀ with ha₀
  set H := hubble a t₀ with hHdef
  set X : ℝ → ℝ := fun t => H * (t₀ - t) with hX
  set E : ℝ → ℝ := fun t => a t / a₀ - CCS.Apoly q j s l (X t) with hE
  have hXt : Tendsto X (𝓝 t₀) (𝓝 0) := by
    have : Continuous X := by fun_prop
    simpa [hX] using this.tendsto t₀
  have htX : (fun t => t - t₀) =O[𝓝 t₀] X := by
    refine IsBigO.of_bound (‖H‖⁻¹) (Eventually.of_forall fun t => ?_)
    simp only [hX, norm_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hH), one_mul, ← norm_neg]; ring_nf; rfl
  have hEo : E =o[𝓝 t₀] fun t => X t ^ 5 := hT.trans_isBigO (htX.pow 5)
  have key := CCS.inversion q j s l X E hXt hEo
  have hXz : X =O[𝓝 t₀] fun t => redshift a t₀ t := by
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by
      refine IsBigO.of_bound (‖H‖) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul, ← norm_neg (t₀ - t)]; ring_nf; rfl
    exact this.trans (CCS.sub_isBigO_redshift a t₀ hd ha0 hH)
  refine (key.trans_isBigO (hXz.pow 5)).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  have hz : 1 / (CCS.Apoly q j s l (X t) + E t) - 1 = redshift a t₀ t := by
    simp only [hE, redshift]; rw [add_sub_cancel, one_div_div]
  show X t - _ = _
  rw [hz]

/-! ### `t⁸ sin(1/t)` and its derivatives -/

/-- `A(t) sin(1/t) + B(t) cos(1/t)`. -/
noncomputable def osc (A B : ℝ → ℝ) (t : ℝ) : ℝ := A t * Real.sin (1 / t) + B t * Real.cos (1 / t)

theorem osc_hasDerivAt (A B : ℝ → ℝ) {A' B' t : ℝ} (ht : t ≠ 0) (hA : HasDerivAt A A' t)
    (hB : HasDerivAt B B' t) :
    HasDerivAt (osc A B) (osc (fun _ => A' + B t / t ^ 2) (fun _ => B' - A t / t ^ 2) t) t := by
  have hi : HasDerivAt (fun x : ℝ => 1 / x) (-(t ^ 2)⁻¹) t := by
    simpa [one_div] using hasDerivAt_inv ht
  have h := (hA.mul (hi.sin)).add (hB.mul (hi.cos))
  show HasDerivAt (fun y => A y * Real.sin (1 / y) + B y * Real.cos (1 / y))
    ((A' + B t / t ^ 2) * Real.sin (1 / t) + (B' - A t / t ^ 2) * Real.cos (1 / t)) t
  convert h using 1
  field_simp
  ring

/-- `t² G(t)` with `G` bounded near `0` has derivative `0` at `0`. -/
theorem hasDerivAt_zero_of_isBigO {f : ℝ → ℝ} (h0 : f 0 = 0) (h : f =O[𝓝 0] fun t => t ^ 2) :
    HasDerivAt f 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have e : (fun x : ℝ => f (0 + x) - f 0 - x • (0 : ℝ)) = f := by funext x; simp [h0]
  rw [e]
  exact h.trans_isLittleO (isLittleO_pow_id (by norm_num))

theorem osc_isBigO (A B : ℝ → ℝ) (hA : ContinuousAt A 0) (hB : ContinuousAt B 0) :
    osc A B =O[𝓝 0] fun _ => (1 : ℝ) := by
  have hA1 : A =O[𝓝 0] fun _ => (1 : ℝ) := hA.tendsto.isBigO_one ℝ
  have hB1 : B =O[𝓝 0] fun _ => (1 : ℝ) := hB.tendsto.isBigO_one ℝ
  have hs : (fun t : ℝ => Real.sin (1 / t)) =O[𝓝 0] fun _ => (1 : ℝ) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun t => by simpa using Real.abs_sin_le_one (1 / t))
  have hc : (fun t : ℝ => Real.cos (1 / t)) =O[𝓝 0] fun _ => (1 : ℝ) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun t => by simpa using Real.abs_cos_le_one (1 / t))
  have := (hA1.mul hs).add (hB1.mul hc)
  simpa [osc] using this

/-- `t² · osc A B` has derivative `0` at `0` when `A`, `B` are continuous at `0`. -/
theorem sq_osc_hasDerivAt_zero (A B : ℝ → ℝ) (hA : ContinuousAt A 0) (hB : ContinuousAt B 0) :
    HasDerivAt (fun t => t ^ 2 * osc A B t) 0 0 := by
  refine hasDerivAt_zero_of_isBigO (by simp) ?_
  have := (isBigO_refl (fun t : ℝ => t ^ 2) (𝓝 0)).mul (osc_isBigO A B hA hB)
  simpa using this

/-- `ε = t⁸ sin(1/t)` and its first four derivatives (`runs/2026-11-14T2228Z/scripts/eps_derivs.py`). -/
noncomputable def F0 (t : ℝ) : ℝ := osc (fun t => t ^ 8) (fun _ => 0) t
noncomputable def F1 (t : ℝ) : ℝ := osc (fun t => 8 * t ^ 7) (fun t => -t ^ 6) t
noncomputable def F2 (t : ℝ) : ℝ := osc (fun t => 56 * t ^ 6 - t ^ 4) (fun t => -14 * t ^ 5) t
noncomputable def F3 (t : ℝ) : ℝ :=
  osc (fun t => 336 * t ^ 5 - 18 * t ^ 3) (fun t => -126 * t ^ 4 + t ^ 2) t
noncomputable def F4 (t : ℝ) : ℝ :=
  osc (fun t => 1680 * t ^ 4 - 180 * t ^ 2 + 1) (fun t => -840 * t ^ 3 + 20 * t) t

theorem F0_hasDerivAt (t : ℝ) : HasDerivAt F0 (F1 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun t => t ^ 6) (fun _ => 0) (by fun_prop) (by fun_prop)
    have e : F1 0 = 0 := by simp [F1, osc]
    rw [e]
    convert h using 1
    funext x; simp only [F0, osc]; ring
  · have h := osc_hasDerivAt (fun t => t ^ 8) (fun _ => 0) ht (hasDerivAt_pow 8 t)
      (hasDerivAt_const t 0)
    unfold F0
    convert h using 1
    simp only [F1, osc]; field_simp; ring

theorem F1_hasDerivAt (t : ℝ) : HasDerivAt F1 (F2 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun t => 8 * t ^ 5) (fun t => -t ^ 4) (by fun_prop)
      (by fun_prop)
    have e : F2 0 = 0 := by simp [F2, osc]
    rw [e]
    convert h using 1
    funext x; simp only [F1, osc]; ring
  · have h := osc_hasDerivAt (fun t => 8 * t ^ 7) (fun t => -t ^ 6) ht
      ((hasDerivAt_pow 7 t).const_mul 8) ((hasDerivAt_pow 6 t).neg)
    unfold F1
    convert h using 1
    simp only [F2, osc]; field_simp; ring

theorem F2_hasDerivAt (t : ℝ) : HasDerivAt F2 (F3 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun t => 56 * t ^ 4 - t ^ 2) (fun t => -14 * t ^ 3)
      (by fun_prop) (by fun_prop)
    have e : F3 0 = 0 := by simp [F3, osc]
    rw [e]
    convert h using 1
    funext x; simp only [F2, osc]; ring
  · have h := osc_hasDerivAt (fun t => 56 * t ^ 6 - t ^ 4) (fun t => -14 * t ^ 5) ht
      (((hasDerivAt_pow 6 t).const_mul 56).sub (hasDerivAt_pow 4 t))
      ((hasDerivAt_pow 5 t).const_mul (-14))
    unfold F2
    convert h using 1
    simp only [F3, osc]; field_simp; ring

theorem F3_hasDerivAt (t : ℝ) : HasDerivAt F3 (F4 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun t => 336 * t ^ 3 - 18 * t) (fun t => -126 * t ^ 2 + 1)
      (by fun_prop) (by fun_prop)
    have e : F4 0 = 0 := by simp [F4, osc]
    rw [e]
    convert h using 1
    funext x; simp only [F3, osc]; ring
  · have h := osc_hasDerivAt (fun t => 336 * t ^ 5 - 18 * t ^ 3) (fun t => -126 * t ^ 4 + t ^ 2) ht
      (((hasDerivAt_pow 5 t).const_mul 336).sub ((hasDerivAt_pow 3 t).const_mul 18))
      (((hasDerivAt_pow 4 t).const_mul (-126)).add (hasDerivAt_pow 2 t))
    unfold F3
    convert h using 1
    simp only [F4, osc]; field_simp; ring

/-- `A(t) sin(1/t) + B(t) cos(1/t)` is not continuous at `0` when `A`, `B` are continuous with `A(0) ≠ 0` and
`B(0) = 0`: along `t = 1/(π/2 + 2πn)` it tends to `A(0)`, while its value at `0` is `B(0) = 0`. -/
theorem osc_not_continuousAt (A B : ℝ → ℝ) (hA : Continuous A) (hA0 : A 0 ≠ 0) (hB0 : B 0 = 0) :
    ¬ ContinuousAt (osc A B) 0 := by
  intro hc
  set u : ℕ → ℝ := fun n => 1 / (Real.pi / 2 + n * (2 * Real.pi)) with hu
  have hden : Tendsto (fun n : ℕ => Real.pi / 2 + n * (2 * Real.pi)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))
  have hu0 : Tendsto u atTop (𝓝 0) := by
    refine (hden.inv_tendsto_atTop).congr fun n => ?_
    simp [hu]
  have h1 := (hc.tendsto.comp hu0)
  have hval : ∀ n, osc A B (u n) = A (u n) := by
    intro n
    have e : 1 / u n = Real.pi / 2 + n * (2 * Real.pi) := by simp [hu]
    simp only [osc, e, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi, Real.sin_pi_div_two,
      Real.cos_pi_div_two]
    ring
  have h2 : Tendsto (osc A B ∘ u) atTop (𝓝 (A 0)) := by
    refine ((hA.tendsto 0).comp hu0).congr fun n => ?_
    simp [hval]
  have e0 : osc A B 0 = 0 := by simp [osc, hB0]
  rw [e0] at h1
  exact hA0 (tendsto_nhds_unique h1 h2).symm

/-- The fourth derivative of `t⁸ sin(1/t)` is not continuous at `0`. -/
theorem F4_not_continuousAt : ¬ ContinuousAt F4 0 :=
  osc_not_continuousAt _ _ (by fun_prop) (by norm_num) (by norm_num)

/-! ### The witnesses `a = 1 + t + b t² + f t⁵ + t⁸ sin(1/t)` -/

theorem PQ_hasDerivAt (α β γ ε ζ η t : ℝ) :
    HasDerivAt (PQ α β γ ε ζ η) (PQ β (2 * γ) (3 * ε) (4 * ζ) (5 * η) 0 t) t := by
  have hd : Differentiable ℝ (PQ α β γ ε ζ η) := by unfold PQ; fun_prop
  have h := (hd t).hasDerivAt
  rwa [PQ_deriv] at h

theorem deriv_sum {f g f' g' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t) : deriv (fun t => f t + g t) = fun t => f' t + g' t := by
  funext t; exact ((hf t).add (hg t)).deriv

/-- The scale factor `1 + t + b t² + f t⁵ + t⁸ sin(1/t)`. -/
noncomputable def W (b f : ℝ) (t : ℝ) : ℝ := PQ 1 1 b 0 0 f t + F0 t

theorem W_iter (b f : ℝ) :
    iteratedDeriv 1 (W b f) = (fun t => PQ 1 (2 * b) 0 0 (5 * f) 0 t + F1 t) ∧
    iteratedDeriv 2 (W b f) = (fun t => PQ (2 * b) 0 0 (20 * f) 0 0 t + F2 t) ∧
    iteratedDeriv 3 (W b f) = (fun t => PQ 0 0 (60 * f) 0 0 0 t + F3 t) ∧
    iteratedDeriv 4 (W b f) = (fun t => PQ 0 (120 * f) 0 0 0 0 t + F4 t) := by
  have d1 : iteratedDeriv 1 (W b f) = (fun t => PQ 1 (2 * b) 0 0 (5 * f) 0 t + F1 t) := by
    rw [iteratedDeriv_one]
    have := deriv_sum (fun t => PQ_hasDerivAt 1 1 b 0 0 f t) F0_hasDerivAt
    have hW : W b f = fun t => PQ 1 1 b 0 0 f t + F0 t := rfl
    rw [hW, this]; funext t; congr 1; simp only [PQ]; ring
  have d2 : iteratedDeriv 2 (W b f) = (fun t => PQ (2 * b) 0 0 (20 * f) 0 0 t + F2 t) := by
    rw [iteratedDeriv_succ, d1]
    rw [deriv_sum (fun t => PQ_hasDerivAt 1 (2 * b) 0 0 (5 * f) 0 t) F1_hasDerivAt]
    funext t; congr 1; simp only [PQ]; ring
  have d3 : iteratedDeriv 3 (W b f) = (fun t => PQ 0 0 (60 * f) 0 0 0 t + F3 t) := by
    rw [iteratedDeriv_succ, d2]
    rw [deriv_sum (fun t => PQ_hasDerivAt (2 * b) 0 0 (20 * f) 0 0 t) F2_hasDerivAt]
    funext t; congr 1; simp only [PQ]; ring
  have d4 : iteratedDeriv 4 (W b f) = (fun t => PQ 0 (120 * f) 0 0 0 0 t + F4 t) := by
    rw [iteratedDeriv_succ, d3]
    rw [deriv_sum (fun t => PQ_hasDerivAt 0 0 (60 * f) 0 0 0 t) F3_hasDerivAt]
    funext t; congr 1; simp only [PQ]; ring
  exact ⟨d1, d2, d3, d4⟩

/-- Lean's fifth derivative of `W b f` at `0` is the junk value `0`. -/
theorem W_iter5 (b f : ℝ) : iteratedDeriv 5 (W b f) 0 = 0 := by
  rw [iteratedDeriv_succ, (W_iter b f).2.2.2]
  apply deriv_zero_of_not_differentiableAt
  intro h
  apply F4_not_continuousAt
  have hp : DifferentiableAt ℝ (PQ 0 (120 * f) 0 0 0 0) 0 :=
    (PQ_smooth _ _ _ _ _ _ 1).differentiableAt (by norm_num)
  have := (h.sub hp).continuousAt
  convert this using 1
  funext t; simp

theorem W_zero (b f : ℝ) : W b f 0 = 1 := by simp [W, F0, osc, PQ]

theorem W_d1 (b f : ℝ) : deriv (W b f) 0 = 1 := by
  rw [← iteratedDeriv_one, (W_iter b f).1]; simp [F1, osc, PQ]

theorem W_coeffs (b f : ℝ) : hubble (W b f) 0 = 1 ∧ decel (W b f) 0 = -(2 * b) ∧
    cosmoCoeff 3 (W b f) 0 = 0 ∧ cosmoCoeff 4 (W b f) 0 = 0 ∧ cosmoCoeff 5 (W b f) 0 = 0 := by
  have h2 : deriv (deriv (W b f)) 0 = 2 * b := by
    have e : deriv (deriv (W b f)) = iteratedDeriv 2 (W b f) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [e, (W_iter b f).2.1]; simp [F2, osc, PQ]
  refine ⟨unit_hubble (W_zero b f) (W_d1 b f), ?_, ?_, ?_, ?_⟩
  · rw [unit_decel (W_zero b f) (W_d1 b f), h2]
  · rw [unit_coeff (W_zero b f) (W_d1 b f), (W_iter b f).2.2.1]; simp [F3, osc, PQ]
  · rw [unit_coeff (W_zero b f) (W_d1 b f), (W_iter b f).2.2.2]; simp [F4, osc, PQ]
  · rw [unit_coeff (W_zero b f) (W_d1 b f), W_iter5]

/-- `W b f` agrees with its quintic's Taylor polynomial (`q₀ = −2b`, `j₀ = s₀ = 0`, `l₀ = 120 f`) up to
`o(t⁵)`. -/
theorem W_taylor (b f : ℝ) :
    (fun t => W b f t / W b f 0 - CCS.Apoly (-(2 * b)) 0 0 (120 * f) (hubble (W b f) 0 * (0 - t)))
      =o[𝓝 0] fun t => (t - 0) ^ 5 := by
  have e : (fun t => W b f t / W b f 0 -
      CCS.Apoly (-(2 * b)) 0 0 (120 * f) (hubble (W b f) 0 * (0 - t))) = F0 := by
    funext t; rw [W_zero, (W_coeffs b f).1]; simp only [W, PQ, CCS.Apoly]; ring
  rw [e]
  have h8 : F0 =O[𝓝 0] fun t => t ^ 8 := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    simp only [F0, osc, Real.norm_eq_abs, zero_mul, add_zero, abs_mul, one_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  simpa using h8.trans_isLittleO (isLittleO_pow_pow (by norm_num : 5 < 8))

theorem W_diff (b f : ℝ) : Differentiable ℝ (W b f) := fun t =>
  ((PQ_hasDerivAt 1 1 b 0 0 f t).add (F0_hasDerivAt t)).differentiableAt

/-- Smoothness (`C⁵` at `t₀`) is needed in the two-sided `CCS.printedD4_fails`:
`a = 1 + t − t²/2 − (21/8) t⁵ + t⁸ sin(1/t)` has `a(0) = 1`, `H₀ = 1`, `q₀ = 1`, four derivatives everywhere
and a fourth derivative not continuous at `0`, so Lean's junk fifth derivative gives `l₀ = 0`; `a` agrees with
the quintic's Taylor polynomial (`l₀ = −315`) to `o(t⁵)`, and the correct `D⁴` at `l₀ = −315` equals the
printed `D⁴` at `l₀ = 0`, so the printed series holds with remainder `o(z⁵)` on both sides. -/
theorem printedD4_fails_h1 : necessity% Checked.Cosmography.CCS.printedD4_fails 1 := by
  obtain ⟨hH, hq, hj, hs, hl⟩ := W_coeffs (-1 / 2) (-(21 / 8))
  refine ⟨W (-1 / 2) (-(21 / 8)), 0, by rw [W_zero]; norm_num, by rw [hH]; norm_num,
    by rw [hq]; norm_num, ?_⟩
  have hc := core (W (-1 / 2) (-(21 / 8))) 0 (-(2 * (-1 / 2))) 0 0 (120 * (-(21 / 8)))
    (W_diff _ _ 0) (by rw [W_zero]; norm_num) (by rw [hH]; norm_num) (W_taylor _ _)
  refine hc.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [CCS.remainder, hH, hq, hj, hs, hl, CCS.printedD4, CCS.correctD4]
  norm_num

/-! ### `BambaY.printedD2y_fails` (flat `d_L(y)` to third order, top coefficient `j₀`)

Witness `1 + t + (11/3) t³ + t⁴ sin(1/t)`: two derivatives everywhere, second derivative
`(12 t² − 1) sin(1/t) − 6 t cos(1/t)` not continuous at `0`, so Lean's `j₀` is the junk `0`, `q₀ = 0`; the
cubic's own `j₀ = 22` makes the correct `D²` equal the printed one at `j₀ = 0`. -/

namespace Y
open Checked.Cosmography.BambaY

/-- The proof of `BambaY.lumDist_y_third_order` from the point where it has the Taylor expansion, for free
coefficients `q j` and a continuous scale factor. -/
theorem core (a : ℝ → ℝ) (t₀ q j : ℝ) (hc : Continuous a) (hd : DifferentiableAt ℝ a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hT : (fun t => a t / a t₀ - A3 q j (hubble a t₀ * (t₀ - t))) =o[𝓝 t₀] fun t => (t - t₀) ^ 3) :
    (fun t => hubble a t₀ * lumDistFlat a t₀ t - seriesY (correctD2y q j 1) q (yred a t₀ t))
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 3) := by
  set a₀ := a t₀ with ha₀
  set H := hubble a t₀ with hHdef
  have hne : {t | a t ≠ 0} ∈ 𝓝 t₀ := hd.continuousAt.eventually_ne ha0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hne
  set Bl := Metric.ball t₀ δ with hBl
  have hopen : IsOpen Bl := Metric.isOpen_ball
  have hmem : t₀ ∈ Bl := Metric.mem_ball_self hδ
  have hBl_nhds : Bl ∈ 𝓝 t₀ := hopen.mem_nhds hmem
  have hnz : ∀ t ∈ Bl, a t ≠ 0 := fun t ht => hball ht
  have hcont : ContinuousOn a Bl := hc.continuousOn
  set X : ℝ → ℝ := fun t => H * (t₀ - t) with hX
  set E : ℝ → ℝ := fun t => a t / a₀ - A3 q j (X t) with hE
  have hXc : Continuous X := by fun_prop
  have hXt : Tendsto X (𝓝 t₀) (𝓝 0) := by simpa [hX] using hXc.tendsto t₀
  have htX : ∀ n : ℕ, (fun t => (t - t₀) ^ n) =O[𝓝 t₀] fun t => X t ^ n := by
    intro n
    have : (fun t => t - t₀) =O[𝓝 t₀] X := by
      refine IsBigO.of_bound (‖H‖⁻¹) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hH), one_mul, ← norm_neg]; ring_nf; rfl
    exact this.pow n
  have hXt' : ∀ n : ℕ, (fun t => X t ^ n) =O[𝓝 t₀] fun t => (t - t₀) ^ n := by
    intro n
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by
      refine IsBigO.of_bound (‖H‖) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul, ← norm_neg (t₀ - t)]; ring_nf; rfl
    exact this.pow n
  have hEo : E =o[𝓝 t₀] fun t => X t ^ 3 := hT.trans_isBigO (htX 3)
  have hE0 : Tendsto E (𝓝 t₀) (𝓝 0) := by
    have : Tendsto (fun t => X t ^ 3) (𝓝 t₀) (𝓝 0) := by simpa using hXt.pow 3
    exact hEo.trans_tendsto this
  have hA : Continuous (A3 q j) := cont_A3 q j
  have hw1 : Tendsto (fun t => A3 q j (X t) + E t) (𝓝 t₀) (𝓝 1) := by
    have h := ((hA.tendsto 0).comp hXt).add hE0
    rwa [show A3 q j 0 + 0 = 1 by simp [A3]] at h
  have hwinv : (fun t => (A3 q j (X t) + E t)⁻¹) =O[𝓝 t₀] (fun _ => (1 : ℝ)) :=
    (hw1.inv₀ one_ne_zero).isBigO_one ℝ
  have hwE : ∀ t, a t / a₀ = A3 q j (X t) + E t := fun t => by simp only [hE]; ring
  set R : ℝ → ℝ := fun t => a₀ * H * comoving a t₀ t - P3 q (X t) with hR
  set R' : ℝ → ℝ := fun t => H * (B2 q (X t) - a₀ / a t) with hR'
  have hfc : ContinuousOn (fun s => 1 / a s) Bl := continuousOn_const.div hcont hnz
  have hderR : ∀ t ∈ Bl, HasDerivAt R (R' t) t := by
    intro t ht
    have hsub : Set.uIcc t t₀ ⊆ Bl := (convex_ball t₀ δ).ordConnected.uIcc_subset ht hmem
    have hχ : HasDerivAt (comoving a t₀) (-(1 / a t)) t :=
      intervalIntegral.integral_hasDerivAt_left ((hfc.mono hsub).intervalIntegrable)
        (hfc.stronglyMeasurableAtFilter hopen t ht) (hfc.continuousAt (hopen.mem_nhds ht))
    have hXd : HasDerivAt X (-H) t := by
      simpa using ((hasDerivAt_id t).const_sub t₀).const_mul H
    have hP := (hasDerivAt_P3 q (X t)).comp t hXd
    have := (hχ.const_mul (a₀ * H)).sub hP
    have e : R' t = a₀ * H * -(1 / a t) - B2 q (X t) * -H := by
      show H * (B2 q (X t) - a₀ / a t) = _
      field_simp; ring
    rw [e]; exact this
  have hR0 : R t₀ = 0 := by simp [hR, comoving, hX, P3]
  have hR'o : R' =o[𝓝 t₀] fun t => (t - t₀) ^ 2 := by
    have hC : Continuous (C3 q j) := cont_C3 q j
    have hB : Continuous (B2 q) := cont_B2 q
    have e1 : ∀ t ∈ Bl, R' t = H * ((X t ^ 3 * C3 q j (X t) + E t * B2 q (X t))
        * (A3 q j (X t) + E t)⁻¹) := by
      intro t ht
      have hw : A3 q j (X t) + E t ≠ 0 := by
        rw [← hwE]; exact div_ne_zero (hnz t ht) ha0
      have hab := idAB3 q j (X t)
      have ha' : a₀ / a t = (A3 q j (X t) + E t)⁻¹ := by rw [← hwE, inv_div]
      show H * (B2 q (X t) - a₀ / a t) = _
      rw [ha']
      exact alg2 H _ _ _ _ _ hw hab
    have b1 : (fun t => X t ^ 3 * C3 q j (X t)) =o[𝓝 t₀] fun t => X t ^ 2 :=
      pow_succ_mul_isLittleO hXt 2 _ (CCS.bdd hXt _ hC)
    have hX32 : (fun t => X t ^ 3) =o[𝓝 t₀] fun t => X t ^ 2 := by
      simpa using pow_succ_mul_isLittleO hXt 2 (fun _ => (1 : ℝ)) (isBigO_refl _ _)
    have b2 : (fun t => E t * B2 q (X t)) =o[𝓝 t₀] fun t => X t ^ 2 := by
      simpa using (hEo.trans hX32).mul_isBigO (CCS.bdd hXt _ hB)
    have b3 := (((b1.add b2).mul_isBigO hwinv).const_mul_left H)
    simp only [mul_one] at b3
    exact (b3.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => (e1 t ht).symm)
      EventuallyEq.rfl).trans_isBigO (hXt' 2)
  have hRo : R =o[𝓝 t₀] fun t => X t ^ 3 :=
    (littleO_of_hasDerivAt hR0 (Filter.eventually_of_mem hBl_nhds hderR) hR'o).trans_isBigO
      (htX 3)
  have n1 : (fun t => X t ^ 4 * W3 q j (X t)) =o[𝓝 t₀] fun t => X t ^ 3 :=
    pow_succ_mul_isLittleO hXt 3 _ (CCS.bdd hXt _ (cont_W3 q j))
  have n3 : (fun t => E t * Q3 q j (A3 q j (X t)) (E t)) =o[𝓝 t₀] fun t => X t ^ 3 := by
    simpa using hEo.mul_isBigO (bdd_Q3 q j _ ((hA.tendsto 0).comp hXt) hE0)
  have hN := (((n1.add hRo).sub n3).mul_isBigO hwinv)
  simp only [mul_one] at hN
  have e2 : ∀ t ∈ Bl, hubble a t₀ * lumDistFlat a t₀ t - seriesY (correctD2y q j 1) q (yred a t₀ t)
      = (X t ^ 4 * W3 q j (X t) + R t
      - E t * Q3 q j (A3 q j (X t)) (E t)) * (A3 q j (X t) + E t)⁻¹ := fun t ht =>
    final_alg q j a₀ (a t) H (comoving a t₀ t) (X t) (E t) ha0 (hnz t ht) (hwE t)
  have hfin := hN.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => (e2 t ht).symm)
    EventuallyEq.rfl
  have hy := hasDerivAt_yred a t₀ hd ha0
  have hy0 : yred a t₀ t₀ = 0 := by
    simp only [yred, redshift, ← ha₀, div_self ha0, sub_self, zero_div]
  have hXy : X =O[𝓝 t₀] fun t => yred a t₀ t := by
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by simpa using hXt' 1
    exact this.trans (sub_isBigO_of_hasDerivAt hy hy0 (neg_ne_zero.2 hH))
  exact hfin.trans_isBigO (hXy.pow 3)

/-- `t⁴ sin(1/t)` and its first two derivatives. -/
noncomputable def E0 (t : ℝ) : ℝ := osc (fun t => t ^ 4) (fun _ => 0) t
noncomputable def E1 (t : ℝ) : ℝ := osc (fun t => 4 * t ^ 3) (fun t => -t ^ 2) t
noncomputable def E2 (t : ℝ) : ℝ := osc (fun t => 12 * t ^ 2 - 1) (fun t => -6 * t) t

theorem E0_hasDerivAt (t : ℝ) : HasDerivAt E0 (E1 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun t => t ^ 2) (fun _ => 0) (by fun_prop) (by fun_prop)
    have e : E1 0 = 0 := by simp [E1, osc]
    rw [e]
    convert h using 1
    funext x; simp only [E0, osc]; ring
  · have h := osc_hasDerivAt (fun t => t ^ 4) (fun _ => 0) ht (hasDerivAt_pow 4 t)
      (hasDerivAt_const t 0)
    unfold E0
    convert h using 1
    simp only [E1, osc]; field_simp; ring

theorem E1_hasDerivAt (t : ℝ) : HasDerivAt E1 (E2 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun t => 4 * t) (fun _ => -1) (by fun_prop) (by fun_prop)
    have e : E2 0 = 0 := by simp [E2, osc]
    rw [e]
    convert h using 1
    funext x; simp only [E1, osc]; ring
  · have h := osc_hasDerivAt (fun t => 4 * t ^ 3) (fun t => -t ^ 2) ht
      ((hasDerivAt_pow 3 t).const_mul 4) ((hasDerivAt_pow 2 t).neg)
    unfold E1
    convert h using 1
    simp only [E2, osc]; field_simp; ring

/-- The witness scale factor `1 + t + (11/3) t³ + t⁴ sin(1/t)`. -/
noncomputable def V (t : ℝ) : ℝ := PQ 1 1 0 (11 / 3) 0 0 t + E0 t

theorem V_iter :
    iteratedDeriv 1 V = (fun t => PQ 1 0 11 0 0 0 t + E1 t) ∧
    iteratedDeriv 2 V = (fun t => PQ 0 22 0 0 0 0 t + E2 t) := by
  have d1 : iteratedDeriv 1 V = (fun t => PQ 1 0 11 0 0 0 t + E1 t) := by
    rw [iteratedDeriv_one]
    have := deriv_sum (fun t => PQ_hasDerivAt 1 1 0 (11 / 3) 0 0 t) E0_hasDerivAt
    have hV : V = fun t => PQ 1 1 0 (11 / 3) 0 0 t + E0 t := rfl
    rw [hV, this]; funext t; congr 1; simp only [PQ]; ring
  have d2 : iteratedDeriv 2 V = (fun t => PQ 0 22 0 0 0 0 t + E2 t) := by
    rw [iteratedDeriv_succ, d1]
    rw [deriv_sum (fun t => PQ_hasDerivAt 1 0 11 0 0 0 t) E1_hasDerivAt]
    funext t; congr 1; simp only [PQ]; ring
  exact ⟨d1, d2⟩

theorem V_iter3 : iteratedDeriv 3 V 0 = 0 := by
  rw [iteratedDeriv_succ, V_iter.2]
  apply deriv_zero_of_not_differentiableAt
  intro h
  apply osc_not_continuousAt (fun t => 12 * t ^ 2 - 1) (fun t => -6 * t) (by fun_prop) (by norm_num)
    (by norm_num)
  have hp : DifferentiableAt ℝ (PQ 0 22 0 0 0 0) 0 :=
    (PQ_smooth _ _ _ _ _ _ 1).differentiableAt (by norm_num)
  have := (h.sub hp).continuousAt
  convert this using 1
  funext t; simp [E2]

theorem V_zero : V 0 = 1 := by simp [V, E0, osc, PQ]

theorem V_d1 : deriv V 0 = 1 := by
  rw [← iteratedDeriv_one, V_iter.1]; simp [E1, osc, PQ]

theorem V_coeffs : hubble V 0 = 1 ∧ decel V 0 = 0 ∧ cosmoCoeff 3 V 0 = 0 := by
  have h2 : deriv (deriv V) 0 = 0 := by
    have e : deriv (deriv V) = iteratedDeriv 2 V := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [e, V_iter.2]; simp [E2, osc, PQ]
  refine ⟨unit_hubble V_zero V_d1, ?_, ?_⟩
  · rw [unit_decel V_zero V_d1, h2]; norm_num
  · rw [unit_coeff V_zero V_d1, V_iter3]

theorem V_taylor :
    (fun t => V t / V 0 - A3 0 22 (hubble V 0 * (0 - t))) =o[𝓝 0] fun t => (t - 0) ^ 3 := by
  have e : (fun t => V t / V 0 - A3 0 22 (hubble V 0 * (0 - t))) = E0 := by
    funext t; rw [V_zero, V_coeffs.1]; simp only [V, PQ, A3]; ring
  rw [e]
  have h4 : E0 =O[𝓝 0] fun t => t ^ 4 := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    simp only [E0, osc, Real.norm_eq_abs, zero_mul, add_zero, abs_mul, one_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  simpa using h4.trans_isLittleO (isLittleO_pow_pow (by norm_num : 3 < 4))

theorem V_cont : Continuous V := by
  have h : Differentiable ℝ V := fun t => ((PQ_hasDerivAt 1 1 0 (11 / 3) 0 0 t).add
    (E0_hasDerivAt t)).differentiableAt
  exact h.continuous

theorem V_diff : DifferentiableAt ℝ V 0 :=
  ((PQ_hasDerivAt 1 1 0 (11 / 3) 0 0 0).add (E0_hasDerivAt 0)).differentiableAt

end Y

/-- Smoothness (`C³` at `t₀`) is needed in the two-sided `BambaY.printedD2y_fails`:
`a = 1 + t + (11/3) t³ + t⁴ sin(1/t)` has `a(0) = 1`, `H₀ = 1`, `q₀ = 0`, two derivatives everywhere and a
second derivative not continuous at `0`, so Lean's junk third derivative gives `j₀ = 0` (`11 − 5q₀ + 3q₀² − j₀ =
11`); `a` agrees with the cubic's Taylor polynomial (`j₀ = 22`) to `o(t³)`, and the correct `D²` at `j₀ = 22`
equals the printed `D²` at `j₀ = 0`, so the printed flat `d_L(y)` series holds with remainder `o(y³)` on both
sides. -/
theorem printedD2y_fails_h1 : necessity% Checked.Cosmography.BambaY.printedD2y_fails 1 := by
  obtain ⟨hH, hq, hj⟩ := Y.V_coeffs
  refine ⟨Y.V, 0, by rw [Y.V_zero]; norm_num, by rw [hH]; norm_num, by rw [hq, hj]; norm_num, ?_⟩
  have hc := Y.core Y.V 0 0 22 Y.V_cont Y.V_diff (by rw [Y.V_zero]; norm_num) (by rw [hH]; norm_num)
    Y.V_taylor
  refine hc.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaY.remainderY, hH, hq, hj, BambaY.printedD2y, BambaY.correctD2y]
  norm_num

/-! ### `BambaK.printedD3y_fails`, `printedD4y_fails` (`d_L(y)` with curvature), and
`BambaA.printedDA3_fails`, `printedDA4_fails` (`d_A(y)`): the series theorems with the Taylor expansion as a
hypothesis -/

namespace K
open Checked.Cosmography.BambaY Checked.Cosmography.BambaK Checked.Cosmography.Transverse

/-- The proof of `BambaK.lumDist_y_fifth_order` from the point where it has the Taylor expansion, for free
coefficients `q j s l` and a continuous scale factor. -/
theorem core (K : ℝ) (a : ℝ → ℝ) (t₀ q j s l : ℝ) (hc : Continuous a) (hd : DifferentiableAt ℝ a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hT : (fun t => a t / a t₀ - CCS.Apoly q j s l (hubble a t₀ * (t₀ - t))) =o[𝓝 t₀]
      fun t => (t - t₀) ^ 5) :
    (fun t => hubble a t₀ * lumDist K a t₀ t - seriesY4 q (correctD2y q j (omega0 K a t₀))
      (correctD3y q j s (omega0 K a t₀)) (correctD4y q j s l (omega0 K a t₀)) (yred a t₀ t))
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 5) := by
  set a₀ := a t₀ with ha₀
  set H := hubble a t₀ with hHdef
  set k := K / (a₀ * H) ^ 2 with hk
  have hΩ : omega0 K a t₀ = 1 + k := by
    show 1 + K / (H ^ 2 * a₀ ^ 2) = 1 + K / (a₀ * H) ^ 2
    ring
  have hne : {t | a t ≠ 0} ∈ 𝓝 t₀ := hd.continuousAt.eventually_ne ha0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hne
  set Bl := Metric.ball t₀ δ with hBl
  have hopen : IsOpen Bl := Metric.isOpen_ball
  have hmem : t₀ ∈ Bl := Metric.mem_ball_self hδ
  have hBl_nhds : Bl ∈ 𝓝 t₀ := hopen.mem_nhds hmem
  have hnz : ∀ t ∈ Bl, a t ≠ 0 := fun t ht => hball ht
  have hcont : ContinuousOn a Bl := hc.continuousOn
  set X : ℝ → ℝ := fun t => H * (t₀ - t) with hX
  set E : ℝ → ℝ := fun t => a t / a₀ - CCS.Apoly q j s l (X t) with hE
  have hXc : Continuous X := by fun_prop
  have hXt : Tendsto X (𝓝 t₀) (𝓝 0) := by simpa [hX] using hXc.tendsto t₀
  have htX : ∀ n : ℕ, (fun t => (t - t₀) ^ n) =O[𝓝 t₀] fun t => X t ^ n := by
    intro n
    have : (fun t => t - t₀) =O[𝓝 t₀] X := by
      refine IsBigO.of_bound (‖H‖⁻¹) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hH), one_mul, ← norm_neg]; ring_nf; rfl
    exact this.pow n
  have hXt' : ∀ n : ℕ, (fun t => X t ^ n) =O[𝓝 t₀] fun t => (t - t₀) ^ n := by
    intro n
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by
      refine IsBigO.of_bound (‖H‖) (Eventually.of_forall fun t => ?_)
      simp only [hX, norm_mul, ← norm_neg (t₀ - t)]; ring_nf; rfl
    exact this.pow n
  have hEo : E =o[𝓝 t₀] fun t => X t ^ 5 := hT.trans_isBigO (htX 5)
  have hE0 : Tendsto E (𝓝 t₀) (𝓝 0) := by
    have : Tendsto (fun t => X t ^ 5) (𝓝 t₀) (𝓝 0) := by simpa using hXt.pow 5
    exact hEo.trans_tendsto this
  have hwE : ∀ t, a t / a₀ = CCS.Apoly q j s l (X t) + E t := fun t => by simp only [hE]; ring
  have hw1A : Tendsto (fun t => CCS.Apoly q j s l (X t) + E t) (𝓝 t₀) (𝓝 1) := by
    have h := (((cont_A q j s l).tendsto 0).comp hXt).add hE0
    rw [show CCS.Apoly q j s l 0 + 0 = 1 by simp [CCS.Apoly]] at h
    exact h
  have hwinvA : (fun t => (CCS.Apoly q j s l (X t) + E t)⁻¹) =O[𝓝 t₀] (fun _ => (1 : ℝ)) :=
    (hw1A.inv₀ one_ne_zero).isBigO_one ℝ
  have hw1 : Tendsto (fun t => a t / a₀) (𝓝 t₀) (𝓝 1) := hw1A.congr fun t => (hwE t).symm
  have hwinv : (fun t => (a t / a₀)⁻¹) =O[𝓝 t₀] (fun _ => (1 : ℝ)) :=
    (hw1.inv₀ one_ne_zero).isBigO_one ℝ
  -- comoving distance: u = a₀ H χ = P5(X) + o(X⁵)
  set u : ℝ → ℝ := fun t => a₀ * H * comoving a t₀ t with hu
  set R : ℝ → ℝ := fun t => u t - P5 q j s l k (X t) with hR
  set R' : ℝ → ℝ := fun t => H * (B4 q j s l k (X t) - a₀ / a t) with hR'
  have hfc : ContinuousOn (fun s => 1 / a s) Bl := continuousOn_const.div hcont hnz
  have hderR : ∀ t ∈ Bl, HasDerivAt R (R' t) t := by
    intro t ht
    have hsub : Set.uIcc t t₀ ⊆ Bl := (convex_ball t₀ δ).ordConnected.uIcc_subset ht hmem
    have hχ : HasDerivAt (comoving a t₀) (-(1 / a t)) t :=
      intervalIntegral.integral_hasDerivAt_left ((hfc.mono hsub).intervalIntegrable)
        (hfc.stronglyMeasurableAtFilter hopen t ht) (hfc.continuousAt (hopen.mem_nhds ht))
    have hXd : HasDerivAt X (-H) t := by
      simpa using ((hasDerivAt_id t).const_sub t₀).const_mul H
    have hP := (hasDerivAt_P5 q j s l k (X t)).comp t hXd
    have := (hχ.const_mul (a₀ * H)).sub hP
    have e : R' t = a₀ * H * -(1 / a t) - B4 q j s l k (X t) * -H := by
      show H * (B4 q j s l k (X t) - a₀ / a t) = _
      ring
    rw [e]; exact this
  have hR0 : R t₀ = 0 := by simp [hR, hu, comoving, hX, P5]
  have hR'o : R' =o[𝓝 t₀] fun t => (t - t₀) ^ 4 := by
    have e1 : ∀ t ∈ Bl, R' t = H * ((X t ^ 5 * C5 q j s l k (X t) + E t * B4 q j s l k (X t))
        * (CCS.Apoly q j s l (X t) + E t)⁻¹) := by
      intro t ht
      have hw : CCS.Apoly q j s l (X t) + E t ≠ 0 := by
        rw [← hwE]; exact div_ne_zero (hnz t ht) ha0
      have ha' : a₀ / a t = (CCS.Apoly q j s l (X t) + E t)⁻¹ := by rw [← hwE, inv_div]
      show H * (B4 q j s l k (X t) - a₀ / a t) = _
      rw [ha']
      exact alg5 H _ _ _ _ _ hw (idAB q j s l k (X t))
    have b1 : (fun t => X t ^ 5 * C5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 4 :=
      pow_succ_mul_isLittleO hXt 4 _ (CCS.bdd hXt _ (cont_C5 q j s l k))
    have hX54 : (fun t => X t ^ 5) =o[𝓝 t₀] fun t => X t ^ 4 := by
      simpa using pow_succ_mul_isLittleO hXt 4 (fun _ => (1 : ℝ)) (isBigO_refl _ _)
    have b2 : (fun t => E t * B4 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 4 := by
      simpa using (hEo.trans hX54).mul_isBigO (CCS.bdd hXt _ (cont_B4 q j s l k))
    have b3 := (((b1.add b2).mul_isBigO hwinvA).const_mul_left H)
    simp only [mul_one] at b3
    exact (b3.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => (e1 t ht).symm)
      EventuallyEq.rfl).trans_isBigO (hXt' 4)
  have hRo : R =o[𝓝 t₀] fun t => X t ^ 5 :=
    (littleO_of_hasDerivAt hR0 (Filter.eventually_of_mem hBl_nhds hderR) hR'o).trans_isBigO
      (htX 5)
  have au0 : (fun t => u t - P5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := hRo
  have au1 : (fun t => u t ^ 1 - P5 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    simpa only [pow_one] using au0
  have au2 := approx_pow (n := 1) hXt (cont_P5 q j s l k) (cont_P5 q j s l k)
    (cont_WM2 q j s l k) (idM2 q j s l k) au0 au1
  have au3 := approx_pow (n := 2) hXt (cont_P5 q j s l k) (cont_M2 q j s l k)
    (cont_WM3 q j s l k) (idM3 q j s l k) au0 au2
  have au4 := approx_pow (n := 3) hXt (cont_P5 q j s l k) (cont_M3 q j s l k)
    (cont_WM4 q j s l k) (idM4 q j s l k) au0 au3
  have au5 := approx_pow (n := 4) hXt (cont_P5 q j s l k) (cont_M4 q j s l k)
    (cont_WM5 q j s l k) (idM5 q j s l k) au0 au4
  -- χ = O(X), so the transverse expansion transfers
  have hX5X : (fun t => X t ^ 5) =O[𝓝 t₀] X := by
    have h := (isBigO_refl X (𝓝 t₀)).mul ((hXt.pow 4).isBigO_one ℝ)
    refine h.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
    · simp only; ring
    · simp
  have huX : u =O[𝓝 t₀] X := by
    have h1 : (fun t => P5 q j s l k (X t)) =O[𝓝 t₀] X := by
      have := (isBigO_refl X (𝓝 t₀)).mul (CCS.bdd hXt _ (cont_P5q q j s l k))
      refine this.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => ?_)
      · simp only [idP]
      · simp
    have h2 : R =O[𝓝 t₀] X := hRo.isBigO.trans hX5X
    refine (h2.add h1).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [hR]; ring
  have haH : a₀ * H ≠ 0 := mul_ne_zero ha0 hH
  have hχX : (fun t => comoving a t₀ t) =O[𝓝 t₀] X := by
    have := huX.const_mul_left (a₀ * H)⁻¹
    refine this.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [hu]; field_simp
  have hχ0 : Tendsto (fun t => comoving a t₀ t) (𝓝 t₀) (𝓝 0) := hχX.trans_tendsto hXt
  have hS := ((transverse_expansion K).comp_tendsto hχ0).const_mul_left (a₀ * H)
  have hS' := hS.trans_isBigO (hχX.pow 5)
  have aSig : (fun t => a₀ * H * transverse K (comoving a t₀ t) - Fpoly q j s l k (X t))
      =o[𝓝 t₀] fun t => X t ^ 5 := by
    have h := ((hS'.add au0).sub (au3.const_mul_left (k / 6))).add
      (au5.const_mul_left (k ^ 2 / 120))
    refine h.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [Function.comp, hu, Fpoly, hk]
    field_simp
    ring
  -- y = 1 − a/a₀ ≈ N1(X), and its powers
  have hyE : ∀ t ∈ Bl, yred a t₀ t = 1 - a t / a₀ := fun t ht => by
    have := hnz t ht
    simp only [yred, redshift, ← ha₀]
    field_simp
    linear_combination (a₀ - a t) * mul_inv_cancel₀ ha0
  have ay1 : (fun t => yred a t₀ t - N1 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    refine hEo.neg_left.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => ?_)
      EventuallyEq.rfl
    show -E t = yred a t₀ t - N1 q j s l k (X t)
    rw [hyE t ht]; simp only [hE, N1]; ring
  have ay1' : (fun t => yred a t₀ t ^ 1 - N1 q j s l k (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := by
    simpa only [pow_one] using ay1
  have ay2 := approx_pow (n := 1) hXt (cont_N1 q j s l k) (cont_N1 q j s l k)
    (cont_WN2 q j s l k) (idN2 q j s l k) ay1 ay1'
  have ay3 := approx_pow (n := 2) hXt (cont_N1 q j s l k) (cont_N2 q j s l k)
    (cont_WN3 q j s l k) (idN3 q j s l k) ay1 ay2
  have ay4 := approx_pow (n := 3) hXt (cont_N1 q j s l k) (cont_N3 q j s l k)
    (cont_WN4 q j s l k) (idN4 q j s l k) ay1 ay3
  have ay5 := approx_pow (n := 4) hXt (cont_N1 q j s l k) (cont_N4 q j s l k)
    (cont_WN5 q j s l k) (idN5 q j s l k) ay1 ay4
  have aS : (fun t => seriesY4 q (correctD2y q j (1 + k)) (correctD3y q j s (1 + k))
      (correctD4y q j s l (1 + k)) (yred a t₀ t) - Spoly q j s l k (X t))
      =o[𝓝 t₀] fun t => X t ^ 5 := by
    have h := ((((ay1.add (ay2.const_mul_left (D1y q))).add
      (ay3.const_mul_left (correctD2y q j (1 + k)))).add
      (ay4.const_mul_left (correctD3y q j s (1 + k)))).add
      (ay5.const_mul_left (correctD4y q j s l (1 + k))))
    refine h.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [seriesY4, Spoly]; ring
  have aw : (fun t => a t / a₀ - CCS.Apoly q j s l (X t)) =o[𝓝 t₀] fun t => X t ^ 5 := hEo
  have awS := approx_mul hXt (cont_A q j s l) (cont_Spoly q j s l k) (cont_Wf q j s l k)
    (idFin q j s l k) aw aS
  have hN := (aSig.sub awS).mul_isBigO hwinv
  simp only [mul_one] at hN
  have e2 : ∀ t ∈ Bl, hubble a t₀ * lumDist K a t₀ t - seriesY4 q (correctD2y q j (omega0 K a t₀))
      (correctD3y q j s (omega0 K a t₀)) (correctD4y q j s l (omega0 K a t₀)) (yred a t₀ t) =
      ((a₀ * H * transverse K (comoving a t₀ t) - Fpoly q j s l k (X t)) -
        (a t / a₀ * seriesY4 q (correctD2y q j (1 + k)) (correctD3y q j s (1 + k))
          (correctD4y q j s l (1 + k)) (yred a t₀ t) - Fpoly q j s l k (X t)))
        * (a t / a₀)⁻¹ := by
    intro t ht
    have := hnz t ht
    show H * (a₀ * (1 + (a₀ / a t - 1)) * transverse K (comoving a t₀ t)) -
      seriesY4 q (correctD2y q j (omega0 K a t₀)) (correctD3y q j s (omega0 K a t₀))
        (correctD4y q j s l (omega0 K a t₀)) (yred a t₀ t) = _
    rw [hΩ]
    field_simp
    ring
  have hfin := hN.congr' (Filter.eventually_of_mem hBl_nhds fun t ht => (e2 t ht).symm)
    EventuallyEq.rfl
  have hXy : X =O[𝓝 t₀] fun t => yred a t₀ t := by
    have : X =O[𝓝 t₀] (fun t => t - t₀) := by simpa using hXt' 1
    exact this.trans (sub_isBigO_yred a t₀ hd ha0 hH)
  exact hfin.trans_isBigO (hXy.pow 5)


end K

namespace KW
open Checked.Cosmography.BambaY Checked.Cosmography.BambaK Checked.Cosmography.BambaA

/-- The proof of `BambaA.angDist_y_fifth_order` from `K.core`, for free coefficients `q j s l`. -/
theorem coreA (K : ℝ) (a : ℝ → ℝ) (t₀ q j s l : ℝ) (hc : Continuous a) (hd : DifferentiableAt ℝ a t₀)
    (ha0 : a t₀ ≠ 0) (hH : hubble a t₀ ≠ 0)
    (hT : (fun t => a t / a t₀ - CCS.Apoly q j s l (hubble a t₀ * (t₀ - t))) =o[𝓝 t₀]
      fun t => (t - t₀) ^ 5) :
    (fun t => hubble a t₀ * angDist K a t₀ t -
      yred a t₀ t * (1 + DA1 q * yred a t₀ t + DA2 q j (omega0 K a t₀) * yred a t₀ t ^ 2
        + correctDA3 q j s (omega0 K a t₀) * yred a t₀ t ^ 3
        + correctDA4 q j s l (omega0 K a t₀) * yred a t₀ t ^ 4))
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 5) := by
  have hL := Checked.Trust.NecessityAH.K.core K a t₀ q j s l hc hd ha0 hH hT
  have hy0 := yred_tendsto a t₀ hd ha0
  have hne : ∀ᶠ t in 𝓝 t₀, a t ≠ 0 := hd.continuousAt.eventually_ne ha0
  have hb : (fun t => (1 - yred a t₀ t) ^ 2) =O[𝓝 t₀] (fun _ => (1 : ℝ)) :=
    ((hy0.const_sub 1).pow 2).isBigO_one ℝ
  have b1 := hb.mul_isLittleO hL
  simp only [one_mul] at b1
  have b2 : (fun t => yred a t₀ t ^ 6 * Vpoly q j s l (omega0 K a t₀) (yred a t₀ t))
      =o[𝓝 t₀] (fun t => yred a t₀ t ^ 5) :=
    pow_succ_mul_isLittleO hy0 5 _ (CCS.bdd hy0 _ (cont_V _ _ _ _ _))
  refine (b1.add b2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hne] with t ht
  have e3 : (1 - yred a t₀ t) ^ 2 = ((1 + redshift a t₀ t) ^ 2)⁻¹ := by
    have hw : 1 + redshift a t₀ t ≠ 0 := by
      simp only [redshift, add_sub_cancel]; exact div_ne_zero ha0 ht
    simp only [yred]; field_simp; ring
  have hid := idA q j s l (omega0 K a t₀) (yred a t₀ t)
  simp only [angDist]
  linear_combination (hubble a t₀ * lumDist K a t₀ t) * e3 - hid

/-- `t⁶ cos(1/t)` and its first three derivatives (`runs/2026-11-14T2228Z/scripts/eps_derivs.py`). -/
noncomputable def U0 (t : ℝ) : ℝ := osc (fun _ => 0) (fun t => t ^ 6) t
noncomputable def U1 (t : ℝ) : ℝ := osc (fun t => t ^ 4) (fun t => 6 * t ^ 5) t
noncomputable def U2 (t : ℝ) : ℝ := osc (fun t => 10 * t ^ 3) (fun t => 30 * t ^ 4 - t ^ 2) t
noncomputable def U3 (t : ℝ) : ℝ := osc (fun t => 60 * t ^ 2 - 1) (fun t => 120 * t ^ 3 - 12 * t) t

theorem U0_hasDerivAt (t : ℝ) : HasDerivAt U0 (U1 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun _ => 0) (fun t => t ^ 4) (by fun_prop) (by fun_prop)
    have e : U1 0 = 0 := by simp [U1, osc]
    rw [e]
    convert h using 1
    funext x; simp only [U0, osc]; ring
  · have h := osc_hasDerivAt (fun _ => 0) (fun t => t ^ 6) ht (hasDerivAt_const t 0)
      (hasDerivAt_pow 6 t)
    unfold U0
    convert h using 1
    simp only [U1, osc]; field_simp; ring

theorem U1_hasDerivAt (t : ℝ) : HasDerivAt U1 (U2 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun t => t ^ 2) (fun t => 6 * t ^ 3) (by fun_prop) (by fun_prop)
    have e : U2 0 = 0 := by simp [U2, osc]
    rw [e]
    convert h using 1
    funext x; simp only [U1, osc]; ring
  · have h := osc_hasDerivAt (fun t => t ^ 4) (fun t => 6 * t ^ 5) ht (hasDerivAt_pow 4 t)
      ((hasDerivAt_pow 5 t).const_mul 6)
    unfold U1
    convert h using 1
    simp only [U2, osc]; field_simp; ring

theorem U2_hasDerivAt (t : ℝ) : HasDerivAt U2 (U3 t) t := by
  by_cases ht : t = 0
  · subst ht
    have h := sq_osc_hasDerivAt_zero (fun t => 10 * t) (fun t => 30 * t ^ 2 - 1) (by fun_prop)
      (by fun_prop)
    have e : U3 0 = 0 := by simp [U3, osc]
    rw [e]
    convert h using 1
    funext x; simp only [U2, osc]; ring
  · have h := osc_hasDerivAt (fun t => 10 * t ^ 3) (fun t => 30 * t ^ 4 - t ^ 2) ht
      ((hasDerivAt_pow 3 t).const_mul 10) (((hasDerivAt_pow 4 t).const_mul 30).sub (hasDerivAt_pow 2 t))
    unfold U2
    convert h using 1
    simp only [U3, osc]; field_simp; ring

/-- The scale factor `1 + t + b t² + c t⁴ + t⁶ cos(1/t)`. -/
noncomputable def Ug (b c : ℝ) (t : ℝ) : ℝ := PQ 1 1 b 0 c 0 t + U0 t

theorem Ug_iter (b c : ℝ) :
    iteratedDeriv 1 (Ug b c) = (fun t => PQ 1 (2 * b) 0 (4 * c) 0 0 t + U1 t) ∧
    iteratedDeriv 2 (Ug b c) = (fun t => PQ (2 * b) 0 (12 * c) 0 0 0 t + U2 t) ∧
    iteratedDeriv 3 (Ug b c) = (fun t => PQ 0 (24 * c) 0 0 0 0 t + U3 t) := by
  have d1 : iteratedDeriv 1 (Ug b c) = (fun t => PQ 1 (2 * b) 0 (4 * c) 0 0 t + U1 t) := by
    rw [iteratedDeriv_one]
    have := deriv_sum (fun t => PQ_hasDerivAt 1 1 b 0 c 0 t) U0_hasDerivAt
    have hU : Ug b c = fun t => PQ 1 1 b 0 c 0 t + U0 t := rfl
    rw [hU, this]; funext t; congr 1; simp only [PQ]; ring
  have d2 : iteratedDeriv 2 (Ug b c) = (fun t => PQ (2 * b) 0 (12 * c) 0 0 0 t + U2 t) := by
    rw [iteratedDeriv_succ, d1]
    rw [deriv_sum (fun t => PQ_hasDerivAt 1 (2 * b) 0 (4 * c) 0 0 t) U1_hasDerivAt]
    funext t; congr 1; simp only [PQ]; ring
  have d3 : iteratedDeriv 3 (Ug b c) = (fun t => PQ 0 (24 * c) 0 0 0 0 t + U3 t) := by
    rw [iteratedDeriv_succ, d2]
    rw [deriv_sum (fun t => PQ_hasDerivAt (2 * b) 0 (12 * c) 0 0 0 t) U2_hasDerivAt]
    funext t; congr 1; simp only [PQ]; ring
  exact ⟨d1, d2, d3⟩

/-- Lean's fourth derivative of `Ug b c` at `0` is the junk value `0`. -/
theorem Ug_iter4 (b c : ℝ) : iteratedDeriv 4 (Ug b c) 0 = 0 := by
  rw [iteratedDeriv_succ, (Ug_iter b c).2.2]
  apply deriv_zero_of_not_differentiableAt
  intro h
  apply osc_not_continuousAt (fun t => 60 * t ^ 2 - 1) (fun t => 120 * t ^ 3 - 12 * t) (by fun_prop)
    (by norm_num) (by norm_num)
  have hp : DifferentiableAt ℝ (PQ 0 (24 * c) 0 0 0 0) 0 :=
    (PQ_smooth _ _ _ _ _ _ 1).differentiableAt (by norm_num)
  have := (h.sub hp).continuousAt
  convert this using 1
  funext t; simp [U3]

theorem Ug_zero (b c : ℝ) : Ug b c 0 = 1 := by simp [Ug, U0, osc, PQ]

theorem Ug_d1 (b c : ℝ) : deriv (Ug b c) 0 = 1 := by
  rw [← iteratedDeriv_one, (Ug_iter b c).1]; simp [U1, osc, PQ]

theorem Ug_coeffs (b c : ℝ) : hubble (Ug b c) 0 = 1 ∧ decel (Ug b c) 0 = -(2 * b) ∧
    cosmoCoeff 3 (Ug b c) 0 = 0 ∧ cosmoCoeff 4 (Ug b c) 0 = 0 := by
  have h2 : deriv (deriv (Ug b c)) 0 = 2 * b := by
    have e : deriv (deriv (Ug b c)) = iteratedDeriv 2 (Ug b c) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [e, (Ug_iter b c).2.1]; simp [U2, osc, PQ]
  refine ⟨unit_hubble (Ug_zero b c) (Ug_d1 b c), ?_, ?_, ?_⟩
  · rw [unit_decel (Ug_zero b c) (Ug_d1 b c), h2]
  · rw [unit_coeff (Ug_zero b c) (Ug_d1 b c), (Ug_iter b c).2.2]; simp [U3, osc, PQ]
  · rw [unit_coeff (Ug_zero b c) (Ug_d1 b c), Ug_iter4]

/-- `Ug b c` agrees with its quartic's Taylor polynomial (`q₀ = −2b`, `j₀ = 0`, `s₀ = 24 c`, `l₀ = 0`) up to
`o(t⁵)`. -/
theorem Ug_taylor (b c : ℝ) :
    (fun t => Ug b c t / Ug b c 0 - CCS.Apoly (-(2 * b)) 0 (24 * c) 0 (hubble (Ug b c) 0 * (0 - t)))
      =o[𝓝 0] fun t => (t - 0) ^ 5 := by
  have e : (fun t => Ug b c t / Ug b c 0 -
      CCS.Apoly (-(2 * b)) 0 (24 * c) 0 (hubble (Ug b c) 0 * (0 - t))) = U0 := by
    funext t; rw [Ug_zero, (Ug_coeffs b c).1]; simp only [Ug, PQ, CCS.Apoly]; ring
  rw [e]
  have h6 : U0 =O[𝓝 0] fun t => t ^ 6 := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    simp only [U0, osc, Real.norm_eq_abs, zero_mul, zero_add, abs_mul, one_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  simpa using h6.trans_isLittleO (isLittleO_pow_pow (by norm_num : 5 < 6))

theorem Ug_diff (b c : ℝ) : Differentiable ℝ (Ug b c) := fun t =>
  ((PQ_hasDerivAt 1 1 b 0 c 0 t).add (U0_hasDerivAt t)).differentiableAt

theorem y54 {a : ℝ → ℝ} (hd : DifferentiableAt ℝ a 0) (ha0 : a 0 ≠ 0) :
    (fun t => yred a 0 t ^ 5) =o[𝓝 0] (fun t => yred a 0 t ^ 4) := by
  simpa using pow_succ_mul_isLittleO (yred_tendsto a 0 hd ha0) 4 (fun _ => (1 : ℝ)) (isBigO_refl _ _)

end KW

/-- Smoothness (`C⁵` at `t₀`) is needed in the two-sided `BambaK.printedD3y_fails`: with `K = 1`,
`a = 1 + t + t⁴/3 + t⁶ cos(1/t)` has `a(0) = 1`, `H₀ = 1`, `q₀ = 0`, `Ω₀ = 2` (so `(Ω₀ − 1)(3q₀ − 2) = −2`),
three derivatives everywhere and a third derivative not continuous at `0`, so Lean's junk fourth derivative
gives `s₀ = 0`; `a` agrees with the quartic's Taylor polynomial (`s₀ = 8`) to `o(t⁵)`, and the correct `D³` at
`s₀ = 8` equals the printed `D³` at `s₀ = 0`, so the series with the printed `D³` holds with remainder
`o(y⁴)` on both sides. -/
theorem printedD3y_fails_h1 : necessity% Checked.Cosmography.BambaK.printedD3y_fails 1 := by
  obtain ⟨hH, hq, hj, hs⟩ := KW.Ug_coeffs 0 (1 / 3)
  have hΩ : BambaK.omega0 1 (KW.Ug 0 (1 / 3)) 0 = 2 := by
    rw [unit_omega0 (KW.Ug_zero _ _) (KW.Ug_d1 _ _)]; norm_num
  refine ⟨1, KW.Ug 0 (1 / 3), 0, by rw [KW.Ug_zero]; norm_num, by rw [hH]; norm_num,
    by rw [hΩ, hq]; norm_num, ?_⟩
  have hd := KW.Ug_diff 0 (1 / 3) 0
  have ha0 : KW.Ug 0 (1 / 3) 0 ≠ 0 := by rw [KW.Ug_zero]; norm_num
  have hc := (K.core 1 (KW.Ug 0 (1 / 3)) 0 (-(2 * 0)) 0 (24 * (1 / 3)) 0 (KW.Ug_diff _ _).continuous hd
    ha0 (by rw [hH]; norm_num) (KW.Ug_taylor _ _)).trans (KW.y54 hd ha0)
  have h5 := (KW.y54 hd ha0).const_mul_left
    (BambaK.correctD4y (-(2 * 0)) 0 (24 * (1 / 3)) 0 (BambaK.omega0 1 (KW.Ug 0 (1 / 3)) 0))
  refine (hc.add h5).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaK.remK, BambaK.seriesY4, hH, hq, hj, hs, hΩ, BambaK.printedD3y, BambaK.correctD3y]
  ring

/-- Smoothness (`C⁵` at `t₀`) is needed in the two-sided `BambaK.printedD4y_fails`: with `K = 1`,
`a = 1 + t + t⁵/120 + t⁸ sin(1/t)` has `a(0) = 1`, `H₀ = 1`, `q₀ = 0`, `Ω₀ = 2` (so
`(Ω₀ − 1)²/120 + 5q₀(Ω₀ − 1)/12 = 1/120`), four derivatives everywhere and a fourth derivative not continuous at
`0`, so Lean's junk fifth derivative gives `l₀ = 0`; `a` agrees with the quintic's Taylor polynomial
(`l₀ = 1`) to `o(t⁵)`, and the correct `D⁴` at `l₀ = 1` equals the printed `D⁴` at `l₀ = 0`, so the series
with the printed `D⁴` holds with remainder `o(y⁵)` on both sides. -/
theorem printedD4y_fails_h1 : necessity% Checked.Cosmography.BambaK.printedD4y_fails 1 := by
  obtain ⟨hH, hq, hj, hs, hl⟩ := W_coeffs 0 (1 / 120)
  have hΩ : BambaK.omega0 1 (W 0 (1 / 120)) 0 = 2 := by
    rw [unit_omega0 (W_zero _ _) (W_d1 _ _)]; norm_num
  refine ⟨1, W 0 (1 / 120), 0, by rw [W_zero]; norm_num, by rw [hH]; norm_num,
    by rw [hΩ, hq]; norm_num, ?_⟩
  have hc := K.core 1 (W 0 (1 / 120)) 0 (-(2 * 0)) 0 0 (120 * (1 / 120)) (W_diff _ _).continuous
    (W_diff _ _ 0) (by rw [W_zero]; norm_num) (by rw [hH]; norm_num) (W_taylor _ _)
  refine hc.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaK.remK, hH, hq, hj, hs, hl, hΩ, BambaK.correctD4y, BambaK.correctD3y,
    BambaK.printedD4y, BambaK.printedD3y]
  ring_nf

/-- Smoothness (`C⁵` at `t₀`) is needed in the two-sided `BambaA.printedDA3_fails`: with `K = 1`,
`a = 1 + t − t²/2 − t⁴/4 + t⁶ cos(1/t)` has `a(0) = 1`, `H₀ = 1`, `q₀ = 1`, `Ω₀ = 2`, three derivatives
everywhere and a third derivative not continuous at `0`, so Lean's junk fourth derivative gives `s₀ = 0`; `a`
agrees with the quartic's Taylor polynomial (`s₀ = −6`) to `o(t⁵)`, and the correct `D³_A` at `s₀ = −6` equals
the printed `D³_A` at `s₀ = 0`, so the `d_A(y)` series with the printed `D³_A` holds with remainder `o(y⁴)` on
both sides. -/
theorem printedDA3_fails_h1 : necessity% Checked.Cosmography.BambaA.printedDA3_fails 1 := by
  obtain ⟨hH, hq, hj, hs⟩ := KW.Ug_coeffs (-1 / 2) (-1 / 4)
  have hΩ : BambaK.omega0 1 (KW.Ug (-1 / 2) (-1 / 4)) 0 = 2 := by
    rw [unit_omega0 (KW.Ug_zero _ _) (KW.Ug_d1 _ _)]; norm_num
  refine ⟨1, KW.Ug (-1 / 2) (-1 / 4), 0, by rw [KW.Ug_zero]; norm_num, by rw [hH]; norm_num,
    by rw [hΩ, hq]; norm_num, ?_⟩
  have hd := KW.Ug_diff (-1 / 2) (-1 / 4) 0
  have ha0 : KW.Ug (-1 / 2) (-1 / 4) 0 ≠ 0 := by rw [KW.Ug_zero]; norm_num
  have hc := (KW.coreA 1 (KW.Ug (-1 / 2) (-1 / 4)) 0 (-(2 * (-1 / 2))) 0 (24 * (-1 / 4)) 0
    (KW.Ug_diff _ _).continuous hd ha0 (by rw [hH]; norm_num) (KW.Ug_taylor _ _)).trans (KW.y54 hd ha0)
  have h5 := (KW.y54 hd ha0).const_mul_left
    (BambaA.correctDA4 (-(2 * (-1 / 2))) 0 (24 * (-1 / 4)) 0
      (BambaK.omega0 1 (KW.Ug (-1 / 2) (-1 / 4)) 0))
  refine (hc.add h5).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaA.remA, hH, hq, hj, hs, hΩ, BambaA.printedDA3, BambaA.correctDA3]
  ring

/-- Smoothness (`C⁵` at `t₀`) is needed in the two-sided `BambaA.printedDA4_fails`: with `K = 1`,
`a = 1 + t + t⁵/120 + t⁸ sin(1/t)` has `a(0) = 1`, `H₀ = 1`, `q₀ = 0`, `j₀ = 0`, `Ω₀ = 2` (so
`(Ω₀ − 1)[(Ω₀ − 1) + 10j₀ − 45q₀² + 20q₀] = 1`), and Lean's junk fifth derivative gives `l₀ = 0`; `a` agrees with
the quintic's Taylor polynomial (`l₀ = 1`) to `o(t⁵)`, and the correct `D⁴_A` at `l₀ = 1` equals the printed
`D⁴_A` at `l₀ = 0`, so the `d_A(y)` series with the printed `D⁴_A` holds with remainder `o(y⁵)` on both
sides. -/
theorem printedDA4_fails_h1 : necessity% Checked.Cosmography.BambaA.printedDA4_fails 1 := by
  obtain ⟨hH, hq, hj, hs, hl⟩ := W_coeffs 0 (1 / 120)
  have hΩ : BambaK.omega0 1 (W 0 (1 / 120)) 0 = 2 := by
    rw [unit_omega0 (W_zero _ _) (W_d1 _ _)]; norm_num
  refine ⟨1, W 0 (1 / 120), 0, by rw [W_zero]; norm_num, by rw [hH]; norm_num,
    by rw [hΩ, hq, hj]; norm_num, ?_⟩
  have hc := KW.coreA 1 (W 0 (1 / 120)) 0 (-(2 * 0)) 0 0 (120 * (1 / 120)) (W_diff _ _).continuous
    (W_diff _ _ 0) (by rw [W_zero]; norm_num) (by rw [hH]; norm_num) (W_taylor _ _)
  refine hc.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  simp only [BambaA.remA, hH, hq, hj, hs, hl, hΩ, BambaA.correctDA4, BambaA.correctDA3,
    BambaA.printedDA4, BambaA.printedDA3]
  ring

end Checked.Trust.NecessityAH
