import Checked.Fidelity.MoreSpecs
import Work.Fidelity.RedTeamMore
import Work.Fidelity.RedTeamLumDistCheck

/-!
# Blind mutation benchmark for `HubbleSpec`, `DecelSpec`, `AngDistSpec`, `FlatLCDMSpec`

Protocol (trust track T1): the specifications (`MoreSpecs.lean`) were written by one subagent
that never saw the mutants; the mutants (`RedTeamMore.lean`) by another that never saw the
specifications; both files were frozen in commit b68bff5 before any refutation was attempted.
Each `reject_*` below is a Lean proof that a mutant violates the specification.

Not counted as mutants (equal to the true definition on the physical domain the brief fixed):
`rq4` (differs only where ȧ = 0, where q is undefined and the specification deliberately leaves
it free) and `ra5` (differs only for t > t₀, outside the brief's admissible inputs t < t₀).
-/

namespace Work.Fidelity

open Checked.Fidelity

open Real Filter Topology Checked.Cosmography Checked.Cosmography.BambaY
open Checked.Cosmography.Transverse Checked.Cosmography.BambaK Checked.Cosmography.BambaA
open Checked.Cosmography.Aviles Work.Fidelity.RedTeamMore

lemma rt_deriv_expMul (h : ℝ) : deriv (fun s => Real.exp (h * s)) = fun s => h * Real.exp (h * s) := by
  funext s; exact (ms_hasDerivAt_expMul h s).deriv

lemma rt_deriv2_expMul (h t : ℝ) :
    deriv (deriv (fun s => Real.exp (h * s))) t = h * (h * Real.exp (h * t)) := by
  rw [rt_deriv_expMul]; exact ((ms_hasDerivAt_expMul h t).const_mul h).deriv

lemma one_lt_exp_one : 1 < Real.exp 1 := by
  have := Real.exp_one_gt_d9; norm_num at this; linarith

/-! ## Hubble rate -/

theorem reject_rh1 : ¬ HubbleSpec rh1 := fun h => by
  have e := h.deSitter 1 1
  have hd : deriv (fun s => Real.exp (1 * s) ^ 2) 1 = 2 * Real.exp 1 * Real.exp 1 := by
    rw [((ms_hasDerivAt_expMul 1 1).fun_pow 2).deriv]; simp
  simp only [rh1, hd] at e
  have h0 := (Real.exp_pos 1).ne'
  simp at e

theorem reject_rh2 : ¬ HubbleSpec rh2 := fun h => by
  have e := h.deSitter 2 0
  have hd : deriv (fun s => Real.log (Real.exp (2 * s))) 0 = 2 := by
    simp only [Real.log_exp]
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul 2).deriv
  simp only [rh2, hd] at e
  norm_num at e

theorem reject_rh3 : ¬ HubbleSpec rh3 := fun h => by
  have e := h.deSitter 1 1
  simp only [rh3, rt_deriv_expMul] at e
  simp at e
  have h0 := (Real.exp_pos 1).ne'
  field_simp at e
  have := Real.exp_injective e
  norm_num at this

theorem reject_rh4 : ¬ HubbleSpec rh4 := fun h => by
  have e := h.deSitter (-1) 0
  simp only [rh4, rt_deriv_expMul] at e
  norm_num at e

theorem reject_rh5 : ¬ HubbleSpec rh5 := fun h => by
  have e := h.deSitter (-1) 0
  simp only [rh5, rt_deriv2_expMul] at e
  norm_num at e

/-! ## Deceleration parameter -/

theorem reject_rq1 : ¬ DecelSpec rq1 := fun h => by
  have e := h.deSitter 1 1 one_ne_zero
  simp only [rq1] at e
  rw [rt_deriv2_expMul, rt_deriv_expMul] at e
  have h0 := (Real.exp_pos 1).ne'
  simp at e
  field_simp at e
  have h3 := (Real.exp_eq_one_iff (2 : ℝ)).1 (by linarith)
  norm_num at h3

theorem reject_rq5 : ¬ DecelSpec rq5 := fun h => by
  have e := h.deSitter 2 0 two_ne_zero
  simp only [rq5] at e
  rw [rt_deriv2_expMul, rt_deriv_expMul] at e
  norm_num at e

/-- `a = t²` at `t = 1`: the specification's `formula` anchor forces `q = −1/2`. -/
lemma sq_decel_at (Q : (ℝ → ℝ) → ℝ → ℝ) (h : DecelSpec Q) : Q (fun s => s ^ 2) 1 = -1 / 2 := by
  have := h.formula (fun s => s ^ 2) (fun s => 2 * s) 2 1
    (Eventually.of_forall fun s => by simpa using hasDerivAt_pow 2 s)
    (by simpa using (hasDerivAt_id' (1 : ℝ)).const_mul 2) (by norm_num) (by norm_num)
  rw [this]; norm_num

lemma deriv_sq_fun : deriv (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
  funext s; simp

lemma hubble_sq_deriv_at_one : deriv (fun s : ℝ => 2 * s / s ^ 2) 1 = -2 := by
  have := ((hasDerivAt_id' (1 : ℝ)).const_mul 2).fun_div (hasDerivAt_pow 2 (1 : ℝ)) (by norm_num)
  rw [this.deriv]; norm_num

theorem reject_rq2 : ¬ DecelSpec rq2 := fun h => by
  have e := sq_decel_at _ h
  simp only [rq2, deriv_sq_fun] at e
  rw [hubble_sq_deriv_at_one] at e
  norm_num at e

theorem reject_rq3 : ¬ DecelSpec rq3 := fun h => by
  have e := sq_decel_at _ h
  simp only [rq3, deriv_sq_fun] at e
  rw [hubble_sq_deriv_at_one] at e
  norm_num at e

/-! ## Angular-diameter distance -/

lemma lumDist_deSitter_at : lumDist 0 Real.exp 0 (-Real.log 2) = 2 := by
  rw [lumDist_meets_spec.deSitter _ (by linarith [Real.log_pos one_lt_two]), exp_neg_negLog2]
  norm_num

theorem reject_ra1 : ¬ AngDistSpec ra1 := fun h => by
  have e := h.deSitter _ (by linarith [Real.log_pos one_lt_two] : -Real.log 2 ≤ 0)
  simp only [ra1, lumDist_deSitter_at, red_exp, Real.exp_neg, Real.exp_log two_pos] at e
  norm_num at e

theorem reject_ra2 : ¬ AngDistSpec ra2 := fun h => by
  have e := h.rescale 2 two_pos 0 Real.exp 0 (-Real.log 2)
  simp only [ra2, mul_zero, transverse, lt_irrefl, ite_false, comoving_rescale 2 two_pos,
    redshift_rescale 2 two_pos, com_exp, red_exp] at e
  norm_num at e

theorem reject_ra3 : ¬ AngDistSpec ra3 := fun h => by
  have e := h.staticClosed 1 one_pos 1 0 zero_le_one
  simp [ra3, lumDist, transverse, comoving_one, redshift] at e
  have h1 := Real.sin_lt one_pos
  have h2 := (Real.self_lt_sinh_iff (x := 1)).2 one_pos
  norm_num at e
  linarith

theorem reject_ra4 : ¬ AngDistSpec ra4 := fun h => by
  have e := h.staticClosed 2 two_pos π 0 pi_pos.le
  have hs : Real.sqrt (1 * 2 ^ 2 : ℝ) = 2 := by
    rw [one_mul, Real.sqrt_sq (by norm_num)]
  simp only [ra4, transverse, com_const2, hs] at e
  norm_num at e
  rw [show 2 * (π / 2) = π by ring, Real.sin_pi] at e
  norm_num at e

/-! ## Flat ΛCDM predicate -/

theorem reject_rL1 : ¬ FlatLCDMSpec rL1 := fun h => by
  apply h.contracting 0 1 0 one_pos
  refine Eventually.of_forall fun t => ⟨Real.exp_pos _, ?_, ?_⟩
  · exact (ms_hasDerivAt_expMul (-1) t).differentiableAt
  · rw [ms_hubble_expMul, ms_hubble_expMul]; simp

theorem reject_rL5 : ¬ FlatLCDMSpec rL5 := fun h => by
  have := (h.deSitter 2 0 two_pos).2.self_of_nhds
  rw [ms_hubble_expMul] at this
  norm_num at this

/-- The piecewise model `eᵗ` (t ≤ 0), `1 + t` (t > 0): differentiable at 0 with `ȧ = 1`. -/
noncomputable def pw (t : ℝ) : ℝ := if t ≤ 0 then Real.exp t else 1 + t

lemma pw_hasDerivAt_zero : HasDerivAt pw 1 0 := by
  have h1 : HasDerivWithinAt pw 1 (Set.Iic 0) 0 := by
    have := (Real.hasDerivAt_exp 0).hasDerivWithinAt (s := Set.Iic 0)
    rw [Real.exp_zero] at this
    exact this.congr (fun x hx => by simp [pw, Set.mem_Iic.1 hx]) (by simp [pw])
  have h2 : HasDerivWithinAt pw 1 (Set.Ici 0) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).const_add 1).hasDerivWithinAt (s := Set.Ici 0)
    refine this.congr (fun x hx => ?_) (by simp [pw])
    rcases (Set.mem_Ici.1 hx).lt_or_eq with hx | hx
    · simp [pw, not_le.2 hx]
    · subst hx; simp [pw]
  have := h1.union h2
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this

lemma pw_hubble_zero : hubble pw 0 = 1 := by
  simp [hubble, pw_hasDerivAt_zero.deriv, pw]

lemma pw_past : ∀ᶠ t in 𝓝[<] (0 : ℝ), 0 < pw t ∧ DifferentiableAt ℝ pw t ∧
    hubble pw t = hubble pw 0 * √((0 : ℝ) * (1 + redshift pw 0 t) ^ 3 + 1 - 0) := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hev : pw =ᶠ[𝓝 t] Real.exp := by
    filter_upwards [gt_mem_nhds (Set.mem_Iio.1 ht)] with s hs; simp [pw, hs.le]
  refine ⟨by simp [pw, (Set.mem_Iio.1 ht).le, Real.exp_pos], ?_, ?_⟩
  · exact (Real.differentiableAt_exp).congr_of_eventuallyEq hev
  · rw [ms_hubble_eventually hev, ms_hubble_exp, pw_hubble_zero]; simp

lemma pw_eq : (fun t => if t ≤ 0 then Real.exp t else 1 + t) = pw := rfl

theorem reject_rL3 : ¬ FlatLCDMSpec rL3 := fun h => by
  apply h.notPastOnly
  rw [pw_eq]
  exact ⟨by rw [pw_hubble_zero]; norm_num, pw_past⟩

theorem reject_rL2 : ¬ FlatLCDMSpec rL2 := fun h => by
  apply h.notPastOnly
  rw [pw_eq]
  refine ⟨by rw [pw_hubble_zero]; norm_num, ?_⟩
  exact (pw_past.frequently).filter_mono nhdsWithin_le_nhds

end Work.Fidelity

namespace Work.Fidelity

open Checked.Fidelity

open Real Filter Topology Checked.Cosmography Work.Fidelity.RedTeamMore

/-- The precedence slip `Ω(1 + z³)` fails in Einstein–de Sitter: for every `t > 1` the mutant's
equation would force `1 = u⁶ + (1 − u²)³` with `u = t^{1/3} > 1`, i.e. `3u⁴(u² − 1) = 0`. -/
theorem reject_rL4 : ¬ FlatLCDMSpec rL4 := fun h => by
  have hE := (h.eds 1 one_pos).2
  obtain ⟨t, ht, -, -, he⟩ := hE.exists_gt
  have ht0 : 0 < t := by linarith
  rw [hubble_meets_spec.powerLaw _ _ ht0, hubble_meets_spec.powerLaw _ _ one_pos] at he
  simp only [redshift, Real.one_rpow] at he
  set u := t ^ (1 / 3 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht0 _
  have htu : t = u ^ 3 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have h23 : t ^ (2 / 3 : ℝ) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hu1 : 1 < u := by
    by_contra hc; push_neg at hc
    have : u ^ 3 ≤ 1 := pow_le_one₀ hu0.le hc
    linarith
  rw [h23, htu] at he
  set w := 1 / u ^ 2 - 1 with hw
  have hw1 : -1 < w := by have : 0 < 1 / u ^ 2 := by positivity
                          linarith
  have hw0 : w ≤ 0 := by
    have : 1 / u ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hb : 0 ≤ 1 * (1 + w ^ 3) + 1 - 1 := by
    nlinarith [mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hw0 (by linarith : w - 1 ≤ 0))
      (by linarith : (0:ℝ) ≤ w + 1)]
  have hsq := congrArg (· ^ 2) he
  simp only [mul_pow, Real.sq_sqrt hb] at hsq
  have hu2 : u ^ 2 ≠ 0 := by positivity
  rw [hw] at hsq
  field_simp at hsq
  nlinarith [mul_pos (mul_pos hu0 hu0) (sub_pos.2 hu1), pow_pos hu0 4]

end Work.Fidelity
