import Checked.Cosmography.Lookback

/-!
# Fidelity audit tests for `Checked.Cosmography.lookback_second_order` (annex XL, 40.3)

* not vacuous: de Sitter `a = exp` and power law `a = t²` satisfy every hypothesis;
* definitions bite on examples: `H`, `q` take their textbook values there;
* near-miss 1: dropping `a'(t₀) ≠ 0` makes the conclusion false (static `a = 1`);
* near-miss 2: any other second-order coefficient fails (shown for de Sitter);
* blind restatement: its deceleration parameter `-(a''/a) H⁻²` equals ours.
-/

namespace Work.CosmographyAudit

open Filter Asymptotics Topology Checked.Cosmography

/-! ### Definitions on examples -/

lemma hubble_exp : hubble Real.exp 0 = 1 := by simp [hubble, Real.deriv_exp]

lemma decel_exp : decel Real.exp 0 = -1 := by
  simp [decel, Real.deriv_exp]

lemma hubble_sq : hubble (fun t : ℝ => t ^ 2) 1 = 2 := by
  have : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t; simp
  simp [hubble]

lemma decel_sq : decel (fun t : ℝ => t ^ 2) 1 = -1 / 2 := by
  have h1 : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t; simp
  have h2 : deriv (fun t : ℝ => 2 * t) = fun _ => 2 := by
    funext t; simp
  simp only [decel, h1, h2]; norm_num

/-! ### Not vacuous: the hypotheses hold for de Sitter and for `a = t²` -/

example := lookback_second_order Real.exp 0
  (Eventually.of_forall fun t => Real.differentiableAt_exp)
  (by simp [Real.deriv_exp])
  (Real.exp_pos 0).ne' (by simp [Real.deriv_exp])

example := lookback_second_order (fun t : ℝ => t ^ 2) 1
  (Eventually.of_forall fun t => by fun_prop)
  (by
    have h1 : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by funext t; simp
    rw [h1]; fun_prop)
  (by norm_num) (by simp)

/-- The de Sitter instance spelled out: `-t - (z - z²/2) = o(z²)` with `z = e^{-t} - 1`,
i.e. the second-order Taylor coefficient of `log (1 + z)`. -/
lemma lookback_deSitter :
    (fun t : ℝ => -t - ((Real.exp 0 / Real.exp t - 1) - (1 / 2) * (Real.exp 0 / Real.exp t - 1) ^ 2))
      =o[𝓝 0] (fun t => (Real.exp 0 / Real.exp t - 1) ^ 2) := by
  have h := lookback_second_order Real.exp 0
    (Eventually.of_forall fun t => Real.differentiableAt_exp)
    (by simp [Real.deriv_exp])
    (Real.exp_pos 0).ne' (by simp [Real.deriv_exp])
  rw [hubble_exp, decel_exp] at h
  simp only [redshift] at h
  convert h using 2 with t
  ring

/-! ### Near-miss 1: without `a'(t₀) ≠ 0` the statement is false -/

lemma nearMiss_static :
    ¬ (fun t : ℝ => (0 - t) - (redshift (fun _ => 1) 0 t
        - (1 + decel (fun _ => 1) 0 / 2) * redshift (fun _ => 1) 0 t ^ 2)
        / hubble (fun _ => 1) 0)
      =o[𝓝 0] (fun t => redshift (fun _ => (1:ℝ)) 0 t ^ 2) := by
  intro h
  have h0 : (fun t : ℝ => redshift (fun _ => (1:ℝ)) 0 t ^ 2) = fun _ => 0 := by
    funext t; simp [redshift]
  rw [h0, isLittleO_zero_right_iff] at h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h
  have := hball (y := ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  simp [redshift, hubble] at this
  linarith

/-! ### Near-miss 2: the coefficient `1 + q₀/2` is the only one that works -/

/-- If `c • g = o(g)` and `g` is not eventually zero, then `c = 0`. -/
lemma coeff_eq_zero_of_isLittleO {g : ℝ → ℝ} {l : Filter ℝ} {c : ℝ}
    (h : (fun t => c * g t) =o[l] g) (hg : ∃ᶠ t in l, g t ≠ 0) : c = 0 := by
  by_contra hc
  have hc' : 0 < |c| / 2 := by positivity
  have := h.def hc'
  apply hg
  filter_upwards [this] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul] at ht
  have : |g t| = 0 := by
    by_contra hne
    have hpos : 0 < |g t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    nlinarith [abs_pos.2 hc]
  exact not_not.2 (abs_eq_zero.1 this)

lemma deSitter_redshift_frequently :
    ∃ᶠ t in 𝓝 (0:ℝ), (Real.exp 0 / Real.exp t - 1) ^ 2 ≠ 0 := by
  rw [Filter.Frequently]
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h
  have := hball (y := ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  simp only [Real.exp_zero, ne_eq, not_not, pow_eq_zero_iff two_ne_zero, sub_eq_zero,
    one_div] at this
  rw [inv_eq_one, Real.exp_eq_one_iff] at this
  linarith

/-- For de Sitter, replacing the coefficient `1/2` by any `k ≠ 1/2` makes the statement false. -/
lemma nearMiss_wrong_coefficient (k : ℝ) (hk : k ≠ 1 / 2) :
    ¬ (fun t : ℝ => -t - ((Real.exp 0 / Real.exp t - 1) - k * (Real.exp 0 / Real.exp t - 1) ^ 2))
      =o[𝓝 0] (fun t => (Real.exp 0 / Real.exp t - 1) ^ 2) := by
  intro h
  have hsub := h.sub lookback_deSitter
  have hc : (fun t : ℝ => (k - 1 / 2) * (Real.exp 0 / Real.exp t - 1) ^ 2)
      =o[𝓝 0] (fun t => (Real.exp 0 / Real.exp t - 1) ^ 2) := by
    refine hsub.congr_left fun t => ?_
    ring
  have := coeff_eq_zero_of_isLittleO hc deSitter_redshift_frequently
  exact hk (by linarith)

/-! ### Blind restatement: its deceleration parameter agrees with ours -/

lemma decel_eq_blind (a : ℝ → ℝ) (t : ℝ) (ha : a t ≠ 0) (hd : deriv a t ≠ 0) :
    decel a t = -(deriv (deriv a) t / a t) * (hubble a t)⁻¹ ^ 2 := by
  simp only [decel, hubble]
  field_simp

end Work.CosmographyAudit
