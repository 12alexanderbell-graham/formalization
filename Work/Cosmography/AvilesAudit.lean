import Work.Cosmography.AvilesLCDM

/-!
# Fidelity audit of C2 (Aviles et al. 2012, Eq. (15)): blind restatement and sanity tests

`BlindC2` below (namespace renamed from `Blind`, which run 0028Z already uses) is the blind restater's file (`runs/2026-10-30T0220Z/Aviles_blind.lean`),
definitions and statements verbatim; only the two `sorry`s are replaced by derivations from
`Work.Cosmography.Aviles.flatLCDM_coeffs`, and the printed claims, in the restater's own
reading, are refuted.
-/

open Filter Topology

namespace BlindC2

/-- Hubble rate H ≡ (1/a) da/dt (Eq. 3). -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Redshift: 1 + z = a0 / a(t), with a0 = a(t0) (source text after Eq. 15). -/
noncomputable def redshift (a : ℝ → ℝ) (t0 t : ℝ) : ℝ := a t0 / a t - 1

/-- Generic cosmographic ratio (1/(a Hⁿ)) dⁿa/dtⁿ, evaluated at time t. -/
noncomputable def cosmo (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  iteratedDeriv n a t / (a t * hubble a t ^ n)

/-- Eq. (3), subscript 0 = evaluated at t = t0. Note the minus sign on q only. -/
noncomputable def q0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := -cosmo 2 a t0
noncomputable def j0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := cosmo 3 a t0
noncomputable def s0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := cosmo 4 a t0
noncomputable def l0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := cosmo 5 a t0
noncomputable def m0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := cosmo 6 a t0

/-- Flat ΛCDM as stated before Eq. (15): H = H0 √(Ωm (1+z)³ + 1 − Ωm). -/
structure FlatLCDM (a : ℝ → ℝ) (t0 H0 Ωm : ℝ) : Prop where
  smooth : ContDiff ℝ 6 a
  pos : ∀ᶠ t in 𝓝 t0, 0 < a t
  norm : a t0 = 1
  H0_pos : 0 < H0
  friedmann : ∀ᶠ t in 𝓝 t0, hubble a t = H0 * √(Ωm * (1 + redshift a t0 t) ^ 3 + 1 - Ωm)

def PrintedL0 : Prop :=
  ∀ (a : ℝ → ℝ) (t0 H0 Ωm : ℝ), 0 ≤ Ωm → Ωm ≤ 1 → FlatLCDM a t0 H0 Ωm →
    l0 a t0 = 1 + 3 * Ωm - 27 / 2 * Ωm ^ 2

def PrintedM0 : Prop :=
  ∀ (a : ℝ → ℝ) (t0 H0 Ωm : ℝ), 0 ≤ Ωm → Ωm ≤ 1 → FlatLCDM a t0 H0 Ωm →
    m0 a t0 = 1 - 27 / 2 * Ωm ^ 2 - 81 * Ωm ^ 2 - 81 / 2 * Ωm ^ 3

/-- The blind model implies ours, with the same `H₀`. -/
lemma toOurs {a : ℝ → ℝ} {t0 H0 Ωm : ℝ} (h : FlatLCDM a t0 H0 Ωm) :
    Work.Cosmography.Aviles.IsFlatLCDM Ωm a t0 ∧ ContDiffAt ℝ 6 a t0 := by
  have hH : Checked.Cosmography.hubble a t0 = H0 := by
    have := h.friedmann.self_of_nhds
    simp only [redshift, h.norm, div_one, sub_self, add_zero, one_pow, mul_one,
      add_sub_cancel_left, Real.sqrt_one] at this
    simpa [hubble, Checked.Cosmography.hubble] using this
  refine ⟨⟨by rw [hH]; exact h.H0_pos, ?_⟩, h.smooth.contDiffAt⟩
  filter_upwards [h.pos, h.friedmann] with t hp hf
  refine ⟨hp, (h.smooth.differentiable (by norm_num)).differentiableAt, ?_⟩
  rw [hH]
  exact hf

theorem lcdm_l0 (a : ℝ → ℝ) (t0 H0 Ωm : ℝ) (h0 : 0 ≤ Ωm) (h1 : Ωm ≤ 1)
    (h : FlatLCDM a t0 H0 Ωm) :
    l0 a t0 = 1 + 3 * Ωm + 27 / 2 * Ωm ^ 2 := by
  obtain ⟨hL, hs⟩ := toOurs h
  exact (Work.Cosmography.Aviles.flatLCDM_coeffs Ωm a t0 hL hs).2.2.2.1

theorem lcdm_m0 (a : ℝ → ℝ) (t0 H0 Ωm : ℝ) (h0 : 0 ≤ Ωm) (h1 : Ωm ≤ 1)
    (h : FlatLCDM a t0 H0 Ωm) :
    m0 a t0 = 1 - 27 / 2 * Ωm - 81 * Ωm ^ 2 - 81 / 4 * Ωm ^ 3 := by
  obtain ⟨hL, hs⟩ := toOurs h
  exact (Work.Cosmography.Aviles.flatLCDM_coeffs Ωm a t0 hL hs).2.2.2.2

/-! ### A globally C⁶ Einstein–de Sitter model (the restater asks for `ContDiff ℝ 6 a`):
`g t = smoothTransition (4t − 1) · t^{2/3}`, equal to `t^{2/3}` for `t ≥ 1/2`, zero for
`t ≤ 1/4`. -/

noncomputable def g : ℝ → ℝ := fun t => Real.smoothTransition (4 * t - 1) * t ^ (2 / 3 : ℝ)

lemma g_eq {t : ℝ} (ht : 1 / 2 ≤ t) : g t = Work.Cosmography.Aviles.eds t := by
  simp only [g, Work.Cosmography.Aviles.eds]
  rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]

lemma g_ev {t : ℝ} (ht : 1 / 2 < t) : g =ᶠ[𝓝 t] Work.Cosmography.Aviles.eds := by
  filter_upwards [lt_mem_nhds ht] with x hx using g_eq hx.le

lemma g_smooth : ContDiff ℝ 6 g := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge 0 t with ht | ht
  · exact ((Real.smoothTransition.contDiff).comp (by fun_prop)).contDiffAt.mul
      (Real.contDiffAt_rpow_const_of_ne ht.ne')
  · have : g =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds (show t < 1 / 4 by linarith)] with x hx
      simp only [g]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq this

lemma g_flat : FlatLCDM g 1 (2 / 3) 1 := by
  open Work.Cosmography.Aviles in
  have hE := (eds_isFlatLCDM one_pos).2
  refine ⟨g_smooth, ?_, ?_, by norm_num, ?_⟩
  · filter_upwards [lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with t ht
    rw [g_eq ht.le]; exact Real.rpow_pos_of_pos (by linarith) _
  · rw [g_eq (by norm_num)]; simp [eds]
  · filter_upwards [hE, lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)] with t ⟨_, _, hf⟩ ht
    have hH1 : Checked.Cosmography.hubble eds 1 = 2 / 3 := by rw [hubble_eds one_pos]; norm_num
    have hd : deriv g t = deriv eds t := (g_ev ht).deriv_eq
    simp only [hubble, redshift, hd, g_eq ht.le, g_eq (show (1 / 2 : ℝ) ≤ 1 by norm_num)]
    rw [← hH1]
    exact hf

/-- The printed `l₀` is false in the restater's own reading too. -/
theorem printedL0_false : ¬ PrintedL0 := by
  intro h
  have h1 := h g 1 (2 / 3) 1 (by norm_num) le_rfl g_flat
  rw [lcdm_l0 g 1 (2 / 3) 1 (by norm_num) le_rfl g_flat] at h1
  norm_num at h1

/-- The printed `m₀` is false in the restater's own reading too. -/
theorem printedM0_false : ¬ PrintedM0 := by
  intro h
  have h1 := h g 1 (2 / 3) 1 (by norm_num) le_rfl g_flat
  rw [lcdm_m0 g 1 (2 / 3) 1 (by norm_num) le_rfl g_flat] at h1
  norm_num at h1

end BlindC2

namespace Work.Cosmography.AvilesAudit

open Work.Cosmography.Aviles Checked.Cosmography

/-! ### Sanity tests -/

/-- Not vacuous at Ω = 0: de Sitter `a = exp` is flat ΛCDM with Ω = 0, and the theorem gives
`l₀ = 1`, `m₀ = 1`, the textbook de Sitter values (all a⁽ⁿ⁾/(aHⁿ) = 1). -/
lemma deSitter_isFlatLCDM : IsFlatLCDM 0 Real.exp 0 := by
  refine ⟨by simp [hubble], Filter.Eventually.of_forall fun t => ⟨Real.exp_pos t,
    Real.differentiableAt_exp, ?_⟩⟩
  simp [hubble]

example : cosmoCoeff 5 Real.exp 0 = 1 ∧ cosmoCoeff 6 Real.exp 0 = 1 := by
  have := flatLCDM_coeffs 0 Real.exp 0 deSitter_isFlatLCDM Real.contDiff_exp.contDiffAt
  norm_num at this
  exact ⟨this.2.2.2.1, this.2.2.2.2⟩

/-- Bites: the general theorem at Ω = 1 agrees with the direct EdS computation
(`l0_eds` computes the 5th derivative of t^{2/3} independently). -/
example : (1 : ℝ) + 3 * 1 + 27 / 2 * 1 ^ 2 = cosmoCoeff 5 eds 1 := by
  rw [l0_eds one_pos]; norm_num

/-- Near-miss: no other value of l₀ at Ω = 1 is consistent with the model. -/
example (c : ℝ) (hc : c ≠ 35 / 2) :
    ¬ ∀ a t₀, IsFlatLCDM 1 a t₀ → ContDiffAt ℝ 6 a t₀ → cosmoCoeff 5 a t₀ = c := by
  intro h
  have := h eds 1 (eds_isFlatLCDM one_pos) (Real.contDiffAt_rpow_const_of_ne one_ne_zero)
  rw [l0_eds one_pos] at this
  exact hc this.symm

end Work.Cosmography.AvilesAudit
