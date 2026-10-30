import Checked.Fidelity.Pins

/-!
# Spec gaps for `FlatLCDMSpec` (spec-aware adversary)

`FlatLCDMSpec` (`Checked/Fidelity/MoreSpecs.lean`) is meant to characterise
`Checked.Cosmography.Aviles.IsFlatLCDM`. Its positive anchors are four exact solutions
(EdS, de Sitter, `sinh^{2/3}`, `sin^{2/3}`), closed under rescaling and time translation; its
negative anchors are contracting de Sitter, EdS / de Sitter with the wrong `Ω`, and two
one-sided piecewise models with `Ω = 0`. Every negative anchor is either *contracting* or a
*flat ΛCDM-anchor with the wrong Ω* or an `Ω = 0` one-sided splice; no scale factor outside the
anchor families (Milne, curved ΛCDM, `Ω < 0` bounce, ...) is ever tested. Hence:

* `gapL_curv` (A): **curvature allowed** — `H = H₀ √(Ω(1+z)³ + Ω_k(1+z)² + 1 − Ω − Ω_k)` for
  *some* `Ω_k` (flatness forgotten). Meets the spec; accepts Milne `a = t` (`Ω = 0`, `Ω_k = 1`),
  which is not flat ΛCDM (`milne_not_flatLCDM`).
* `gapL_decel` (A): **cosmographic surrogate** — "expanding, `a > 0`, and `q₀ = 3Ω/2 − 1`"
  (the true consequence `flatLCDM_coeffs` used as a definition). Meets the spec; accepts Milne
  with `Ω = 2/3` (`q₀ = 0`).
* `gapL_nonneg` (A): **Ω-range restriction** `IsFlatLCDM Ω a t₀ ∧ 0 ≤ Ω`. Meets the spec (every
  positive anchor has `Ω ≥ 0`); rejects the bouncing model `a = cosh^{2/3} t`, which is flat ΛCDM
  with `Ω = −1/sinh² t₀ < 0` (`cosh_isFlatLCDM`).
* `gapL_milneOne` (B): `IsFlatLCDM ∨ (Ω = 1 ∧ a is affine increasing)` — Milne declared to be EdS.

Mutations that are *not* gaps (paper arguments, equivalent to `IsFlatLCDM`): the law on the
punctured neighbourhood `𝓝[≠] t₀` plus `a t₀ > 0`, `H₀ > 0` (at `t₀` the law is `H₀ = H₀ · 1`
and `H₀ ≠ 0` gives differentiability); the squared law `H² = H₀²(…)` plus `H₀ > 0` (the radicand
is near 1, so `H ≠ 0` near `t₀`, and `H = (log a)'` has the Darboux property, so `H > 0`).
One-sided (`𝓝[<]`, `𝓝[>]`) versions are killed by `notPastOnly` / `notFutureOnly`.
-/

namespace Work.Fidelity.GapsLCDM

open Real Filter Topology Checked.Cosmography Checked.Cosmography.Aviles Checked.Fidelity

/-! ## Helpers -/

lemma hub_rescale (c : ℝ) (hc : 0 < c) (a : ℝ → ℝ) (t : ℝ) :
    hubble (fun s => c * a s) t = hubble a t := ms_hubble_rescale c hc.ne' a t

lemma diff_rescale (c : ℝ) (hc : 0 < c) (a : ℝ → ℝ) (t : ℝ) :
    DifferentiableAt ℝ (fun s => c * a s) t ↔ DifferentiableAt ℝ a t := by
  constructor
  · intro h
    have := h.const_mul c⁻¹
    simpa [← mul_assoc, inv_mul_cancel₀ hc.ne'] using this
  · intro h; exact h.const_mul c

lemma tendsto_shift (τ t₀ : ℝ) : Tendsto (fun s => s + τ) (𝓝 (t₀ - τ)) (𝓝 t₀) := by
  have := (tendsto_id (x := 𝓝 (t₀ - τ))).add_const τ
  rw [sub_add_cancel] at this
  exact this

/-- From `H = H₀ √R` with `H, H₀ > 0`: `(H/H₀)² = R`. -/
lemma sq_law {H H₀ R : ℝ} (hH₀ : 0 < H₀) (hH : 0 < H) (h : H = H₀ * √R) : (H / H₀) ^ 2 = R := by
  have hs : √R = H / H₀ := by field_simp; linarith
  have hR : 0 < R := Real.sqrt_pos.1 (hs ▸ div_pos hH hH₀)
  rw [← hs, Real.sq_sqrt hR.le]

/-- Two distinct values `y₁ < y₂ < 1` kill `c (y³ − 1) + k (y² − 1)`. -/
lemma two_pt {c k y₁ y₂ : ℝ} (h0 : 0 < y₁) (h12 : y₁ < y₂) (h2 : y₂ < 1)
    (e₁ : c * (y₁ ^ 3 - 1) + k * (y₁ ^ 2 - 1) = 0) (e₂ : c * (y₂ ^ 3 - 1) + k * (y₂ ^ 2 - 1) = 0) :
    c = 0 := by
  have f₁ : c * (y₁ ^ 2 + y₁ + 1) + k * (y₁ + 1) = 0 := by
    have : (y₁ - 1) * (c * (y₁ ^ 2 + y₁ + 1) + k * (y₁ + 1)) = 0 := by linear_combination e₁
    exact (mul_eq_zero.1 this).resolve_left (by linarith)
  have f₂ : c * (y₂ ^ 2 + y₂ + 1) + k * (y₂ + 1) = 0 := by
    have : (y₂ - 1) * (c * (y₂ ^ 2 + y₂ + 1) + k * (y₂ + 1)) = 0 := by linear_combination e₂
    exact (mul_eq_zero.1 this).resolve_left (by linarith)
  have : c * ((y₁ - y₂) * (y₁ * y₂ + y₁ + y₂)) = 0 := by
    linear_combination (y₂ + 1) * f₁ - (y₁ + 1) * f₂
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h (by linarith)
    · nlinarith

/-- Two points `t₀ < t₂ < t₁` in an eventually-true set. -/
lemma two_gt {p : ℝ → Prop} {t₀ : ℝ} (h : ∀ᶠ t in 𝓝 t₀, p t) :
    ∃ t₁ t₂, t₀ < t₂ ∧ t₂ < t₁ ∧ p t₁ ∧ p t₂ := by
  obtain ⟨t₁, h1, p1⟩ := h.exists_gt
  obtain ⟨t₂, h2, p2, h21⟩ := (h.and (gt_mem_nhds h1)).exists_gt
  exact ⟨t₁, t₂, h2, h21, p1, p2⟩

lemma two_lt {p : ℝ → Prop} {t₀ : ℝ} (h : ∀ᶠ t in 𝓝 t₀, p t) :
    ∃ t₁ t₂, t₁ < t₂ ∧ t₂ < t₀ ∧ p t₁ ∧ p t₂ := by
  obtain ⟨t₁, h1, p1⟩ := h.exists_lt
  obtain ⟨t₂, h2, p2, h21⟩ := (h.and (lt_mem_nhds h1)).exists_lt
  exact ⟨t₁, t₂, h21, h2, p1, p2⟩

lemma hubble_id (t : ℝ) : hubble id t = 1 / t := by simp [hubble]

/-- Milne `a = t` is not flat ΛCDM at `t₀ = 1`, for any `Ω`. -/
theorem milne_not_flatLCDM (Ω : ℝ) : ¬ IsFlatLCDM Ω id 1 := by
  rintro ⟨-, hev⟩
  obtain ⟨t₁, t₂, h2, h21, ⟨-, -, e₁⟩, ⟨-, -, e₂⟩⟩ := two_gt hev
  have p1 : 0 < t₁ := by linarith
  have p2 : 0 < t₂ := by linarith
  rw [hubble_id, hubble_id, redshift] at e₁ e₂
  simp only [id, add_sub_cancel] at e₁ e₂
  rw [div_one] at e₁ e₂
  have s₁ := sq_law one_pos (by positivity : (0:ℝ) < 1 / t₁) e₁
  have s₂ := sq_law one_pos (by positivity : (0:ℝ) < 1 / t₂) e₂
  simp only [div_one] at s₁ s₂
  have hy1 : 1 / t₁ < 1 / t₂ := one_div_lt_one_div_of_lt p2 h21
  have hy2 : 1 / t₂ < 1 := by rw [div_lt_one p2]; exact h2
  have := two_pt (c := Ω) (k := -1) (by positivity) hy1 hy2 (by linear_combination -s₁)
    (by linear_combination -s₂)
  subst this
  have : (1 / t₁) ^ 2 < 1 := pow_lt_one₀ (by positivity) (hy1.trans hy2) (by norm_num)
  linarith

/-- A splice of two functions with the same value and derivative at `0`. -/
lemma splice_hasDerivAt (g k : ℝ → ℝ) (d : ℝ) (hg : HasDerivAt g d 0) (hk : HasDerivAt k d 0)
    (h0 : g 0 = k 0) : HasDerivAt (fun t => if t ≤ 0 then g t else k t) d 0 := by
  have h1 : HasDerivWithinAt (fun t => if t ≤ 0 then g t else k t) d (Set.Iic 0) 0 :=
    hg.hasDerivWithinAt.congr (fun x hx => by simp [Set.mem_Iic.1 hx]) (by simp)
  have h2 : HasDerivWithinAt (fun t => if t ≤ 0 then g t else k t) d (Set.Ici 0) 0 := by
    refine hk.hasDerivWithinAt.congr (fun x hx => ?_) (by simp [h0])
    rcases (Set.mem_Ici.1 hx).lt_or_eq with hx | hx
    · simp [not_le.2 hx]
    · subst hx; simp [h0]
  have := h1.union h2
  rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this

lemma hasDerivAt_onePlus (t : ℝ) : HasDerivAt (fun s => 1 + s) 1 t := (hasDerivAt_id t).const_add 1

/-- `pastDS` : de Sitter for `t ≤ 0`, coasting after (spec's `notPastOnly` model). -/
lemma pastDS_hasDerivAt : HasDerivAt (fun t => if t ≤ 0 then Real.exp t else 1 + t) 1 0 :=
  splice_hasDerivAt _ _ 1 (by simpa using Real.hasDerivAt_exp 0) (hasDerivAt_onePlus 0) (by simp)

lemma futDS_hasDerivAt : HasDerivAt (fun t => if t ≤ 0 then 1 + t else Real.exp t) 1 0 :=
  splice_hasDerivAt _ _ 1 (hasDerivAt_onePlus 0) (by simpa using Real.hasDerivAt_exp 0) (by simp)

lemma pastDS_hubble0 : hubble (fun t => if t ≤ 0 then Real.exp t else 1 + t) 0 = 1 := by
  simp [hubble, pastDS_hasDerivAt.deriv]

lemma futDS_hubble0 : hubble (fun t => if t ≤ 0 then 1 + t else Real.exp t) 0 = 1 := by
  simp [hubble, futDS_hasDerivAt.deriv]

/-! ## Gap 1 (A): curvature allowed (flatness forgotten) -/

/-- ΛCDM with *some* curvature: `H = H₀ √(Ω(1+z)³ + Ω_k(1+z)² + 1 − Ω − Ω_k)` near `t₀`. -/
def PCurv (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < hubble a t₀ ∧ ∃ k : ℝ, ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
    hubble a t = hubble a t₀ *
      √(Ω * (1 + redshift a t₀ t) ^ 3 + k * (1 + redshift a t₀ t) ^ 2 + 1 - Ω - k)

lemma pcurv_of_flat {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h : IsFlatLCDM Ω a t₀) : PCurv Ω a t₀ :=
  ⟨h.1, 0, h.2.mono fun t ht => by simpa using ht⟩

/-- Ω = 0 splices: a point with `H = H₀` and `y ≠ 1` forces `k = 0`. -/
lemma k_zero {k y : ℝ} (hy : y ≠ 1) (hy0 : 0 < y)
    (h : (1 : ℝ) = 1 * √(0 * y ^ 3 + k * y ^ 2 + 1 - 0 - k)) : k = 0 := by
  have := sq_law one_pos one_pos h
  have e : k * ((y - 1) * (y + 1)) = 0 := by linear_combination -this
  rcases mul_eq_zero.1 e with e | e
  · exact e
  · rcases mul_eq_zero.1 e with e | e
    · exact absurd (by linarith) hy
    · linarith

theorem gapL_curv : FlatLCDMSpec PCurv where
  eds t₀ h := pcurv_of_flat (isFlatLCDM_meets_spec.eds t₀ h)
  deSitter h t₀ hh := pcurv_of_flat (isFlatLCDM_meets_spec.deSitter h t₀ hh)
  lcdm t₀ h := pcurv_of_flat (isFlatLCDM_meets_spec.lcdm t₀ h)
  negLambda t₀ h₀ h₁ := pcurv_of_flat (isFlatLCDM_meets_spec.negLambda t₀ h₀ h₁)
  rescale c hc Ω a t₀ := by
    simp only [PCurv, hub_rescale c hc, redshift_rescale c hc, diff_rescale c hc,
      mul_pos_iff_of_pos_left hc]
  translate τ Ω a t₀ h := by
    obtain ⟨hH, k, hev⟩ := h
    refine ⟨by rwa [ms_hubble_translate, sub_add_cancel], k, ?_⟩
    filter_upwards [(tendsto_shift τ t₀).eventually hev] with s ⟨h1, h2, h3⟩
    refine ⟨h1, (h2.hasDerivAt.comp_add_const s τ).differentiableAt, ?_⟩
    rw [ms_hubble_translate, ms_hubble_translate, sub_add_cancel]
    simpa only [redshift, sub_add_cancel] using h3
  expanding Ω a t₀ h := by
    obtain ⟨hH, k, hev⟩ := h
    have ha : 0 < a t₀ := hev.self_of_nhds.1
    exact ⟨ha, (div_pos_iff_of_pos_right ha).1 hH⟩
  contracting Ω h t₀ hh hP := by
    have := hP.1
    rw [show (fun t => Real.exp (-h * t)) = fun t => Real.exp ((-h) * t) from rfl,
      ms_hubble_expMul] at this
    linarith
  edsOnlyOne Ω t₀ h₀ hΩ hP := by
    obtain ⟨-, k, hev⟩ := hP
    obtain ⟨t₁, t₂, h2, h21, ⟨-, -, e₁⟩, ⟨-, -, e₂⟩⟩ := two_gt hev
    have p1 : 0 < t₁ := by linarith
    have p2 : 0 < t₂ := by linarith
    change hubble eds t₁ = hubble eds t₀ * _ at e₁
    change hubble eds t₂ = hubble eds t₀ * _ at e₂
    rw [hubble_eds p1, hubble_eds h₀, redshift, add_sub_cancel] at e₁
    rw [hubble_eds p2, hubble_eds h₀, redshift, add_sub_cancel] at e₂
    have s₁ := sq_law (by positivity) (by positivity) e₁
    have s₂ := sq_law (by positivity) (by positivity) e₂
    have c0 : (eds t₀) ^ 3 = t₀ ^ 2 := eds_cube h₀
    have c1 : (eds t₁) ^ 3 = t₁ ^ 2 := eds_cube p1
    have c2 : (eds t₂) ^ 3 = t₂ ^ 2 := eds_cube p2
    have q0 : 0 < eds t₀ := Real.rpow_pos_of_pos h₀ _
    have q1 : 0 < eds t₁ := Real.rpow_pos_of_pos p1 _
    have q2 : 0 < eds t₂ := Real.rpow_pos_of_pos p2 _
    have r1 : 2 / 3 / t₁ / (2 / 3 / t₀) = t₀ / t₁ := by field_simp
    have r2 : 2 / 3 / t₂ / (2 / 3 / t₀) = t₀ / t₂ := by field_simp
    have y1 : (t₀ / t₁) ^ 2 = (eds t₀ / eds t₁) ^ 3 := by rw [div_pow, div_pow, c0, c1]
    have y2 : (t₀ / t₂) ^ 2 = (eds t₀ / eds t₂) ^ 3 := by rw [div_pow, div_pow, c0, c2]
    change (2 / 3 / t₁ / (2 / 3 / t₀)) ^ 2 = Ω * (eds t₀ / eds t₁) ^ 3 +
      k * (eds t₀ / eds t₁) ^ 2 + 1 - Ω - k at s₁
    change (2 / 3 / t₂ / (2 / 3 / t₀)) ^ 2 = Ω * (eds t₀ / eds t₂) ^ 3 +
      k * (eds t₀ / eds t₂) ^ 2 + 1 - Ω - k at s₂
    rw [r1, y1] at s₁; rw [r2, y2] at s₂
    have m21 : eds t₂ < eds t₁ := Real.rpow_lt_rpow p2.le h21 (by norm_num)
    have m02 : eds t₀ < eds t₂ := Real.rpow_lt_rpow h₀.le h2 (by norm_num)
    have := two_pt (c := 1 - Ω) (k := -k) (div_pos q0 q1)
      (div_lt_div_of_pos_left q0 q2 m21) ((div_lt_one q2).2 m02)
      (by linear_combination s₁) (by linear_combination s₂)
    exact hΩ (by linarith)
  deSitterOnlyZero Ω h t₀ hh hΩ hP := by
    obtain ⟨-, k, hev⟩ := hP
    obtain ⟨t₁, t₂, h2, h21, ⟨-, -, e₁⟩, ⟨-, -, e₂⟩⟩ := two_gt hev
    rw [ms_hubble_expMul, ms_hubble_expMul, redshift, add_sub_cancel] at e₁ e₂
    have s₁ := sq_law hh hh e₁
    have s₂ := sq_law hh hh e₂
    rw [div_self hh.ne'] at s₁ s₂
    have E0 := Real.exp_pos (h * t₀)
    have E1 := Real.exp_pos (h * t₁)
    have E2 := Real.exp_pos (h * t₂)
    have m21 : Real.exp (h * t₂) < Real.exp (h * t₁) := Real.exp_lt_exp.2 (by nlinarith)
    have m02 : Real.exp (h * t₀) < Real.exp (h * t₂) := Real.exp_lt_exp.2 (by nlinarith)
    exact hΩ (two_pt (c := Ω) (k := k) (div_pos E0 E1) (div_lt_div_of_pos_left E0 E2 m21)
      ((div_lt_one E2).2 m02) (by linear_combination -s₁) (by linear_combination -s₂))
  notPastOnly hP := by
    obtain ⟨-, k, hev⟩ := hP
    obtain ⟨t₁, ht₁, -, -, e₁⟩ := hev.exists_lt
    obtain ⟨t₂, ht₂, -, -, e₂⟩ := hev.exists_gt
    have h1 : hubble (fun t => if t ≤ 0 then Real.exp t else 1 + t) t₁ = 1 := by
      rw [ms_hubble_eventually (b := Real.exp), ms_hubble_exp]
      filter_upwards [gt_mem_nhds ht₁] with s hs; simp [hs.le]
    have h2 : hubble (fun t => if t ≤ 0 then Real.exp t else 1 + t) t₂ = 1 / (1 + t₂) := by
      rw [ms_hubble_eventually (b := fun s => 1 + s), ms_hubble_onePlus]
      filter_upwards [lt_mem_nhds ht₂] with s hs; simp [not_le.2 hs]
    rw [h1, pastDS_hubble0, redshift] at e₁
    rw [h2, pastDS_hubble0] at e₂
    simp only [ht₁.le, ite_true, le_refl, Real.exp_zero, add_sub_cancel] at e₁
    have hk : k = 0 := k_zero (y := 1 / Real.exp t₁)
      (by rw [Ne, div_eq_one_iff_eq (Real.exp_pos _).ne']; exact fun e =>
        absurd (Real.exp_eq_one_iff _ |>.1 e.symm) ht₁.ne)
      (by positivity) e₁
    subst hk
    norm_num at e₂
    linarith
  notFutureOnly hP := by
    obtain ⟨-, k, hev⟩ := hP
    obtain ⟨t₁, ht₁, ⟨-, -, e₁⟩, hm1⟩ := (hev.and (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))).exists_lt
    obtain ⟨t₂, ht₂, -, -, e₂⟩ := hev.exists_gt
    have h1 : hubble (fun t => if t ≤ 0 then 1 + t else Real.exp t) t₁ = 1 / (1 + t₁) := by
      rw [ms_hubble_eventually (b := fun s => 1 + s), ms_hubble_onePlus]
      filter_upwards [gt_mem_nhds ht₁] with s hs; simp [hs.le]
    have h2 : hubble (fun t => if t ≤ 0 then 1 + t else Real.exp t) t₂ = 1 := by
      rw [ms_hubble_eventually (b := Real.exp), ms_hubble_exp]
      filter_upwards [lt_mem_nhds ht₂] with s hs; simp [not_le.2 hs]
    rw [h2, futDS_hubble0, redshift] at e₂
    rw [h1, futDS_hubble0] at e₁
    simp only [not_le.2 ht₂, ite_false, le_refl, ite_true, add_zero, add_sub_cancel] at e₂
    have hk : k = 0 := k_zero (y := 1 / Real.exp t₂)
      (by rw [Ne, div_eq_one_iff_eq (Real.exp_pos _).ne']; exact fun e =>
        absurd (Real.exp_eq_one_iff _ |>.1 e.symm) ht₂.ne')
      (by positivity) e₂
    subst hk
    have : 0 < 1 + t₁ := by linarith
    norm_num at e₁
    linarith

/-- Milne `a = t` (`Ω = 0`, `Ω_k = 1`, `H = 1/t = H₀(1+z)`) is accepted by `PCurv`. -/
theorem pcurv_milne : PCurv 0 id 1 := by
  refine ⟨by rw [hubble_id]; norm_num, 1, ?_⟩
  filter_upwards [lt_mem_nhds one_pos] with t ht
  refine ⟨ht, differentiableAt_id, ?_⟩
  rw [hubble_id, hubble_id, redshift]
  simp only [id, add_sub_cancel]
  rw [show 0 * (1 / t) ^ 3 + 1 * (1 / t) ^ 2 + 1 - 0 - 1 = (1 / t) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  ring

theorem gapL_curv_wrong : PCurv 0 id 1 ∧ ¬ IsFlatLCDM 0 id 1 :=
  ⟨pcurv_milne, milne_not_flatLCDM 0⟩

/-! ## Gap 2 (A): cosmographic surrogate `q₀ = 3Ω/2 − 1` -/

/-- "Expanding, `a > 0`, and deceleration `q₀ = 3Ω/2 − 1`" (the true consequence
`flatLCDM_coeffs` mistaken for the definition). -/
def PDecel (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < a t₀ ∧ 0 < deriv a t₀ ∧ decel a t₀ = 3 / 2 * Ω - 1

lemma pdecel_of_flat {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h : IsFlatLCDM Ω a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) : PDecel Ω a t₀ :=
  ⟨(isFlatLCDM_meets_spec.expanding Ω a t₀ h).1, (isFlatLCDM_meets_spec.expanding Ω a t₀ h).2,
    (flatLCDM_coeffs Ω a t₀ h hs).1⟩

/-- A `C¹` splice whose two halves have different second derivatives at `0` has junk
`deriv (deriv f) 0 = 0`. -/
lemma splice_deriv2 (g g' k k' : ℝ → ℝ) (d₁ d₂ : ℝ) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hk : ∀ x, HasDerivAt k (k' x) x) (h0 : g 0 = k 0) (h0' : g' 0 = k' 0)
    (hg' : HasDerivAt g' d₁ 0) (hk' : HasDerivAt k' d₂ 0) (hd : d₁ ≠ d₂) :
    deriv (deriv (fun t => if t ≤ 0 then g t else k t)) 0 = 0 := by
  set f := fun t => if t ≤ 0 then g t else k t with hf
  have e0 : deriv f 0 = g' 0 := (splice_hasDerivAt g k (g' 0) (hg 0) (h0' ▸ hk 0) h0).deriv
  have eL : ∀ x ∈ Set.Iic (0 : ℝ), deriv f x = g' x := by
    intro x hx
    rcases (Set.mem_Iic.1 hx).lt_or_eq with hx | hx
    · have : f =ᶠ[𝓝 x] g := by
        filter_upwards [gt_mem_nhds hx] with s hs; simp [hf, hs.le]
      rw [this.deriv_eq, (hg x).deriv]
    · subst hx; exact e0
  have eR : ∀ x ∈ Set.Ici (0 : ℝ), deriv f x = k' x := by
    intro x hx
    rcases (Set.mem_Ici.1 hx).lt_or_eq with hx | hx
    · have : f =ᶠ[𝓝 x] k := by
        filter_upwards [lt_mem_nhds hx] with s hs; simp [hf, not_le.2 hs]
      rw [this.deriv_eq, (hk x).deriv]
    · subst hx; rw [e0, h0']
  apply deriv_zero_of_not_differentiableAt
  intro hD
  have L : HasDerivWithinAt (deriv f) d₁ (Set.Iic 0) 0 :=
    hg'.hasDerivWithinAt.congr eL (eL 0 (Set.mem_Iic.2 le_rfl))
  have R : HasDerivWithinAt (deriv f) d₂ (Set.Ici 0) 0 :=
    hk'.hasDerivWithinAt.congr eR (eR 0 (Set.mem_Ici.2 le_rfl))
  have u1 := (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv _ hD.hasDerivAt.hasDerivWithinAt L
  have u2 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hD.hasDerivAt.hasDerivWithinAt R
  exact hd (u1.symm.trans u2)

lemma contDiffAt_rpow23_comp {f : ℝ → ℝ} {t : ℝ} (hf : ContDiff ℝ ⊤ f) (h : f t ≠ 0) :
    ContDiffAt ℝ 6 (fun s => f s ^ (2 / 3 : ℝ)) t :=
  (Real.contDiffAt_rpow_const_of_ne h).comp t (hf.of_le le_top).contDiffAt

theorem gapL_decel : FlatLCDMSpec PDecel where
  eds t₀ h := pdecel_of_flat (isFlatLCDM_meets_spec.eds t₀ h)
    (Real.contDiffAt_rpow_const_of_ne h.ne')
  deSitter h t₀ hh := pdecel_of_flat (isFlatLCDM_meets_spec.deSitter h t₀ hh)
    ((contDiff_const.mul contDiff_id).exp.contDiffAt)
  lcdm t₀ h := pdecel_of_flat (isFlatLCDM_meets_spec.lcdm t₀ h)
    (contDiffAt_rpow23_comp Real.contDiff_sinh (Real.sinh_pos_iff.2 h).ne')
  negLambda t₀ h₀ h₁ := pdecel_of_flat (isFlatLCDM_meets_spec.negLambda t₀ h₀ h₁)
    (contDiffAt_rpow23_comp Real.contDiff_sin
      (Real.sin_pos_of_pos_of_lt_pi h₀ (by linarith [Real.pi_pos])).ne')
  rescale c hc Ω a t₀ := by
    unfold PDecel
    rw [deriv_const_mul_field']
    simp only [mul_pos_iff_of_pos_left hc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by rw [← decel_meets_spec.rescale c hc a t₀ h2.ne']; exact h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by rw [decel_meets_spec.rescale c hc a t₀ h2.ne']; exact h3⟩
  translate τ Ω a t₀ h := by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by simpa using h1, by rw [deriv_comp_add_const, sub_add_cancel]; exact h2, ?_⟩
    rw [decel_meets_spec.translate τ a (t₀ - τ) (by rw [sub_add_cancel]; exact h2.ne'),
      sub_add_cancel]
    exact h3
  expanding Ω a t₀ h := ⟨h.1, h.2.1⟩
  contracting Ω h t₀ hh hP := by
    have := hP.2.1
    rw [(ms_hasDerivAt_expMul (-h) t₀).deriv] at this
    have := Real.exp_pos (-h * t₀)
    nlinarith
  edsOnlyOne Ω t₀ h₀ hΩ hP := by
    have := hP.2.2
    rw [decel_meets_spec.eds t₀ h₀] at this
    exact hΩ (by linarith)
  deSitterOnlyZero Ω h t₀ hh hΩ hP := by
    have := hP.2.2
    rw [decel_meets_spec.deSitter h t₀ hh.ne'] at this
    exact hΩ (by linarith)
  notPastOnly hP := by
    have := hP.2.2
    rw [decel, splice_deriv2 Real.exp Real.exp (fun s => 1 + s) (fun _ => 1) 1 0
      Real.hasDerivAt_exp hasDerivAt_onePlus (by simp) (by simp)
      (by simpa using Real.hasDerivAt_exp 0) (hasDerivAt_const _ _) one_ne_zero] at this
    norm_num at this
  notFutureOnly hP := by
    have := hP.2.2
    rw [decel, splice_deriv2 (fun s => 1 + s) (fun _ => 1) Real.exp Real.exp 0 1
      hasDerivAt_onePlus Real.hasDerivAt_exp (by simp) (by simp)
      (hasDerivAt_const _ _) (by simpa using Real.hasDerivAt_exp 0) zero_ne_one] at this
    norm_num at this

/-- Milne with `Ω = 2/3` has `q₀ = 0 = 3Ω/2 − 1` but is not flat ΛCDM. -/
theorem gapL_decel_wrong : PDecel (2 / 3) id 1 ∧ ¬ IsFlatLCDM (2 / 3) id 1 := by
  refine ⟨⟨by norm_num, by simp, ?_⟩, milne_not_flatLCDM _⟩
  simp [decel]

/-! ## Gap 3 (A): Ω-range restriction `0 ≤ Ω` -/

/-- Flat ΛCDM with a non-negative matter fraction. -/
def PNonneg (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop := IsFlatLCDM Ω a t₀ ∧ 0 ≤ Ω

theorem gapL_nonneg : FlatLCDMSpec PNonneg where
  eds t₀ h := ⟨isFlatLCDM_meets_spec.eds t₀ h, zero_le_one⟩
  deSitter h t₀ hh := ⟨isFlatLCDM_meets_spec.deSitter h t₀ hh, le_rfl⟩
  lcdm t₀ h := ⟨isFlatLCDM_meets_spec.lcdm t₀ h, by positivity⟩
  negLambda t₀ h₀ h₁ := ⟨isFlatLCDM_meets_spec.negLambda t₀ h₀ h₁, by positivity⟩
  rescale c hc Ω a t₀ := and_congr_left' (isFlatLCDM_meets_spec.rescale c hc Ω a t₀)
  translate τ Ω a t₀ h := ⟨isFlatLCDM_meets_spec.translate τ Ω a t₀ h.1, h.2⟩
  expanding Ω a t₀ h := isFlatLCDM_meets_spec.expanding Ω a t₀ h.1
  contracting Ω h t₀ hh hP := isFlatLCDM_meets_spec.contracting Ω h t₀ hh hP.1
  edsOnlyOne Ω t₀ h₀ hΩ hP := isFlatLCDM_meets_spec.edsOnlyOne Ω t₀ h₀ hΩ hP.1
  deSitterOnlyZero Ω h t₀ hh hΩ hP := isFlatLCDM_meets_spec.deSitterOnlyZero Ω h t₀ hh hΩ hP.1
  notPastOnly hP := isFlatLCDM_meets_spec.notPastOnly hP.1
  notFutureOnly hP := isFlatLCDM_meets_spec.notFutureOnly hP.1

/-- Bouncing flat ΛCDM with negative matter density, `a = cosh^{2/3} t` (`H = (2/3) tanh t`). -/
noncomputable def bounce : ℝ → ℝ := fun t => Real.cosh t ^ (2 / 3 : ℝ)

lemma hasDerivAt_bounce (t : ℝ) :
    HasDerivAt bounce (Real.sinh t * (2 / 3) * Real.cosh t ^ ((2 / 3 : ℝ) - 1)) t :=
  (Real.hasDerivAt_cosh t).rpow_const (Or.inl (Real.cosh_pos t).ne')

lemma hubble_bounce (t : ℝ) : hubble bounce t = 2 / 3 * Real.sinh t / Real.cosh t := by
  have hc := Real.cosh_pos t
  unfold hubble
  rw [(hasDerivAt_bounce t).deriv, bounce, Real.rpow_sub hc, Real.rpow_one]
  have : 0 < Real.cosh t ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  field_simp

lemma bounce_cube (t : ℝ) : bounce t ^ 3 = Real.cosh t ^ 2 := by
  unfold bounce
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.cosh_pos t).le]; norm_num

/-- `cosh^{2/3}` is flat ΛCDM at every `t₀ > 0` with `Ω = −1/sinh² t₀ < 0`. -/
theorem bounce_isFlatLCDM {t₀ : ℝ} (h₀ : 0 < t₀) :
    IsFlatLCDM (-1 / Real.sinh t₀ ^ 2) bounce t₀ := by
  have hs0 : 0 < Real.sinh t₀ := Real.sinh_pos_iff.2 h₀
  have hc0 : 0 < Real.cosh t₀ := Real.cosh_pos t₀
  refine ⟨by rw [hubble_bounce]; positivity, ?_⟩
  filter_upwards [lt_mem_nhds h₀] with t ht
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.2 ht
  have hc : 0 < Real.cosh t := Real.cosh_pos t
  refine ⟨Real.rpow_pos_of_pos hc _, (hasDerivAt_bounce t).differentiableAt, ?_⟩
  rw [hubble_bounce, hubble_bounce, redshift, add_sub_cancel]
  have e0 : 0 < bounce t₀ := Real.rpow_pos_of_pos hc0 _
  have e1 : 0 < bounce t := Real.rpow_pos_of_pos hc _
  have harg : -1 / Real.sinh t₀ ^ 2 * (bounce t₀ / bounce t) ^ 3 + 1 - -1 / Real.sinh t₀ ^ 2 =
      (Real.cosh t₀ * Real.sinh t / (Real.sinh t₀ * Real.cosh t)) ^ 2 := by
    rw [div_pow, bounce_cube, bounce_cube]
    have h1 := Real.cosh_sq t₀
    have h2 := Real.cosh_sq t
    field_simp
    linear_combination (Real.cosh t₀ ^ 2) * h2 - (Real.cosh t ^ 2) * h1
  rw [harg, Real.sqrt_sq (by positivity)]
  field_simp

theorem gapL_nonneg_wrong : IsFlatLCDM (-1 / Real.sinh 1 ^ 2) bounce 1 ∧
    ¬ PNonneg (-1 / Real.sinh 1 ^ 2) bounce 1 := by
  refine ⟨bounce_isFlatLCDM one_pos, fun h => ?_⟩
  have := h.2
  have : 0 < Real.sinh 1 ^ 2 := by have := Real.sinh_pos_iff.2 (one_pos (α := ℝ)); positivity
  have : -1 / Real.sinh 1 ^ 2 < 0 := div_neg_of_neg_of_pos (by norm_num) this
  linarith

/-! ## Gap 4 (B): Milne declared to be Einstein–de Sitter -/

/-- `IsFlatLCDM`, or `Ω = 1` with an increasing affine scale factor. -/
def PMilneOne (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  IsFlatLCDM Ω a t₀ ∨ (Ω = 1 ∧ ∃ c s : ℝ, 0 < c ∧ 0 < t₀ + s ∧ ∀ t, a t = c * (t + s))

lemma exp_not_affine (h c s : ℝ) (hE : ∀ t, Real.exp (h * t) = c * (t + s)) : False := by
  have := hE (-s); rw [neg_add_cancel, mul_zero] at this
  exact (Real.exp_pos _).ne' this

theorem gapL_milneOne : FlatLCDMSpec PMilneOne where
  eds t₀ h := Or.inl (isFlatLCDM_meets_spec.eds t₀ h)
  deSitter h t₀ hh := Or.inl (isFlatLCDM_meets_spec.deSitter h t₀ hh)
  lcdm t₀ h := Or.inl (isFlatLCDM_meets_spec.lcdm t₀ h)
  negLambda t₀ h₀ h₁ := Or.inl (isFlatLCDM_meets_spec.negLambda t₀ h₀ h₁)
  rescale c hc Ω a t₀ := by
    unfold PMilneOne
    rw [isFlatLCDM_meets_spec.rescale c hc Ω a t₀]
    apply or_congr_right
    apply and_congr_right; intro _
    constructor
    · rintro ⟨d, s, hd, hs, hE⟩
      refine ⟨d / c, s, div_pos hd hc, hs, fun t => ?_⟩
      have := hE t; simp only at this; field_simp; linarith
    · rintro ⟨d, s, hd, hs, hE⟩
      exact ⟨c * d, s, mul_pos hc hd, hs, fun t => by show c * a t = _; rw [hE t]; ring⟩
  translate τ Ω a t₀ h := by
    rcases h with h | ⟨hΩ, c, s, hc, hs, hE⟩
    · exact Or.inl (isFlatLCDM_meets_spec.translate τ Ω a t₀ h)
    · exact Or.inr ⟨hΩ, c, s + τ, hc, by linarith, fun t => by show a (t + τ) = _; rw [hE]; ring⟩
  expanding Ω a t₀ h := by
    rcases h with h | ⟨-, c, s, hc, hs, hE⟩
    · exact isFlatLCDM_meets_spec.expanding Ω a t₀ h
    · have ha : a = fun t => c * (t + s) := funext hE
      subst ha
      refine ⟨by positivity, ?_⟩
      rw [deriv_const_mul_field']
      show 0 < c * deriv (fun t => t + s) t₀
      rw [deriv_add_const, deriv_id'']; simpa using hc
  contracting Ω h t₀ hh hP := by
    rcases hP with hP | ⟨-, c, s, -, -, hE⟩
    · exact isFlatLCDM_meets_spec.contracting Ω h t₀ hh hP
    · exact exp_not_affine (-h) c s hE
  edsOnlyOne Ω t₀ h₀ hΩ hP := by
    rcases hP with hP | ⟨h1, -⟩
    · exact isFlatLCDM_meets_spec.edsOnlyOne Ω t₀ h₀ hΩ hP
    · exact hΩ h1
  deSitterOnlyZero Ω h t₀ hh hΩ hP := by
    rcases hP with hP | ⟨-, c, s, -, -, hE⟩
    · exact isFlatLCDM_meets_spec.deSitterOnlyZero Ω h t₀ hh hΩ hP
    · exact exp_not_affine h c s hE
  notPastOnly hP := by
    rcases hP with hP | ⟨h1, -⟩
    · exact isFlatLCDM_meets_spec.notPastOnly hP
    · norm_num at h1
  notFutureOnly hP := by
    rcases hP with hP | ⟨h1, -⟩
    · exact isFlatLCDM_meets_spec.notFutureOnly hP
    · norm_num at h1

theorem gapL_milneOne_wrong : PMilneOne 1 id 1 ∧ ¬ IsFlatLCDM 1 id 1 :=
  ⟨Or.inr ⟨rfl, 1, 0, one_pos, by norm_num, fun t => by simp⟩, milne_not_flatLCDM 1⟩

end Work.Fidelity.GapsLCDM
