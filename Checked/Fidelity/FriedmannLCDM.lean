import Mathlib.Analysis.Calculus.Darboux
import Checked.Fidelity.Pins

/-!
# `IsFlatLCDM` pinned by a blind textbook specification (trust track T1)

`Checked.Cosmography.Aviles.IsFlatLCDM Ω a t₀` (the model hypothesis behind finding F1) is the
paper's sentence "H = H₀ √(Ω(1+z)³ + 1 − Ω)" near `t₀`, `H₀ > 0`. The anchors-only
`FlatLCDMSpec` (`MoreSpecs.lean`) leaked to a spec-aware adversary (run 1828Z,
`Work/Fidelity/SpecGapsLCDM.lean`: flatness forgotten, a `q₀` stand-in, an `Ω ≥ 0` restriction).

Here the definition is tied to a *first-principles* formulation written blind:

* `FriedmannLCDM` is copied verbatim from `Work/Fidelity/FriedmannBlind.lean` (frozen in commit
  3a4a5b8), written by a subagent that did not read any repository Lean file: the flat Friedmann
  equation `(ȧ/a)² = ρ + Λ/3` (`8πG/3 = 1`, `c = 1`, `K = 0`) with integrated dust continuity
  `ρ a³ = const`, expansion `ȧ(t₀) > 0`, and `Ω = ρ(t₀)/H₀²`. Referee
  `runs/2026-10-30T2028Z/referee_friedmann.md`: STANDS.
* `isFlatLCDM_iff_friedmann`: the two are equivalent, for every `Ω`, `a`, `t₀`. The non-trivial
  direction needs Darboux's theorem: the Friedmann equation fixes only `H²`, and `ȧ > 0` at `t₀`
  propagates to a neighbourhood because a derivative that never vanishes on an interval has
  constant sign.
* `FlatLCDMSpec2` = `FlatLCDMSpec` + the Friedmann law + two anchors outside the old anchor
  families (Milne `a = t` is never flat ΛCDM; the bounce `cosh^{2/3}` is flat ΛCDM with `Ω < 0`).
  `isFlatLCDM_meets_spec2`, and `flatLCDMSpec2_pins`: any predicate meeting the spec *is*
  `IsFlatLCDM`.
-/

namespace Checked.Fidelity

open Real Filter Topology Checked.Cosmography Checked.Cosmography.Aviles

/-- (Verbatim from `Work.Fidelity.FriedmannBlind.FriedmannLCDM`, blind textbook spec.)
Near `t₀`, `a` solves the flat dust + Λ Friedmann equation, the universe is
expanding at `t₀`, and `Ω` is the present matter density parameter
`ρ_m(t₀) / ρ_crit(t₀)` with `ρ_crit = H₀²` (units `c = 1`, `8πG/3 = 1`). -/
def FriedmannLCDM (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ∃ (ρ : ℝ → ℝ) (Λ : ℝ),
    (∀ᶠ t in nhds t₀,
        0 < a t ∧
        DifferentiableAt ℝ a t ∧
        -- dust continuity equation, integrated: ρ_m a³ = const
        ρ t * a t ^ 3 = ρ t₀ * a t₀ ^ 3 ∧
        -- flat Friedmann equation with 8πG/3 = 1:  H² = ρ_m + Λ/3
        (deriv a t / a t) ^ 2 = ρ t + Λ / 3) ∧
    -- expanding at t₀
    0 < deriv a t₀ ∧
    -- Ω = ρ_m(t₀) / ρ_crit(t₀), ρ_crit(t₀) = H₀² = (ȧ(t₀)/a(t₀))²
    Ω = ρ t₀ / (deriv a t₀ / a t₀) ^ 2

/-! ## Helpers -/

lemma fr_one_add_redshift {a : ℝ → ℝ} {t₀ t : ℝ} : 1 + redshift a t₀ t = a t₀ / a t := by
  simp [redshift]

/-- If `a` is continuous at `t₀` with `a t₀ > 0`, the radicand `Ω (a₀/a)³ + 1 − Ω` is
eventually positive. -/
lemma fr_radicand_pos (Ω : ℝ) {a : ℝ → ℝ} {t₀ : ℝ} (ha : 0 < a t₀) (hc : ContinuousAt a t₀) :
    ∀ᶠ t in 𝓝 t₀, 0 < Ω * (a t₀ / a t) ^ 3 + 1 - Ω := by
  have h : ContinuousAt (fun t => Ω * (a t₀ / a t) ^ 3 + 1 - Ω) t₀ :=
    ((continuousAt_const.mul ((continuousAt_const.div hc ha.ne').pow 3)).add
      continuousAt_const).sub continuousAt_const
  have h1 : (fun t => Ω * (a t₀ / a t) ^ 3 + 1 - Ω) t₀ = 1 := by
    simp [div_self ha.ne']
  exact h.eventually (lt_mem_nhds (by rw [h1]; exact one_pos))

/-! ## The equivalence -/

theorem isFlatLCDM_to_friedmann {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h : IsFlatLCDM Ω a t₀) :
    FriedmannLCDM Ω a t₀ := by
  obtain ⟨hH₀, hev⟩ := h
  obtain ⟨ha₀, hd₀, -⟩ := hev.self_of_nhds
  set H₀ := hubble a t₀ with hH₀def
  have hH₀ne : H₀ ≠ 0 := hH₀.ne'
  refine ⟨fun t => Ω * H₀ ^ 2 * (a t₀ / a t) ^ 3, 3 * ((1 - Ω) * H₀ ^ 2), ?_, ?_, ?_⟩
  · filter_upwards [hev, fr_radicand_pos Ω ha₀ hd₀.continuousAt] with t ⟨hat, hdt, hlaw⟩ hR
    refine ⟨hat, hdt, ?_, ?_⟩
    · field_simp
    · have e : deriv a t / a t = H₀ * √(Ω * (a t₀ / a t) ^ 3 + 1 - Ω) := by
        rw [← fr_one_add_redshift]; exact hlaw
      rw [e, mul_pow, Real.sq_sqrt hR.le]
      ring
  · have : 0 < deriv a t₀ / a t₀ := hH₀
    exact (div_pos_iff_of_pos_right ha₀).1 this
  · change Ω = Ω * H₀ ^ 2 * (a t₀ / a t₀) ^ 3 / H₀ ^ 2
    rw [div_self ha₀.ne']
    field_simp

theorem friedmann_to_isFlatLCDM {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h : FriedmannLCDM Ω a t₀) :
    IsFlatLCDM Ω a t₀ := by
  obtain ⟨ρ, Λ, hev, hexp, hΩ⟩ := h
  obtain ⟨ha₀, hd₀, -, hF₀⟩ := hev.self_of_nhds
  set H₀ := deriv a t₀ / a t₀ with hH₀def
  have hH₀ : 0 < H₀ := div_pos hexp ha₀
  have hρ₀ : ρ t₀ = Ω * H₀ ^ 2 := by rw [hΩ]; field_simp
  -- the Friedmann law in redshift form: `H² = H₀² (Ω (a₀/a)³ + 1 − Ω)`
  have hsq : ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
      (deriv a t / a t) ^ 2 = H₀ ^ 2 * (Ω * (a t₀ / a t) ^ 3 + 1 - Ω) ∧
      0 < Ω * (a t₀ / a t) ^ 3 + 1 - Ω := by
    filter_upwards [hev, fr_radicand_pos Ω ha₀ hd₀.continuousAt] with t ⟨hat, hdt, hc, hF⟩ hR
    refine ⟨hat, hdt, ?_, hR⟩
    have hρt : ρ t = ρ t₀ * (a t₀ / a t) ^ 3 := by
      rw [div_pow, mul_div_assoc', ← hc]; field_simp
    rw [hF, hρt, hρ₀]
    have hF₀' : H₀ ^ 2 = Ω * H₀ ^ 2 + Λ / 3 := by rw [← hρ₀]; exact hF₀
    linear_combination -hF₀'
  -- a ball on which all of this holds
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hsq
  set s := Metric.ball t₀ ε with hs
  have hconv : Convex ℝ s := convex_ball t₀ ε
  have hderiv : ∀ x ∈ s, HasDerivWithinAt a (deriv a x) s x :=
    fun x hx => (hball x hx).2.1.hasDerivAt.hasDerivWithinAt
  have hne : ∀ x ∈ s, deriv a x ≠ 0 := by
    intro x hx h0
    obtain ⟨hax, -, e, hR⟩ := hball x hx
    rw [h0, zero_div] at e
    have : 0 < H₀ ^ 2 * (Ω * (a t₀ / a x) ^ 3 + 1 - Ω) := by positivity
    linarith [show (0 : ℝ) ^ 2 = 0 by norm_num]
  have hpos : ∀ x ∈ s, 0 < deriv a x := by
    rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hconv hderiv hne with h | h
    · exact absurd (h t₀ (Metric.mem_ball_self hε)) (not_lt.2 hexp.le)
    · exact h
  refine ⟨hH₀, ?_⟩
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  obtain ⟨hat, hdt, e, hR⟩ := hball t ht
  refine ⟨hat, hdt, ?_⟩
  have hHt : 0 < deriv a t / a t := div_pos (hpos t ht) hat
  change deriv a t / a t = H₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)
  rw [fr_one_add_redshift]
  rw [← Real.sqrt_sq hHt.le, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hH₀.le]

/-- **The program's flat ΛCDM predicate equals the blind textbook Friedmann formulation**, for
every `Ω`, every scale factor `a` and every `t₀`. -/
theorem isFlatLCDM_iff_friedmann (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    IsFlatLCDM Ω a t₀ ↔ FriedmannLCDM Ω a t₀ :=
  ⟨isFlatLCDM_to_friedmann, friedmann_to_isFlatLCDM⟩

/-! ## Two anchors outside the families of `FlatLCDMSpec` (from the run-1828Z adversary) -/

lemma fr_sq_law {H H₀ R : ℝ} (hH₀ : 0 < H₀) (hH : 0 < H) (h : H = H₀ * √R) :
    (H / H₀) ^ 2 = R := by
  have hs : √R = H / H₀ := by field_simp; linarith
  have hR : 0 < R := Real.sqrt_pos.1 (hs ▸ div_pos hH hH₀)
  rw [← hs, Real.sq_sqrt hR.le]

lemma fr_two_pt {c k y₁ y₂ : ℝ} (h0 : 0 < y₁) (h12 : y₁ < y₂) (h2 : y₂ < 1)
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

lemma fr_two_gt {p : ℝ → Prop} {t₀ : ℝ} (h : ∀ᶠ t in 𝓝 t₀, p t) :
    ∃ t₁ t₂, t₀ < t₂ ∧ t₂ < t₁ ∧ p t₁ ∧ p t₂ := by
  obtain ⟨t₁, h1, p1⟩ := h.exists_gt
  obtain ⟨t₂, h2, p2, h21⟩ := (h.and (gt_mem_nhds h1)).exists_gt
  exact ⟨t₁, t₂, h2, h21, p1, p2⟩

lemma fr_hubble_id (t : ℝ) : hubble id t = 1 / t := by simp [hubble]

/-- Milne `a = t` (empty open universe) is not flat ΛCDM at `t₀ = 1`, for any `Ω`. -/
theorem milne_notFlatLCDM (Ω : ℝ) : ¬ IsFlatLCDM Ω id 1 := by
  rintro ⟨-, hev⟩
  obtain ⟨t₁, t₂, h2, h21, ⟨-, -, e₁⟩, ⟨-, -, e₂⟩⟩ := fr_two_gt hev
  have p1 : 0 < t₁ := by linarith
  have p2 : 0 < t₂ := by linarith
  rw [fr_hubble_id, fr_hubble_id, redshift] at e₁ e₂
  simp only [id, add_sub_cancel] at e₁ e₂
  rw [div_one] at e₁ e₂
  have s₁ := fr_sq_law one_pos (by positivity : (0:ℝ) < 1 / t₁) e₁
  have s₂ := fr_sq_law one_pos (by positivity : (0:ℝ) < 1 / t₂) e₂
  simp only [div_one] at s₁ s₂
  have hy1 : 1 / t₁ < 1 / t₂ := one_div_lt_one_div_of_lt p2 h21
  have hy2 : 1 / t₂ < 1 := by rw [div_lt_one p2]; exact h2
  have := fr_two_pt (c := Ω) (k := -1) (by positivity) hy1 hy2 (by linear_combination -s₁)
    (by linear_combination -s₂)
  subst this
  have : (1 / t₁) ^ 2 < 1 := pow_lt_one₀ (by positivity) (hy1.trans hy2) (by norm_num)
  linarith

/-- Bouncing flat ΛCDM with negative matter density, `a = cosh^{2/3} t` (`H = (2/3) tanh t`). -/
noncomputable def coshBounce : ℝ → ℝ := fun t => Real.cosh t ^ (2 / 3 : ℝ)

lemma hasDerivAt_coshBounce (t : ℝ) :
    HasDerivAt coshBounce (Real.sinh t * (2 / 3) * Real.cosh t ^ ((2 / 3 : ℝ) - 1)) t :=
  (Real.hasDerivAt_cosh t).rpow_const (Or.inl (Real.cosh_pos t).ne')

lemma hubble_coshBounce (t : ℝ) : hubble coshBounce t = 2 / 3 * Real.sinh t / Real.cosh t := by
  have hc := Real.cosh_pos t
  unfold hubble
  rw [(hasDerivAt_coshBounce t).deriv, coshBounce, Real.rpow_sub hc, Real.rpow_one]
  have : 0 < Real.cosh t ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  field_simp

lemma coshBounce_cube (t : ℝ) : coshBounce t ^ 3 = Real.cosh t ^ 2 := by
  unfold coshBounce
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.cosh_pos t).le]; norm_num

/-- `cosh^{2/3}` is flat ΛCDM at every `t₀ > 0` with `Ω = −1/sinh² t₀ < 0`. -/
theorem coshBounce_isFlatLCDM {t₀ : ℝ} (h₀ : 0 < t₀) :
    IsFlatLCDM (-1 / Real.sinh t₀ ^ 2) coshBounce t₀ := by
  have hs0 : 0 < Real.sinh t₀ := Real.sinh_pos_iff.2 h₀
  have hc0 : 0 < Real.cosh t₀ := Real.cosh_pos t₀
  refine ⟨by rw [hubble_coshBounce]; positivity, ?_⟩
  filter_upwards [lt_mem_nhds h₀] with t ht
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.2 ht
  have hc : 0 < Real.cosh t := Real.cosh_pos t
  refine ⟨Real.rpow_pos_of_pos hc _, (hasDerivAt_coshBounce t).differentiableAt, ?_⟩
  rw [hubble_coshBounce, hubble_coshBounce, redshift, add_sub_cancel]
  have e0 : 0 < coshBounce t₀ := Real.rpow_pos_of_pos hc0 _
  have e1 : 0 < coshBounce t := Real.rpow_pos_of_pos hc _
  have harg : -1 / Real.sinh t₀ ^ 2 * (coshBounce t₀ / coshBounce t) ^ 3 + 1 -
      -1 / Real.sinh t₀ ^ 2 =
      (Real.cosh t₀ * Real.sinh t / (Real.sinh t₀ * Real.cosh t)) ^ 2 := by
    rw [div_pow, coshBounce_cube, coshBounce_cube]
    have h1 := Real.cosh_sq t₀
    have h2 := Real.cosh_sq t
    field_simp
    linear_combination (Real.cosh t₀ ^ 2) * h2 - (Real.cosh t ^ 2) * h1
  rw [harg, Real.sqrt_sq (by positivity)]
  field_simp

/-! ## The strengthened specification and the pinning theorem -/

/-- `FlatLCDMSpec` plus the blind first-principles Friedmann law and two anchors outside the
original anchor families. -/
structure FlatLCDMSpec2 (P : ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop extends FlatLCDMSpec P where
  /-- First-principles law: flat GR Friedmann equation with dust + Λ, expanding, `Ω` the
  present matter density parameter (blind spec `FriedmannLCDM`). -/
  friedmann : ∀ Ω a t₀, P Ω a t₀ ↔ FriedmannLCDM Ω a t₀
  /-- Near miss: the empty open (Milne) universe `a = t` is not flat ΛCDM, whatever `Ω`
  (kills "flatness forgotten" and cosmographic `q₀` stand-ins). -/
  milne : ∀ Ω : ℝ, ¬ P Ω id 1
  /-- Positive anchor with `Ω < 0`: the bounce `cosh^{2/3} t` (kills `Ω ≥ 0` restrictions). -/
  bounce : ∀ t₀ : ℝ, 0 < t₀ → P (-1 / Real.sinh t₀ ^ 2) coshBounce t₀

theorem isFlatLCDM_meets_spec2 : FlatLCDMSpec2 IsFlatLCDM where
  toFlatLCDMSpec := isFlatLCDM_meets_spec
  friedmann := isFlatLCDM_iff_friedmann
  milne := milne_notFlatLCDM
  bounce _ h := coshBounce_isFlatLCDM h

/-- **No gap in `FlatLCDMSpec2`:** every predicate meeting it is `IsFlatLCDM`. -/
theorem flatLCDMSpec2_pins (P : ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatLCDMSpec2 P) :
    P = IsFlatLCDM := by
  funext Ω a t₀
  exact propext ((h.friedmann Ω a t₀).trans (isFlatLCDM_iff_friedmann Ω a t₀).symm)

/-- Corollary: the blind textbook formulation satisfies every closed-form anchor and near miss of
`FlatLCDMSpec` (written by a different subagent in run 1828Z) and the two new anchors, so those
anchors also test the blind spec. -/
theorem friedmann_meets_spec2 : FlatLCDMSpec2 FriedmannLCDM := by
  have e : FriedmannLCDM = IsFlatLCDM := by
    funext Ω a t₀; exact propext (isFlatLCDM_iff_friedmann Ω a t₀).symm
  rw [e]; exact isFlatLCDM_meets_spec2

end Checked.Fidelity
