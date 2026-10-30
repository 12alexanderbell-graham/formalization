import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Checked.Fidelity.FriedmannLCDM
import Checked.Cosmography.CPLCoefficients

/-!
# `IsFlatCPL` pinned by a blind first-principles formulation (trust track T1)

`Checked.Cosmography.CPL.IsFlatCPL Ω w₀ wₐ a t₀` (the model hypothesis behind finding F2) is
Capozziello–Lazkoz–Salzano's Eq. (17): `H = H₀ √(Ω(1+z)³ + (1−Ω)(1+z)^{3(1+w₀+wₐ)}
exp(−3wₐ z/(1+z)))` near `t₀`, `H₀ > 0`.

`FriedmannCPL` is copied **verbatim** from `Work/Fidelity/BlindSpecs3.lean` (frozen in commit
f15af15), written by a subagent that read no repository definition: flat Friedmann equation
with dust and a separately conserved dark-energy fluid whose equation of state is
`w = w₀ + wₐ z/(1+z)`, the dark-energy continuity equation in *differential* form. Referee
`runs/2026-10-30T2028Z/referee_friedmannCPL.md`: STANDS.

`isFlatCPL_iff_friedmannCPL`: the two are equivalent for every `Ω, w₀, wₐ, a, t₀`. The backward
direction integrates the continuity equation (the ratio of `ρ_de` to the closed-form solution
has zero derivative on a ball) and fixes the sign of `H` near `t₀` by Darboux's theorem.
`flatCPL_pins`: any predicate equivalent to the blind formulation is `IsFlatCPL`.
-/

namespace Checked.Fidelity

open Real Filter Topology Checked.Cosmography Checked.Cosmography.CPL

/-- (Verbatim from `Work.Fidelity.Blind3.FriedmannCPL`, blind spec.) `FriedmannCPL Ω w₀ wₐ a t₀`: near `t₀`, `a` solves the flat Friedmann equation
(units `8πG/3 = 1`) `H² = ρ_m + ρ_de` with
* pressureless matter, `ρ_m a³ = const` [Ryd16, eq. (5.7)];
* a dark-energy fluid with CPL equation of state `w(z) = w₀ + wₐ z/(1+z)`, `z` measured from
  `t₀` [CP01; Lin03, eq. (3)]; since `z/(1+z) = 1 − a(t)/a(t₀)` this is
  `w = w₀ + wₐ (1 − a(t)/a(t₀))`, i.e. `w(a) = w₀ + wₐ(1 − a/a₀)`;
  separately conserved: `ρ̇_de + 3H(1 + w)ρ_de = 0` [Wei08, eq. (1.5.18)];
* the universe expanding at `t₀` (`ȧ(t₀) > 0`);
* `Ω = ρ_m(t₀) / ρ_crit(t₀) = ρ_m(t₀) / H₀²` (with `8πG/3 = 1`, `ρ_crit = H²`).

No sign is imposed on `Ω`, `w₀`, `wₐ` or the densities. Junk values are excluded: `a > 0`
and differentiable on a neighbourhood (so `deriv a` is the true derivative and `H` has no
zero denominator), and the expansion condition makes `H₀ > 0` so `Ω`'s defining quotient
is well-posed. -/
def FriedmannCPL (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ∃ ρm ρde : ℝ → ℝ,
    (∀ᶠ t in 𝓝 t₀,
      0 < a t ∧
      DifferentiableAt ℝ a t ∧
      -- flat Friedmann equation, 8πG/3 = 1
      (deriv a t / a t) ^ 2 = ρm t + ρde t ∧
      -- pressureless matter: ρ_m a³ conserved
      ρm t * a t ^ 3 = ρm t₀ * a t₀ ^ 3 ∧
      -- dark-energy continuity equation with CPL w(t) = w₀ + wₐ z/(1+z), z/(1+z) = 1 − a/a₀
      HasDerivAt ρde
        (-(3 * (deriv a t / a t) * (1 + (w₀ + wₐ * (1 - a t / a t₀))) * ρde t)) t) ∧
    -- expanding at t₀
    0 < deriv a t₀ ∧
    -- present matter density parameter
    Ω = ρm t₀ / (deriv a t₀ / a t₀) ^ 2

/-! ## The closed-form dark-energy factor -/

/-- `(a₀/a)^{3(1+w₀+wₐ)} exp(3wₐ(a/a₀ − 1))`: the solution of the CPL continuity equation
normalised to `1` at `t₀`. -/
noncomputable def cplG (w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ s : ℝ) : ℝ :=
  (a t₀ / a s) ^ (3 * (1 + w₀ + wₐ)) * Real.exp (3 * wₐ * (a s / a t₀ - 1))

lemma cplG_pos {w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ s : ℝ} (h0 : 0 < a t₀) (hs : 0 < a s) :
    0 < cplG w₀ wₐ a t₀ s :=
  mul_pos (Real.rpow_pos_of_pos (div_pos h0 hs) _) (Real.exp_pos _)

lemma cplG_self {w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ} (h0 : 0 < a t₀) : cplG w₀ wₐ a t₀ t₀ = 1 := by
  simp [cplG, div_self h0.ne']

/-- The redshift form of Capozziello–Lazkoz–Salzano's dark-energy factor equals `cplG`. -/
lemma cplG_eq {w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ s : ℝ} (h0 : 0 < a t₀) (hs : 0 < a s) :
    (1 + redshift a t₀ s) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * redshift a t₀ s) / (1 + redshift a t₀ s)) = cplG w₀ wₐ a t₀ s := by
  have e : 1 + redshift a t₀ s = a t₀ / a s := by simp [redshift]
  rw [e, cplG]
  congr 2
  simp only [redshift]
  have := h0.ne'; have := hs.ne'
  field_simp
  ring

lemma cplG_hasDerivAt {w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ t d : ℝ} (h0 : 0 < a t₀) (ht : 0 < a t)
    (hd : HasDerivAt a d t) :
    HasDerivAt (cplG w₀ wₐ a t₀)
      (-(3 * (d / a t) * (1 + (w₀ + wₐ * (1 - a t / a t₀))) * cplG w₀ wₐ a t₀ t)) t := by
  have hu : HasDerivAt (fun s => a t₀ / a s) ((0 * a t - a t₀ * d) / a t ^ 2) t :=
    (hasDerivAt_const t (a t₀)).div hd ht.ne'
  have hune : a t₀ / a t ≠ 0 := (div_pos h0 ht).ne'
  have hp := hu.rpow_const (p := 3 * (1 + w₀ + wₐ)) (Or.inl hune)
  have he := (((hd.div_const (a t₀)).sub_const 1).const_mul (3 * wₐ)).exp
  have hm := hp.mul he
  refine hm.congr_deriv ?_
  rw [Real.rpow_sub_one hune]
  simp only [cplG]
  have := h0.ne'; have := ht.ne'
  field_simp
  ring

/-! ## The equivalence -/

theorem isFlatCPL_to_friedmannCPL {Ω w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : IsFlatCPL Ω w₀ wₐ a t₀) : FriedmannCPL Ω w₀ wₐ a t₀ := by
  obtain ⟨hH₀, hev⟩ := h
  obtain ⟨ha₀, hd₀, -⟩ := hev.self_of_nhds
  set H₀ := hubble a t₀ with hH₀def
  have hH₀ne : H₀ ≠ 0 := hH₀.ne'
  set K : ℝ → ℝ := fun s => Ω * (a t₀ / a s) ^ 3 + (1 - Ω) * cplG w₀ wₐ a t₀ s with hK
  have hKc : ContinuousAt K t₀ :=
    (continuousAt_const.mul ((continuousAt_const.div hd₀.continuousAt ha₀.ne').pow 3)).add
      (continuousAt_const.mul (cplG_hasDerivAt (w₀ := w₀) (wₐ := wₐ) ha₀ ha₀
        hd₀.hasDerivAt).continuousAt)
  have hK0 : K t₀ = 1 := by simp [hK, cplG_self ha₀, div_self ha₀.ne']
  have hKpos : ∀ᶠ s in 𝓝 t₀, 0 < K s := hKc.eventually (lt_mem_nhds (by rw [hK0]; exact one_pos))
  refine ⟨fun s => Ω * H₀ ^ 2 * (a t₀ / a s) ^ 3,
    fun s => (1 - Ω) * H₀ ^ 2 * cplG w₀ wₐ a t₀ s, ?_, ?_, ?_⟩
  · filter_upwards [hev, hKpos] with t ⟨hat, hdt, hlaw⟩ hKt
    refine ⟨hat, hdt, ?_, ?_, ?_⟩
    · have e1 : (1 + redshift a t₀ t) ^ 3 = (a t₀ / a t) ^ 3 := by simp [redshift]
      rw [e1, mul_assoc (1 - Ω), cplG_eq ha₀ hat] at hlaw
      have hlaw' : deriv a t / a t = H₀ * √(K t) := hlaw
      rw [hlaw', mul_pow, Real.sq_sqrt hKt.le]
      simp only [hK]; ring
    · have := hat.ne'; have := ha₀.ne'
      field_simp
    · have hG := cplG_hasDerivAt (w₀ := w₀) (wₐ := wₐ) ha₀ hat hdt.hasDerivAt
      exact (hG.const_mul ((1 - Ω) * H₀ ^ 2)).congr_deriv (by ring)
  · exact (div_pos_iff_of_pos_right ha₀).1 hH₀
  · change Ω = Ω * H₀ ^ 2 * (a t₀ / a t₀) ^ 3 / H₀ ^ 2
    rw [div_self ha₀.ne']
    field_simp

theorem friedmannCPL_to_isFlatCPL {Ω w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : FriedmannCPL Ω w₀ wₐ a t₀) : IsFlatCPL Ω w₀ wₐ a t₀ := by
  obtain ⟨ρm, ρde, hev, hexp, hΩ⟩ := h
  obtain ⟨ha₀, hd₀, hF₀, -, -⟩ := hev.self_of_nhds
  set H₀ := deriv a t₀ / a t₀ with hH₀def
  have hH₀ : 0 < H₀ := div_pos hexp ha₀
  have hρm₀ : ρm t₀ = Ω * H₀ ^ 2 := by rw [hΩ]; field_simp
  have hρde₀ : ρde t₀ = (1 - Ω) * H₀ ^ 2 := by
    have : H₀ ^ 2 = ρm t₀ + ρde t₀ := hF₀
    rw [hρm₀] at this; linarith
  set K : ℝ → ℝ := fun s => Ω * (a t₀ / a s) ^ 3 + (1 - Ω) * cplG w₀ wₐ a t₀ s with hK
  have hKc : ContinuousAt K t₀ :=
    (continuousAt_const.mul ((continuousAt_const.div hd₀.continuousAt ha₀.ne').pow 3)).add
      (continuousAt_const.mul (cplG_hasDerivAt (w₀ := w₀) (wₐ := wₐ) ha₀ ha₀
        hd₀.hasDerivAt).continuousAt)
  have hK0 : K t₀ = 1 := by simp [hK, cplG_self ha₀, div_self ha₀.ne']
  have hKpos : ∀ᶠ s in 𝓝 t₀, 0 < K s := hKc.eventually (lt_mem_nhds (by rw [hK0]; exact one_pos))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hev.and hKpos)
  set s := Metric.ball t₀ ε with hs
  have ht₀s : t₀ ∈ s := Metric.mem_ball_self hε
  -- integrate the continuity equation: `ρ_de / cplG` is constant on the ball
  have hQ : ∀ x ∈ s, HasDerivAt (fun y => ρde y / cplG w₀ wₐ a t₀ y) 0 x := by
    intro x hx
    obtain ⟨⟨hax, hdx, -, -, hρ⟩, -⟩ := hball x hx
    have hG := cplG_hasDerivAt (w₀ := w₀) (wₐ := wₐ) ha₀ hax hdx.hasDerivAt
    have hGne := (cplG_pos (w₀ := w₀) (wₐ := wₐ) ha₀ hax).ne'
    refine (hρ.div hG hGne).congr_deriv ?_
    field_simp
    ring
  have hconst : ∀ x ∈ s, ρde x / cplG w₀ wₐ a t₀ x = ρde t₀ / cplG w₀ wₐ a t₀ t₀ := by
    intro x hx
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball t₀ ε).isPreconnected
      (fun y hy => (hQ y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hQ y hy).deriv) hx ht₀s
  -- the Friedmann law in redshift form
  have hsq : ∀ x ∈ s, (deriv a x / a x) ^ 2 = H₀ ^ 2 * K x := by
    intro x hx
    obtain ⟨⟨hax, -, hF, hm, -⟩, -⟩ := hball x hx
    have hρde : ρde x = (1 - Ω) * H₀ ^ 2 * cplG w₀ wₐ a t₀ x := by
      have := hconst x hx
      rw [cplG_self ha₀, div_one, hρde₀,
        div_eq_iff (cplG_pos (w₀ := w₀) (wₐ := wₐ) ha₀ hax).ne'] at this
      rw [this]
    have hρm : ρm x = Ω * H₀ ^ 2 * (a t₀ / a x) ^ 3 := by
      have := hax.ne'
      rw [← hρm₀, div_pow, mul_div_assoc', ← hm]; field_simp
    rw [hF, hρde, hρm]; simp only [hK]; ring
  -- sign of `H` on the ball (Darboux)
  have hne : ∀ x ∈ s, deriv a x ≠ 0 := by
    intro x hx h0
    have e := hsq x hx
    obtain ⟨-, hKx⟩ := hball x hx
    rw [h0, zero_div] at e
    have : 0 < H₀ ^ 2 * K x := by positivity
    linarith [show (0 : ℝ) ^ 2 = 0 by norm_num]
  have hpos : ∀ x ∈ s, 0 < deriv a x := by
    rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_ball t₀ ε)
      (fun x hx => (hball x hx).1.2.1.hasDerivAt.hasDerivWithinAt) hne with h | h
    · exact absurd (h t₀ ht₀s) (not_lt.2 hexp.le)
    · exact h
  refine ⟨hH₀, ?_⟩
  filter_upwards [Metric.ball_mem_nhds t₀ hε] with t ht
  obtain ⟨⟨hat, hdt, -, -, -⟩, hKt⟩ := hball t ht
  refine ⟨hat, hdt, ?_⟩
  have e1 : (1 + redshift a t₀ t) ^ 3 = (a t₀ / a t) ^ 3 := by simp [redshift]
  rw [e1, mul_assoc (1 - Ω), cplG_eq ha₀ hat]
  change deriv a t / a t = H₀ * √(K t)
  have hHt : 0 < deriv a t / a t := div_pos (hpos t ht) hat
  rw [← Real.sqrt_sq hHt.le, hsq t ht, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hH₀.le]

/-- **The program's flat CPL predicate equals the blind first-principles formulation**, for
every `Ω, w₀, wₐ`, every scale factor and every `t₀`. -/
theorem isFlatCPL_iff_friedmannCPL (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    IsFlatCPL Ω w₀ wₐ a t₀ ↔ FriedmannCPL Ω w₀ wₐ a t₀ :=
  ⟨isFlatCPL_to_friedmannCPL, friedmannCPL_to_isFlatCPL⟩

/-- **Pinning:** any predicate obeying the blind first-principles law is `IsFlatCPL`. -/
theorem flatCPL_pins (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop)
    (h : ∀ Ω w₀ wₐ a t₀, P Ω w₀ wₐ a t₀ ↔ FriedmannCPL Ω w₀ wₐ a t₀) : P = IsFlatCPL := by
  funext Ω w₀ wₐ a t₀
  exact propext ((h Ω w₀ wₐ a t₀).trans (isFlatCPL_iff_friedmannCPL Ω w₀ wₐ a t₀).symm)

end Checked.Fidelity
