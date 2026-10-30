import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Checked.Cosmography.FRCosmo

/-!
# The F(R) cosmology definitions pinned by a blind specification (trust track T1)

`Checked.Cosmography.FRCosmo` (findings F9, F10) uses `curv` (Ricci scalar, review convention
`R = −6(Ḣ + 2H²)`), `rhoM` (dust density), `FriedmannEq` (expansion-rate equation (11.1)–(11.2)
multiplied by `3F′`) and `MasterEq` ((11.5) multiplied by `−2F′`). The specification below is
copied **verbatim** from `Work/Fidelity/BlindFR.lean` (frozen in commit ff9272f), written by a
subagent that read no repository definition, who derived the FLRW equations of metric F(R)
gravity from the field equations and mapped them to the review's sign convention (`R = −R_c`,
`F(R) = −f(−R)`; ΛCDM is `F = R + 2Λ`, as the review states). Referee
`runs/2026-10-30T2028Z/referee_FR.md`: STANDS (sympy re-derivation; both equations match
term by term). (The blind file's unused helper `hubble` is not copied.)

* `curv_meets_spec`, `ricciSpec_pins`: any `Rc` meeting `RicciFlatFLRWSpec` is `curv` wherever
  `a > 0` is twice differentiable.
* `rhoM_eq_dust`: `rhoM = DustDensity`.
* `friedmannEq_iff_blind`, `masterEq_iff_blind`: the program's field equations are the blind
  ones with `R = curv a`, at every time, for every `F`.
-/

namespace Checked.Fidelity

open Real Filter Topology Checked.Cosmography Checked.Cosmography.FRCosmo

/-- Specification of the Ricci scalar of a spatially flat FLRW metric with scale factor `a`
(function of cosmic time), in the **negative** convention: `Rc a t = −6 (ä/a + (ȧ/a)²)`,
so that de Sitter (`a = c·e^{ht}`) has `R = −12 h²`.  In the common convention
(`R_c = +6(ä/a + (ȧ/a)²)`) this is `R = −R_c`.

* `law` determines `Rc a t` whenever `a(t) > 0` and `a` is twice differentiable at `t`, given
  as: `a` has derivative `a' s` at every `s` near `t`, and `a'` has derivative `a''t` at `t`
  (explicit derivative functions, so no `deriv` junk values enter).
* anchors: de Sitter, radiation `a = t^{1/2}` (`R = 0`, conformal/traceless source),
  matter `a = t^{2/3}` (`R = −4/(3t²)`; in common convention `R_c = 4/(3t²) = ρ` for
  Einstein–de Sitter with `κ² = 1`, as `R_c = κ²(ρ − 3p)`).
* invariances: rescaling `a ↦ c·a` (`c > 0`), and time translation. -/
structure RicciFlatFLRWSpec (Rc : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Determining law: `R = −6 (ä/a + (ȧ/a)²)`. -/
  law : ∀ (a a' a'' : ℝ → ℝ) (t : ℝ), 0 < a t →
    (∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) → HasDerivAt a' (a'' t) t →
    Rc a t = -6 * (a'' t / a t + (a' t / a t) ^ 2)
  /-- de Sitter anchor: `a = c·e^{h t}` has `R = −12 h²`. -/
  deSitter : ∀ (c h t : ℝ), 0 < c → Rc (fun s => c * Real.exp (h * s)) t = -12 * h ^ 2
  /-- Radiation anchor: `a = t^{1/2}` has `R = 0` for `t > 0`. -/
  radiation : ∀ t : ℝ, 0 < t → Rc (fun s => s ^ (1 / 2 : ℝ)) t = 0
  /-- Matter (Einstein–de Sitter) anchor: `a = t^{2/3}` has `R = −4/(3t²)` for `t > 0`. -/
  matter : ∀ t : ℝ, 0 < t → Rc (fun s => s ^ (2 / 3 : ℝ)) t = -4 / (3 * t ^ 2)
  /-- Invariance under constant rescaling of the scale factor (normalization of `a` is
  unphysical in flat FLRW). Stated under the same regularity hypotheses as `law`. -/
  scale_invariant : ∀ (a a' a'' : ℝ → ℝ) (c t : ℝ), 0 < c → 0 < a t →
    (∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) → HasDerivAt a' (a'' t) t →
    Rc (fun s => c * a s) t = Rc a t
  /-- Invariance under time translation. Stated under the regularity hypotheses of `law`
  at the shifted time `t + τ`. -/
  time_translation : ∀ (a a' a'' : ℝ → ℝ) (τ t : ℝ), 0 < a (t + τ) →
    (∀ᶠ s in 𝓝 (t + τ), HasDerivAt a (a' s) s) → HasDerivAt a' (a'' (t + τ)) (t + τ) →
    Rc (fun s => a (s + τ)) t = Rc a (t + τ)

/-- Matter (dust) density at time `t`, for dust whose present (`t = t₀`) density parameter is
`Ω`, measured relative to the **GR** critical density with `κ² = 1`, i.e.
`ρ_crit = 3 H₀²` with `H₀ = ȧ(t₀)/a(t₀)` (from `3H² = κ²ρ`).

Closed form: `ρ(t) = 3 H₀² Ω (a(t₀)/a(t))³`.
Why: dust has `p = 0`; in metric F(R) gravity matter is minimally coupled, so `∇^μ T_μν = 0`
still holds (the geometric side is identically divergence free by the generalized Bianchi
identity), giving `ρ̇ + 3H(ρ + p) = 0`, i.e. `ρ a³ = const`, and `ρ(t₀) = Ω ρ_crit`.
Note: `Ω` is *not* the fraction of the F(R) "effective" critical density `3F′(R₀)H₀²`;
it is the GR-normalized parameter. -/
noncomputable def DustDensity (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  3 * (deriv a t₀ / a t₀) ^ 2 * Ω * (a t₀ / a t) ^ 3

/-- The 00 (Friedmann / constraint) component of the metric F(R) field equations in flat FLRW,
dust source, `κ² = 1`, **negative-R convention** (de Sitter `R = −12H²`), at time `t`:

`3 F′(R) H² = ρ + ½ (F(R) − R F′(R)) − 3 H F″(R) Ṙ`,

with `H = ȧ/a`, `ρ = DustDensity Ω a t₀ t`, `R = R(t)` supplied by the caller (intended
`R = Rc a`).  Derived from De Felice–Tsujikawa (2.15),
`3F′H² = κ²ρ + ½(F′R_c − f) − 3H d(F′)/dt`, via `R = −R_c`, `F(R) = −f(−R)` (see module
docstring).  Multiplied through by `F′` (no division by `F′`).
Checks: `F = R` gives `3H² = ρ`; `F = R + 2Λ` gives `3H² = ρ + Λ` (ΛCDM). -/
def FRFirstEq (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) (R : ℝ → ℝ) : Prop :=
  3 * deriv F (R t) * (deriv a t / a t) ^ 2 =
    DustDensity Ω a t₀ t + (F (R t) - R t * deriv F (R t)) / 2
      - 3 * (deriv a t / a t) * deriv^[2] F (R t) * deriv R t

/-- The `Ḣ` equation (00 + ii combination) of metric F(R) gravity in flat FLRW, dust source
(`p = 0`), `κ² = 1`, **negative-R convention**, at time `t`:

`−2 F′(R) Ḣ = ρ + F‴(R) Ṙ² + F″(R) R̈ − H F″(R) Ṙ`,

i.e. `−2F′Ḣ = κ²(ρ + p) + d²F′/dt² − H dF′/dt` (De Felice–Tsujikawa (2.16)), where
`d F′/dt = F″ Ṙ` and `d² F′/dt² = F‴ Ṙ² + F″ R̈` are the same in both sign conventions.
`Ḣ` is written as the derivative of `s ↦ ȧ(s)/a(s)`.  No division by `F′`.
Checks: `F = R` gives the Raychaudhuri equation `−2Ḣ = ρ`; same for `F = R + 2Λ`. -/
def FRSecondEq (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) (R : ℝ → ℝ) : Prop :=
  -2 * deriv F (R t) * deriv (fun s => deriv a s / a s) t =
    DustDensity Ω a t₀ t + deriv^[3] F (R t) * (deriv R t) ^ 2
      + deriv^[2] F (R t) * deriv^[2] R t
      - (deriv a t / a t) * deriv^[2] F (R t) * deriv R t

/-! ## Proofs -/

/-- `curv` from explicit derivatives. -/
lemma curv_eq_of {a a' : ℝ → ℝ} {a'' t : ℝ} (ha : 0 < a t)
    (h1 : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) (h2 : HasDerivAt a' a'' t) :
    curv a t = -6 * (a'' / a t + (a' t / a t) ^ 2) := by
  have hat : HasDerivAt a (a' t) t := h1.self_of_nhds
  have hH : HasDerivAt (fun s => a' s / a s) ((a'' * a t - a' t * a' t) / a t ^ 2) t :=
    h2.div hat ha.ne'
  have heq : hubble a =ᶠ[𝓝 t] fun s => a' s / a s := by
    filter_upwards [h1] with s hs
    simp only [hubble, hs.deriv]
  have hd : deriv (hubble a) t = (a'' * a t - a' t * a' t) / a t ^ 2 :=
    (hH.congr_of_eventuallyEq heq).deriv
  have hh : hubble a t = a' t / a t := by simp only [hubble, hat.deriv]
  simp only [curv, hd, hh]
  have := ha.ne'
  field_simp
  ring

lemma curv_rpow (p t : ℝ) (ht : 0 < t) :
    curv (fun s => s ^ p) t = -6 * (p * (p - 1) + p ^ 2) / t ^ 2 := by
  have h1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => s ^ p) (p * s ^ (p - 1)) s := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact Real.hasDerivAt_rpow_const (Or.inl hs.ne')
  have h2 : HasDerivAt (fun s => p * s ^ (p - 1)) (p * ((p - 1) * t ^ (p - 1 - 1))) t :=
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul p
  rw [curv_eq_of (a := fun s => s ^ p) (t := t) (Real.rpow_pos_of_pos ht p) h1 h2]
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  rw [Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_one]
  field_simp

theorem curv_meets_spec : RicciFlatFLRWSpec curv where
  law a a' a'' t ha h1 h2 := curv_eq_of ha h1 h2
  deSitter c h t hc := by
    have h1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => c * Real.exp (h * s))
        (c * (h * Real.exp (h * s))) s := by
      refine Eventually.of_forall fun s => ?_
      have := ((hasDerivAt_id s).const_mul h).exp.const_mul c
      simpa [mul_comm] using this
    have h2 : HasDerivAt (fun s => c * (h * Real.exp (h * s))) (c * (h * (h * Real.exp (h * t)))) t := by
      have := (((hasDerivAt_id t).const_mul h).exp.const_mul h).const_mul c
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    rw [curv_eq_of (a := fun s => c * Real.exp (h * s)) (t := t) (mul_pos hc (Real.exp_pos _)) h1 h2]
    have := Real.exp_pos (h * t)
    field_simp
    ring
  radiation t ht := by rw [curv_rpow _ t ht]; norm_num
  matter t ht := by
    rw [curv_rpow _ t ht]
    have : t ^ 2 ≠ 0 := by positivity
    field_simp
    norm_num
  scale_invariant a a' a'' c t hc ha h1 h2 := by
    have h1' : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => c * a s) (c * a' s) s :=
      h1.mono fun s hs => hs.const_mul c
    rw [curv_eq_of (a := fun s => c * a s) (t := t) (mul_pos hc ha) h1' (h2.const_mul c),
      curv_eq_of ha h1 h2]
    have := hc.ne'; have := ha.ne'
    field_simp
  time_translation a a' a'' τ t ha h1 h2 := by
    have hshift : Tendsto (fun s => s + τ) (𝓝 t) (𝓝 (t + τ)) := by
      simpa using (tendsto_id (x := 𝓝 t)).add_const τ
    have h1' : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => a (s + τ)) (a' (s + τ)) s := by
      filter_upwards [hshift.eventually h1] with s hs
      simpa using hs.comp_add_const s τ
    have h2' : HasDerivAt (fun s => a' (s + τ)) (a'' (t + τ)) t := by
      simpa using h2.comp_add_const t τ
    rw [curv_eq_of (a := fun s => a (s + τ)) (t := t) ha h1' h2', curv_eq_of ha h1 h2]

/-- **Pinning:** any `Rc` meeting `RicciFlatFLRWSpec` is `curv` wherever `a > 0` is twice
differentiable at `t`. -/
theorem ricciSpec_pins (Rc : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatFLRWSpec Rc) (a a' a'' : ℝ → ℝ)
    (t : ℝ) (ha : 0 < a t) (h1 : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s)
    (h2 : HasDerivAt a' (a'' t) t) : Rc a t = curv a t := by
  rw [h.law a a' a'' t ha h1 h2, curv_eq_of ha h1 h2]

/-- The program's dust density is the blind one. -/
theorem rhoM_eq_dust : rhoM = DustDensity := rfl

/-- The program's expansion-rate equation is the blind 00 equation with `R = curv a`. -/
theorem friedmannEq_iff_blind (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    FriedmannEq Ω a F t₀ t ↔ FRFirstEq Ω a F t₀ t (curv a) := by
  unfold FriedmannEq FRFirstEq
  rw [rhoM_eq_dust]
  simp only [hubble]
  constructor <;> intro h <;> linear_combination h

/-- The program's master equation is the blind `Ḣ` equation with `R = curv a`. -/
theorem masterEq_iff_blind (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) :
    MasterEq Ω a F t₀ t ↔ FRSecondEq Ω a F t₀ t (curv a) := by
  unfold MasterEq FRSecondEq
  rw [rhoM_eq_dust]
  have e : hubble a = fun s => deriv a s / a s := rfl
  simp only [e]
  constructor <;> intro h <;> linear_combination h

end Checked.Fidelity
