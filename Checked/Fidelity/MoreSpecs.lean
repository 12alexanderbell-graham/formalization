import Checked.Cosmography.BambaAngular
import Checked.Cosmography.LCDMWitness
import Checked.Fidelity.LumDistSpec

/-!
# Machine-checked fidelity: specifications for `hubble`, `decel`, `angDist`, `IsFlatLCDM`

Continuation of `Work/Fidelity/LumDistSpec.lean` (trust track T1). For each trusted definition
we state a `…Spec` structure of textbook anchors, written from standard cosmology independently of
the definition, and prove that the repo's definition meets it:

* `HubbleSpec`   for `Checked.Cosmography.hubble`        (`H = ȧ/a`);
* `DecelSpec`    for `Checked.Cosmography.decel`         (`q = −ä a/ȧ²`);
* `AngDistSpec`  for `Checked.Cosmography.BambaA.angDist` (`d_A = a(t_e) S_K(χ) = d_L/(1+z)²`);
* `FlatLCDMSpec` for `Checked.Cosmography.Aviles.IsFlatLCDM`
  (`H = H₀ √(Ω(1+z)³ + 1 − Ω)` near `t₀`, `H₀ > 0`): models that must satisfy it and near-miss
  models that must not.

Every anchor carries explicit physical hypotheses (positive scale factor, differentiability,
`ȧ ≠ 0`, past light cone `t ≤ t₀`, …); no anchor asks for a junk value of the definition
(e.g. `q` where `ȧ = 0`, `H` where `a` is not differentiable, `d_A` for `t > t₀` beyond exact
symmetries).

Conventions: `c = 1`; `t < t₀` is the past; `1 + z = a(t₀)/a(t)`; the curvature constant `K`
scales as `K ↦ c²K` under `a ↦ c a` (`S_K(χ) = sin(√K χ)/√K`, `χ`, `sinh(√−K χ)/√−K`).
-/

namespace Checked.Fidelity

open Filter Topology Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaY Checked.Cosmography.BambaK Checked.Cosmography.BambaA
open Checked.Cosmography.Transverse

/-! ## Specifications -/

/-- Specification of a Hubble-rate function `H a t` (scale factor `a`, cosmic time `t`). -/
structure HubbleSpec (H : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Definition as a logarithmic derivative, `H = d ln a/dt` (Weinberg, *Cosmology* §1.5;
  Hogg 1999, astro-ph/9905116, §3: `H = ȧ/a`), for a positive scale factor differentiable at `t`. -/
  logDeriv : ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → DifferentiableAt ℝ a t →
    HasDerivAt (fun s => Real.log (a s)) (H a t) t
  /-- de Sitter (expanding `h > 0`, contracting `h < 0`, static `h = 0`): `a = e^{ht}` has
  constant `H = h` at every time (Λ-only universe, Ryden, *Introduction to Cosmology*,
  ch. 5). -/
  deSitter : ∀ h t : ℝ, H (fun s => Real.exp (h * s)) t = h
  /-- Power law `a = tⁿ` (EdS `n = 2/3`, radiation `n = 1/2`, Milne `n = 1`): `H = n/t` at every
  `t > 0` (single-component universes, `w = 2/(3n) − 1`; Ryden ch. 5). -/
  powerLaw : ∀ n t : ℝ, 0 < t → H (fun s => s ^ n) t = n / t
  /-- Static universe (`a ≡ R > 0`): `H = 0`. -/
  static : ∀ R t : ℝ, 0 < R → H (fun _ => R) t = 0
  /-- The normalization of `a` is unphysical: `H[c a] = H[a]` (`c > 0`). -/
  rescale : ∀ c : ℝ, 0 < c → ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → DifferentiableAt ℝ a t →
    H (fun s => c * a s) t = H a t
  /-- The origin of time is unphysical: `H[a(· + τ)](t) = H[a](t + τ)`. -/
  translate : ∀ (τ : ℝ) (a : ℝ → ℝ) (t : ℝ), 0 < a (t + τ) → DifferentiableAt ℝ a (t + τ) →
    H (fun s => a (s + τ)) t = H a (t + τ)
  /-- Time reversal turns expansion into contraction: `H[a(−·)](t) = −H[a](−t)`. -/
  timeReverse : ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a (-t) → DifferentiableAt ℝ a (-t) →
    H (fun s => a (-s)) t = -H a (-t)

/-- Specification of a deceleration-parameter function `Q a t`. -/
structure DecelSpec (Q : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Textbook definition `q = −ä a/ȧ²` (Weinberg §1.5; Visser 2004, gr-qc/0309109) for a
  positive, twice-differentiable scale factor with `ȧ ≠ 0`, the derivatives given explicitly
  (`a' = ȧ` near `t`, `a'' = ä` at `t`). -/
  formula : ∀ (a a' : ℝ → ℝ) (a'' t : ℝ), (∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) →
    HasDerivAt a' a'' t → 0 < a t → a' t ≠ 0 → Q a t = -(a'' * a t) / a' t ^ 2
  /-- de Sitter `a = e^{ht}` (`h ≠ 0`, expanding or contracting): `q = −1` (Weinberg §1.5). -/
  deSitter : ∀ h t : ℝ, h ≠ 0 → Q (fun s => Real.exp (h * s)) t = -1
  /-- Power law `a = tⁿ`, `t > 0`: `q = (1 − n)/n` (EdS `q = 1/2`, radiation `q = 1`, Milne
  `q = 0`, `n > 1` accelerating). -/
  powerLaw : ∀ n t : ℝ, n ≠ 0 → 0 < t → Q (fun s => s ^ n) t = (1 - n) / n
  /-- Einstein–de Sitter `a = t^{2/3}`: `q = 1/2` at every `t > 0`. -/
  eds : ∀ t : ℝ, 0 < t → Q (fun s => s ^ (2 / 3 : ℝ)) t = 1 / 2
  /-- Contracting power law (big crunch) `a = (−t)ⁿ`, `t < 0`: `q = (1 − n)/n`, the same as the
  expanding one (`q` is even under time reversal). -/
  crunch : ∀ n t : ℝ, n ≠ 0 → t < 0 → Q (fun s => (-s) ^ n) t = (1 - n) / n
  /-- Normalization invariance `q[c a] = q[a]` (`c > 0`, `ȧ ≠ 0`). -/
  rescale : ∀ c : ℝ, 0 < c → ∀ (a : ℝ → ℝ) (t : ℝ), deriv a t ≠ 0 →
    Q (fun s => c * a s) t = Q a t
  /-- Time-translation invariance. -/
  translate : ∀ (τ : ℝ) (a : ℝ → ℝ) (t : ℝ), deriv a (t + τ) ≠ 0 →
    Q (fun s => a (s + τ)) t = Q a (t + τ)
  /-- Time-reversal invariance `q[a(−·)](t) = q[a](−t)` (`q` is quadratic in `d/dt`). -/
  timeReverse : ∀ (a : ℝ → ℝ) (t : ℝ), deriv a (-t) ≠ 0 →
    Q (fun s => a (-s)) t = Q a (-t)

/-- Specification of an angular-diameter-distance function `D K a t₀ t`. -/
structure AngDistSpec (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Flat FLRW: `d_A = a(t) χ`, `χ = ∫_t^{t₀} ds/a(s)` (Weinberg §1.4;
  Hogg 1999, §§5–6: `d_A = d_M/(1+z)`). Positive continuous `a` on the past light cone. -/
  flat : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    ContinuousOn a (Set.Icc t t₀) → D 0 a t₀ t = a t * ∫ s in t..t₀, 1 / a s
  /-- Closed FLRW (`K = 1`): `d_A = a(t) sin χ`. -/
  closed : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    ContinuousOn a (Set.Icc t t₀) → D 1 a t₀ t = a t * Real.sin (∫ s in t..t₀, 1 / a s)
  /-- Open FLRW (`K = −1`): `d_A = a(t) sinh χ`. -/
  «open» : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    ContinuousOn a (Set.Icc t t₀) → D (-1) a t₀ t = a t * Real.sinh (∫ s in t..t₀, 1 / a s)
  /-- Normalization invariance: `a ↦ c a`, `K ↦ c² K` leaves `d_A` unchanged. -/
  rescale : ∀ c : ℝ, 0 < c → ∀ K a t₀ t, D (c ^ 2 * K) (fun s => c * a s) t₀ t = D K a t₀ t
  /-- Time-translation invariance. -/
  translate : ∀ (τ K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ),
    D K (fun s => a (s + τ)) (t₀ - τ) (t - τ) = D K a t₀ t
  /-- Flat de Sitter (`a = eᵗ`, `t₀ = 0`, `H₀ = 1`): `d_A = z/(1+z) = 1 − eᵗ`
  (bounded by the Hubble radius). -/
  deSitter : ∀ t : ℝ, t ≤ 0 → D 0 Real.exp 0 t = 1 - Real.exp t
  /-- Contracting de Sitter (`a = e^{−t}`, blueshift): `d_A = a(t)(1 − eᵗ) = e^{−t} − 1`. -/
  deSitterContracting : ∀ t : ℝ, t ≤ 0 → D 0 (fun s => Real.exp (-s)) 0 t = Real.exp (-t) - 1
  /-- Milne (`a = t`, `K = −1`, `t₀ = 1`): `d_A = t sinh(ln(1/t)) = (1 − t²)/2`, i.e.
  `z(1 + z/2)/(1+z)²`. -/
  milne : ∀ t : ℝ, 0 < t → t ≤ 1 → D (-1) id 1 t = (1 - t ^ 2) / 2
  /-- Static closed universe of radius `R` (`a ≡ R`, `K = 1`): `d_A = R sin((t₀ − t)/R)`. -/
  staticClosed : ∀ R : ℝ, 0 < R → ∀ t₀ t : ℝ, t ≤ t₀ →
    D 1 (fun _ => R) t₀ t = R * Real.sin ((t₀ - t) / R)
  /-- Static flat universe (`a ≡ R`): `d_A = t₀ − t` (Euclidean). -/
  staticFlat : ∀ R : ℝ, 0 < R → ∀ t₀ t : ℝ, t ≤ t₀ → D 0 (fun _ => R) t₀ t = t₀ - t

/-- Specification of a "flat ΛCDM at `t₀` with matter fraction `Ω`" predicate `P Ω a t₀`. -/
structure FlatLCDMSpec (P : ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- Einstein–de Sitter `a = t^{2/3}` is flat ΛCDM with `Ω = 1` at every `t₀ > 0`
  (`H = 2/(3t)`, `H/H₀ = (1+z)^{3/2}`). -/
  eds : ∀ t₀ : ℝ, 0 < t₀ → P 1 (fun t => t ^ (2 / 3 : ℝ)) t₀
  /-- Expanding de Sitter `a = e^{ht}` (`h > 0`) is flat ΛCDM with `Ω = 0`, at every `t₀`. -/
  deSitter : ∀ h t₀ : ℝ, 0 < h → P 0 (fun t => Real.exp (h * t)) t₀
  /-- Matter + positive Λ: `a = sinh^{2/3} t` (closed form `a ∝ sinh^{2/3}((3/2)√(Λ/3) t)` with Einstein's Λ, units
  `(3/2)√(Λ/3) = 1`) is flat ΛCDM at `t₀ > 0` with `Ω = 1/cosh² t₀ ∈ (0,1)` (`H = (2/3) coth t`). -/
  lcdm : ∀ t₀ : ℝ, 0 < t₀ → P (1 / Real.cosh t₀ ^ 2) (fun t => Real.sinh t ^ (2 / 3 : ℝ)) t₀
  /-- Matter + negative Λ (`Ω > 1`): `a = sin^{2/3} t` (`H = (2/3) cot t`) is flat ΛCDM at
  `t₀ ∈ (0, π/2)` (expanding phase) with `Ω = 1/cos² t₀`. -/
  negLambda : ∀ t₀ : ℝ, 0 < t₀ → t₀ < Real.pi / 2 →
    P (1 / Real.cos t₀ ^ 2) (fun t => Real.sin t ^ (2 / 3 : ℝ)) t₀
  /-- Normalization invariance: `a ↦ c a` (`c > 0`) changes neither `H` nor `z`. -/
  rescale : ∀ c : ℝ, 0 < c → ∀ Ω a t₀, P Ω (fun t => c * a t) t₀ ↔ P Ω a t₀
  /-- Time-translation invariance. -/
  translate : ∀ (τ Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), P Ω a t₀ → P Ω (fun t => a (t + τ)) (t₀ - τ)
  /-- Necessary condition: the model is expanding with a positive scale factor at `t₀`. -/
  expanding : ∀ Ω a t₀, P Ω a t₀ → 0 < a t₀ ∧ 0 < deriv a t₀
  /-- Near miss: contracting de Sitter `a = e^{−ht}` obeys `H = H₀ · 1` but has `H₀ < 0`. -/
  contracting : ∀ Ω h t₀ : ℝ, 0 < h → ¬ P Ω (fun t => Real.exp (-h * t)) t₀
  /-- Near miss: EdS is flat ΛCDM only with `Ω = 1` (the condition at `t = t₀` alone is empty). -/
  edsOnlyOne : ∀ Ω t₀ : ℝ, 0 < t₀ → Ω ≠ 1 → ¬ P Ω (fun t => t ^ (2 / 3 : ℝ)) t₀
  /-- Near miss: de Sitter is flat ΛCDM only with `Ω = 0`. -/
  deSitterOnlyZero : ∀ Ω h t₀ : ℝ, 0 < h → Ω ≠ 0 → ¬ P Ω (fun t => Real.exp (h * t)) t₀
  /-- Near miss (one-sided neighbourhood): de Sitter in the past, coasting `a = 1 + t` in the
  future is not ΛCDM at `t₀ = 0` (the Friedmann equation must hold on both sides). -/
  notPastOnly : ¬ P 0 (fun t => if t ≤ 0 then Real.exp t else 1 + t) 0
  /-- Near miss (one-sided neighbourhood): coasting in the past, de Sitter in the future. -/
  notFutureOnly : ¬ P 0 (fun t => if t ≤ 0 then 1 + t else Real.exp t) 0

/-! ## `hubble` meets `HubbleSpec` -/

lemma ms_hasDerivAt_expMul (h t : ℝ) :
    HasDerivAt (fun s => Real.exp (h * s)) (h * Real.exp (h * t)) t := by
  have := ((hasDerivAt_id t).const_mul h).exp
  rw [show h * Real.exp (h * t) = Real.exp (h * t) * (h * 1) by ring]
  exact this

lemma ms_hubble_expMul (h t : ℝ) : hubble (fun s => Real.exp (h * s)) t = h := by
  unfold hubble
  rw [(ms_hasDerivAt_expMul h t).deriv]
  field_simp

lemma ms_hubble_rescale (c : ℝ) (hc : c ≠ 0) (a : ℝ → ℝ) (t : ℝ) :
    hubble (fun s => c * a s) t = hubble a t := by
  unfold hubble
  rw [deriv_const_mul_field, mul_div_mul_left _ _ hc]

lemma ms_hubble_translate (τ : ℝ) (a : ℝ → ℝ) (t : ℝ) :
    hubble (fun s => a (s + τ)) t = hubble a (t + τ) := by
  unfold hubble; rw [deriv_comp_add_const]

theorem hubble_meets_spec : HubbleSpec hubble where
  logDeriv a t ha hd := (hd.hasDerivAt.log ha.ne')
  deSitter h t := ms_hubble_expMul h t
  powerLaw n t ht := by
    unfold hubble
    rw [(Real.hasDerivAt_rpow_const (Or.inl ht.ne')).deriv, Real.rpow_sub_one ht.ne']
    have : 0 < t ^ n := Real.rpow_pos_of_pos ht n
    field_simp
  static R t _ := by simp [hubble]
  rescale c hc a t _ _ := ms_hubble_rescale c hc.ne' a t
  translate τ a t _ _ := ms_hubble_translate τ a t
  timeReverse a t _ _ := by
    unfold hubble; rw [deriv_comp_neg, neg_div]

/-! ## `decel` meets `DecelSpec` -/

lemma ms_decel_formula (a a' : ℝ → ℝ) (a'' t : ℝ) (h : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s)
    (h2 : HasDerivAt a' a'' t) : decel a t = -(a'' * a t) / a' t ^ 2 := by
  have he : deriv a =ᶠ[𝓝 t] a' := h.mono fun s hs => hs.deriv
  unfold decel
  rw [he.deriv_eq, h2.deriv, he.self_of_nhds]

lemma ms_decel_neg (a : ℝ → ℝ) (t : ℝ) : decel (fun s => a (-s)) t = decel a (-t) := by
  have h1 : deriv (fun s => a (-s)) = fun s => -deriv a (-s) := funext fun s => deriv_comp_neg a s
  have h2 : deriv (fun s => -deriv a (-s)) t = deriv (deriv a) (-t) := by
    have e : (fun s => -deriv a (-s)) = -(fun s => deriv a (-s)) := rfl
    rw [e, deriv.neg, deriv_comp_neg, neg_neg]
  unfold decel
  rw [h1, h2, neg_sq]

lemma ms_decel_powerLaw (n t : ℝ) (hn : n ≠ 0) (ht : 0 < t) :
    decel (fun s => s ^ n) t = (1 - n) / n := by
  have h1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => s ^ n) (n * s ^ (n - 1)) s := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact Real.hasDerivAt_rpow_const (Or.inl hs.ne')
  have h2 := (Real.hasDerivAt_rpow_const (p := n - 1) (Or.inl ht.ne')).const_mul n
  rw [ms_decel_formula _ _ _ t h1 h2, Real.rpow_sub_one ht.ne', Real.rpow_sub_one ht.ne']
  have : 0 < t ^ n := Real.rpow_pos_of_pos ht n
  field_simp
  ring

theorem decel_meets_spec : DecelSpec decel where
  formula a a' a'' t h h2 _ _ := ms_decel_formula a a' a'' t h h2
  deSitter h t hh := by
    have h1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s => Real.exp (h * s)) (h * Real.exp (h * s)) s :=
      Eventually.of_forall fun s => ms_hasDerivAt_expMul h s
    have h2 := (ms_hasDerivAt_expMul h t).const_mul h
    rw [ms_decel_formula _ _ _ t h1 h2]
    have := Real.exp_pos (h * t)
    field_simp
  powerLaw n t hn ht := ms_decel_powerLaw n t hn ht
  eds t ht := by rw [ms_decel_powerLaw _ t (by norm_num) ht]; norm_num
  crunch n t hn ht := by
    have := ms_decel_neg (fun s => s ^ n) t
    rw [show (fun s : ℝ => (-s) ^ n) = fun s => (fun s : ℝ => s ^ n) (-s) from rfl, this,
      ms_decel_powerLaw n (-t) hn (by linarith)]
  rescale c hc a t _ := by
    unfold decel
    rw [deriv_const_mul_field', deriv_const_mul_field]
    have : c ≠ 0 := hc.ne'
    by_cases hd : deriv a t = 0
    · simp [hd]
    · field_simp
  translate τ a t _ := by
    unfold decel
    have h1 : deriv (fun s => a (s + τ)) = fun s => deriv a (s + τ) :=
      funext fun s => deriv_comp_add_const a τ s
    rw [h1, deriv_comp_add_const]
  timeReverse a t _ := ms_decel_neg a t

/-! ## `angDist` meets `AngDistSpec` -/

lemma ms_angDist_eq (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h : a t ≠ 0) (h₀ : a t₀ ≠ 0) :
    angDist K a t₀ t = a t * transverse K (comoving a t₀ t) := by
  unfold angDist lumDist redshift
  rw [add_sub_cancel]
  field_simp

lemma ms_ends {a : ℝ → ℝ} {t₀ t : ℝ} (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) :
    a t ≠ 0 ∧ a t₀ ≠ 0 :=
  ⟨(hpos t ⟨le_rfl, htt⟩).ne', (hpos t₀ ⟨htt, le_rfl⟩).ne'⟩

theorem angDist_meets_spec : AngDistSpec angDist where
  flat a t₀ t htt hpos _ := by
    obtain ⟨h, h₀⟩ := ms_ends htt hpos
    rw [ms_angDist_eq _ _ _ _ h h₀]; simp [transverse, comoving]
  closed a t₀ t htt hpos _ := by
    obtain ⟨h, h₀⟩ := ms_ends htt hpos
    rw [ms_angDist_eq _ _ _ _ h h₀]; simp [transverse, comoving]
  «open» a t₀ t htt hpos _ := by
    obtain ⟨h, h₀⟩ := ms_ends htt hpos
    rw [ms_angDist_eq _ _ _ _ h h₀]; simp [transverse, comoving]
  rescale c hc K a t₀ t := by
    simp only [angDist]
    rw [lumDist_meets_spec.rescale c hc, redshift_rescale c hc]
  translate τ K a t₀ t := by
    have hc : comoving (fun s => a (s + τ)) (t₀ - τ) (t - τ) = comoving a t₀ t := by
      unfold comoving
      rw [intervalIntegral.integral_comp_add_right (fun s => 1 / a s), sub_add_cancel,
        sub_add_cancel]
    simp only [angDist, lumDist, redshift, hc, sub_add_cancel]
  deSitter t _ := by
    rw [ms_angDist_eq _ _ _ _ (Real.exp_pos _).ne' (Real.exp_pos _).ne', comoving_exp]
    simp only [transverse, lt_irrefl, ite_false]
    rw [Real.exp_neg]; field_simp
  deSitterContracting t _ := by
    rw [ms_angDist_eq _ (fun s => Real.exp (-s)) _ _ (Real.exp_pos _).ne' (Real.exp_pos _).ne']
    have hc : comoving (fun s => Real.exp (-s)) 0 t = 1 - Real.exp t := by
      unfold comoving
      have : (fun s => 1 / Real.exp (-s)) = Real.exp := by
        funext s; rw [Real.exp_neg, one_div, inv_inv]
      rw [this, integral_exp, Real.exp_zero]
    simp only [hc, transverse, lt_irrefl, ite_false]
    rw [Real.exp_neg]; field_simp
  milne t ht _ := by
    rw [ms_angDist_eq _ _ _ _ ht.ne' one_ne_zero, comoving_id t ht]
    simp only [transverse, id]
    norm_num
    rw [sinh_log _ (by positivity)]
    field_simp
    ring
  staticClosed R hR t₀ t _ := by
    rw [ms_angDist_eq _ _ _ _ hR.ne' hR.ne']
    simp [transverse, comoving, div_eq_mul_inv]
  staticFlat R hR t₀ t _ := by
    rw [ms_angDist_eq _ _ _ _ hR.ne' hR.ne']
    simp [transverse, comoving]
    field_simp

/-! ## `IsFlatLCDM` meets `FlatLCDMSpec` -/

lemma ms_hasDerivAt_sin23 {t : ℝ} (ht : Real.sin t ≠ 0) :
    HasDerivAt (fun s => Real.sin s ^ (2 / 3 : ℝ))
      (Real.cos t * (2 / 3) * Real.sin t ^ ((2 / 3 : ℝ) - 1)) t :=
  (Real.hasDerivAt_sin t).rpow_const (Or.inl ht)

lemma ms_hubble_sin23 {t : ℝ} (ht : 0 < Real.sin t) :
    hubble (fun s => Real.sin s ^ (2 / 3 : ℝ)) t = 2 / 3 * Real.cos t / Real.sin t := by
  unfold hubble
  rw [(ms_hasDerivAt_sin23 ht.ne').deriv, Real.rpow_sub ht, Real.rpow_one]
  have : 0 < Real.sin t ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos ht _
  field_simp

lemma ms_sin23_cube {t : ℝ} (ht : 0 < Real.sin t) :
    (Real.sin t ^ (2 / 3 : ℝ)) ^ 3 = Real.sin t ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num

lemma ms_isFlatLCDM_sin {t₀ : ℝ} (h₀ : 0 < t₀) (h₁ : t₀ < Real.pi / 2) :
    IsFlatLCDM (1 / Real.cos t₀ ^ 2) (fun t => Real.sin t ^ (2 / 3 : ℝ)) t₀ := by
  have hs0 : 0 < Real.sin t₀ := Real.sin_pos_of_pos_of_lt_pi h₀ (by linarith [Real.pi_pos])
  have hc0 : 0 < Real.cos t₀ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h₁⟩
  refine ⟨by rw [ms_hubble_sin23 hs0]; positivity, ?_⟩
  filter_upwards [Ioo_mem_nhds h₀ h₁] with t ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
  refine ⟨Real.rpow_pos_of_pos hs _, (ms_hasDerivAt_sin23 hs.ne').differentiableAt, ?_⟩
  rw [ms_hubble_sin23 hs, ms_hubble_sin23 hs0, redshift, add_sub_cancel]
  have e0 : 0 < Real.sin t₀ ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hs0 _
  have e1 : 0 < Real.sin t ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hs _
  have harg : 1 / Real.cos t₀ ^ 2 * (Real.sin t₀ ^ (2 / 3 : ℝ) / Real.sin t ^ (2 / 3 : ℝ)) ^ 3
      + 1 - 1 / Real.cos t₀ ^ 2 =
      (Real.sin t₀ * Real.cos t / (Real.cos t₀ * Real.sin t)) ^ 2 := by
    rw [div_pow, ms_sin23_cube hs0, ms_sin23_cube hs]
    have h1 := Real.sin_sq_add_cos_sq t₀
    have h2 := Real.sin_sq_add_cos_sq t
    field_simp
    linear_combination (-Real.sin t₀ ^ 2) * h2 + (Real.sin t ^ 2) * h1
  rw [harg, Real.sqrt_sq (by positivity)]
  field_simp

lemma ms_isFlatLCDM_translate (τ Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (h : IsFlatLCDM Ω a t₀) :
    IsFlatLCDM Ω (fun t => a (t + τ)) (t₀ - τ) := by
  obtain ⟨hH, hev⟩ := h
  have ht : Tendsto (fun s => s + τ) (𝓝 (t₀ - τ)) (𝓝 t₀) := by
    have := (tendsto_id (x := 𝓝 (t₀ - τ))).add_const τ
    rw [sub_add_cancel] at this
    exact this
  refine ⟨by rwa [ms_hubble_translate, sub_add_cancel], ?_⟩
  filter_upwards [ht.eventually hev] with s ⟨h1, h2, h3⟩
  refine ⟨h1, (h2.hasDerivAt.comp_add_const s τ).differentiableAt, ?_⟩
  rw [ms_hubble_translate, ms_hubble_translate, sub_add_cancel]
  simpa only [redshift, sub_add_cancel] using h3

/-- Under `IsFlatLCDM 0 a t₀`, the Hubble rate is constant near `t₀`. -/
lemma ms_const_H {a : ℝ → ℝ} {t₀ : ℝ} (h : IsFlatLCDM 0 a t₀) :
    ∀ᶠ t in 𝓝 t₀, hubble a t = hubble a t₀ := by
  filter_upwards [h.2] with t ⟨_, _, h3⟩
  rw [h3]; simp

lemma ms_hubble_eventually {a b : ℝ → ℝ} {t : ℝ} (h : a =ᶠ[𝓝 t] b) :
    hubble a t = hubble b t := by
  unfold hubble; rw [h.deriv_eq, h.self_of_nhds]

lemma ms_hubble_onePlus (t : ℝ) : hubble (fun s => 1 + s) t = 1 / (1 + t) := by
  unfold hubble
  rw [deriv_const_add, deriv_id'']

lemma ms_hubble_exp (t : ℝ) : hubble Real.exp t = 1 := by
  simp [hubble, Real.deriv_exp, (Real.exp_pos t).ne']

theorem isFlatLCDM_meets_spec : FlatLCDMSpec IsFlatLCDM where
  eds t₀ h := eds_isFlatLCDM h
  deSitter h t₀ hh := by
    refine ⟨by rw [ms_hubble_expMul]; exact hh, Eventually.of_forall fun t => ?_⟩
    refine ⟨Real.exp_pos _, (ms_hasDerivAt_expMul h t).differentiableAt, ?_⟩
    rw [ms_hubble_expMul, ms_hubble_expMul]; simp
  lcdm t₀ h := AvilesWitness.lam_isFlatLCDM h
  negLambda t₀ h₀ h₁ := ms_isFlatLCDM_sin h₀ h₁
  rescale c hc Ω a t₀ := by
    have hc0 : c ≠ 0 := hc.ne'
    simp only [IsFlatLCDM, ms_hubble_rescale c hc0, redshift_rescale c hc]
    have hd : ∀ t, DifferentiableAt ℝ (fun s => c * a s) t ↔ DifferentiableAt ℝ a t := by
      intro t
      constructor
      · intro h
        have := h.const_mul c⁻¹
        simpa [← mul_assoc, inv_mul_cancel₀ hc0] using this
      · intro h; exact h.const_mul c
    simp only [hd, mul_pos_iff_of_pos_left hc]
  translate τ Ω a t₀ h := ms_isFlatLCDM_translate τ Ω a t₀ h
  expanding Ω a t₀ h := by
    have ha : 0 < a t₀ := h.2.self_of_nhds.1
    exact ⟨ha, (div_pos_iff_of_pos_right ha).1 h.1⟩
  contracting Ω h t₀ hh hP := by
    have := hP.1
    rw [show (fun t => Real.exp (-h * t)) = fun t => Real.exp ((-h) * t) from rfl,
      ms_hubble_expMul] at this
    linarith
  edsOnlyOne Ω t₀ h₀ hΩ hP := by
    obtain ⟨t, htt, ht⟩ := (hP.2.and (lt_mem_nhds h₀)).exists_gt
    obtain ⟨⟨_, _, h3⟩, ht0⟩ := ht
    change hubble eds t = hubble eds t₀ * _ at h3
    have c0 : (t₀ ^ (2 / 3 : ℝ)) ^ 3 = t₀ ^ 2 := eds_cube h₀
    have c1 : (t ^ (2 / 3 : ℝ)) ^ 3 = t ^ 2 := eds_cube ht0
    rw [hubble_eds ht0, hubble_eds h₀, redshift, add_sub_cancel, div_pow] at h3
    rw [c0, c1] at h3
    set x := t₀ / t with hx
    have hx0 : 0 < x := div_pos h₀ ht0
    have hx1 : x < 1 := (div_lt_one ht0).2 htt
    have hxs : x = √(Ω * x ^ 2 + 1 - Ω) := by
      rw [hx, div_pow]; field_simp at h3 ⊢; linarith
    have hy : 0 < Ω * x ^ 2 + 1 - Ω := by
      by_contra hn
      rw [Real.sqrt_eq_zero'.2 (not_lt.1 hn)] at hxs; linarith
    have hsq : x ^ 2 = Ω * x ^ 2 + 1 - Ω := by
      have := Real.sq_sqrt hy.le; rw [← hxs] at this; exact this
    have : (1 - Ω) * (x ^ 2 - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hΩ (by linarith)
    · nlinarith
  deSitterOnlyZero Ω h t₀ hh hΩ hP := by
    obtain ⟨t, htt, ⟨_, _, h3⟩⟩ := hP.2.exists_gt
    rw [ms_hubble_expMul, ms_hubble_expMul, redshift, add_sub_cancel] at h3
    set y := Real.exp (h * t₀) / Real.exp (h * t)
    have hy0 : 0 < y := div_pos (Real.exp_pos _) (Real.exp_pos _)
    have hy1 : y < 1 := (div_lt_one (Real.exp_pos _)).2 (Real.exp_lt_exp.2 (by nlinarith))
    have hy3 : y ^ 3 < 1 := pow_lt_one₀ hy0.le hy1 (by norm_num)
    have hs : √(Ω * y ^ 3 + 1 - Ω) = 1 := by
      have := (mul_eq_mul_left_iff.1 (h3.symm.trans (mul_one h).symm)).resolve_right hh.ne'
      exact this
    have := Real.sqrt_eq_one.1 hs
    have : Ω * (y ^ 3 - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hΩ h
    · linarith
  notPastOnly hP := by
    obtain ⟨t₁, ht₁, h₁⟩ := (ms_const_H hP).exists_lt
    obtain ⟨t₂, ht₂, h₂⟩ := (ms_const_H hP).exists_gt
    have e₁ : hubble (fun t => if t ≤ 0 then Real.exp t else 1 + t) t₁ = 1 := by
      rw [ms_hubble_eventually (b := Real.exp), ms_hubble_exp]
      filter_upwards [gt_mem_nhds ht₁] with s hs; simp [hs.le]
    have e₂ : hubble (fun t => if t ≤ 0 then Real.exp t else 1 + t) t₂ = 1 / (1 + t₂) := by
      rw [ms_hubble_eventually (b := fun s => 1 + s), ms_hubble_onePlus]
      filter_upwards [lt_mem_nhds ht₂] with s hs; simp [not_le.2 hs]
    rw [e₁] at h₁; rw [e₂, ← h₁] at h₂
    have : 0 < 1 + t₂ := by linarith
    field_simp at h₂; linarith
  notFutureOnly hP := by
    obtain ⟨t₁, ht₁, h₁⟩ :=
      ((ms_const_H hP).and (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))).exists_lt
    obtain ⟨t₂, ht₂, h₂⟩ := (ms_const_H hP).exists_gt
    have e₁ : hubble (fun t => if t ≤ 0 then 1 + t else Real.exp t) t₁ = 1 / (1 + t₁) := by
      rw [ms_hubble_eventually (b := fun s => 1 + s), ms_hubble_onePlus]
      filter_upwards [gt_mem_nhds ht₁] with s hs; simp [hs.le]
    have e₂ : hubble (fun t => if t ≤ 0 then 1 + t else Real.exp t) t₂ = 1 := by
      rw [ms_hubble_eventually (b := Real.exp), ms_hubble_exp]
      filter_upwards [lt_mem_nhds ht₂] with s hs; simp [not_le.2 hs]
    rw [e₂] at h₂; rw [e₁, ← h₂] at h₁
    have : 0 < 1 + t₁ := by linarith [h₁.2]
    have h1 := h₁.1
    field_simp at h1; linarith

end Checked.Fidelity
