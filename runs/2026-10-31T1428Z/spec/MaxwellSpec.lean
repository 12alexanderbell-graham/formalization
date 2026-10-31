import Mathlib

/-!
# Specification of "Maxwell coexistence on an isotherm"

`M p vl vg ps` is read: on the isotherm `p` (pressure as a function of molar volume at fixed
temperature) the liquid molar volume `vl` and the gas molar volume `vg` coexist at the
saturation pressure `ps`, according to Maxwell's equal-area construction (equivalently: equal
pressure and equal molar Gibbs energy / chemical potential `μ = f + p v`, where the molar
Helmholtz energy along the isotherm satisfies `∂f/∂v = -p`). Convention: `vl < vg`.

Textbook (Maxwell 1875; Callen §9.4; Landau–Lifshitz §84): the horizontal line `p = ps` meets
the isotherm at `vl < vg`, and the area between the isotherm and the line over `[vl, vg]`
vanishes, `∫_{vl}^{vg} p dv = ps (vg - vl)`.

## Physical domain

Every law below is only asserted on the *physical domain* `PhysDomain p vl vg`:
both molar volumes are positive and the isotherm is continuous on an open set containing the
segment between them. (An open neighbourhood rather than the closed segment, so that
definitions phrased with a Helmholtz energy `f` with `HasDerivAt f (-p v) v` at the endpoints
are not over-constrained.) Outside the domain the spec says nothing.

The spec is blind: it was written without seeing the definition under test.
-/

set_option linter.dupNamespace false

namespace Work.Fidelity.MaxwellSpec

open Set MeasureTheory intervalIntegral

/-- Physical domain of the Maxwell construction: positive molar volumes, and an isotherm
continuous on an open set containing the segment `[vl, vg]` (in either order). -/
def PhysDomain (p : ℝ → ℝ) (vl vg : ℝ) : Prop :=
  0 < vl ∧ 0 < vg ∧ ∃ U : Set ℝ, IsOpen U ∧ Set.uIcc vl vg ⊆ U ∧ ContinuousOn p U

/-- Model van der Waals-like loop with three roots of `p = ps`:
`p(v) = ps − k (v − c − d) ((v − c)² − x²)`; the roots are `c − x`, `c + d`, `c + x`.
For `k > 0`, `|d| < x` it is decreasing at the outer roots (stable liquid/gas branches)
and increasing at the middle root (unstable branch). For `d = 0` it is antisymmetric about
`(c, ps)`, so the two Maxwell areas are exactly equal; for `d ≠ 0` they are not. -/
def cubicLoop (ps k c x d : ℝ) : ℝ → ℝ :=
  fun v => ps - k * (v - c - d) * ((v - c) ^ 2 - x ^ 2)

/-! ### An exact van der Waals coexistence point

For `p(v) = A/(v − b) − a/v²`, write `vl = b(1+u)`, `vg = b(1+u r)` (`r > 1`).
Equal pressures fix `A` (i.e. the temperature, `A = R T`) and `ps` rationally, and the
equal-area condition becomes `log r = (r−1)(1+r+2ur)/(r(2+u(1+r)))`, which is *linear* in
`u`. Choosing `r = e²` (so `log r = 2`) gives `u = (r² − 4r − 1)/(4r) ≈ 0.813`, i.e.
`vl ≈ 1.813 b`, `vg ≈ 7.010 b` (reduced volumes ≈ 0.604 and ≈ 2.337). -/

/-- `r = e²`, the exact volume ratio `(vg − b)/(vl − b)` of the anchor. -/
noncomputable def vdWr : ℝ := Real.exp 2
/-- `u = (vl − b)/b` of the anchor. -/
noncomputable def vdWu : ℝ := (vdWr ^ 2 - 4 * vdWr - 1) / (4 * vdWr)
/-- Liquid volume of the anchor. -/
noncomputable def vdWvl (b : ℝ) : ℝ := b * (1 + vdWu)
/-- Gas volume of the anchor. -/
noncomputable def vdWvg (b : ℝ) : ℝ := b * (1 + vdWu * vdWr)
/-- `A = R T` of the anchor isotherm (the unique one with `p(vl) = p(vg)`). -/
noncomputable def vdWA (a b : ℝ) : ℝ :=
  a * (vdWvg b + vdWvl b) * (vdWvl b - b) * (vdWvg b - b) / (vdWvl b ^ 2 * vdWvg b ^ 2)
/-- Saturation pressure of the anchor. -/
noncomputable def vdWps (a b : ℝ) : ℝ :=
  a * (vdWvl b * vdWvg b - b * (vdWvl b + vdWvg b)) / (vdWvl b ^ 2 * vdWvg b ^ 2)

/-- Laws every faithful definition `M` of Maxwell coexistence must satisfy.
Only the physical domain `PhysDomain` is constrained. -/
structure MaxwellSpec (M : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) : Prop where
  /-- (a) DETERMINING LAW (equal areas). On the physical domain, `vl, vg` coexist at `ps` iff
  `vl < vg`, both lie on the line `p = ps`, and the signed area between isotherm and line
  vanishes: `∫_{vl}^{vg} p dv = ps (vg − vl)`. -/
  determining : ∀ (p : ℝ → ℝ) (vl vg ps : ℝ), PhysDomain p vl vg →
    (M p vl vg ps ↔
      vl < vg ∧ p vl = ps ∧ p vg = ps ∧ ∫ v in vl..vg, p v = ps * (vg - vl))
  /-- (a) DETERMINING LAW (equal chemical potential). For any molar Helmholtz energy `f`
  along the isotherm (`∂f/∂v = −p`), coexistence iff equal pressure and equal
  `μ = f + p v`. -/
  equal_chemical_potential : ∀ (p f : ℝ → ℝ) (vl vg ps : ℝ), PhysDomain p vl vg →
    (∀ v ∈ Set.uIcc vl vg, HasDerivAt f (-p v) v) →
    (M p vl vg ps ↔ vl < vg ∧ p vl = ps ∧ p vg = ps ∧ f vl + ps * vl = f vg + ps * vg)
  /-- (b) ANCHOR (general). An isotherm antisymmetric about `(c, ps)` that crosses `ps` at
  `c + x` has Maxwell coexistence between `c − x` and `c + x` at `ps`. -/
  antisymmetric : ∀ (p : ℝ → ℝ) (c x ps : ℝ), 0 < x → PhysDomain p (c - x) (c + x) →
    (∀ t, p (c + t) - ps = -(p (c - t) - ps)) → p (c + x) = ps → M p (c - x) (c + x) ps
  /-- (b) ANCHOR. The symmetric cubic loop coexists between its outer roots. -/
  cubic_loop : ∀ ps k c x : ℝ, 0 < k → 0 < x → x < c →
    M (cubicLoop ps k c x 0) (c - x) (c + x) ps
  /-- (b) ANCHOR. Exact van der Waals coexistence point (see `vdWr`, …, `vdWps`). -/
  vdW_anchor : ∀ a b : ℝ, 0 < a → 0 < b →
    M (fun v => vdWA a b / (v - b) - a / v ^ 2) (vdWvl b) (vdWvg b) (vdWps a b)
  /-- (c) NEAR MISS. Same van der Waals volumes, wrong pressure. -/
  vdW_wrong_pressure : ∀ a b ps : ℝ, 0 < a → 0 < b → ps ≠ vdWps a b →
    ¬ M (fun v => vdWA a b / (v - b) - a / v ^ 2) (vdWvl b) (vdWvg b) ps
  /-- (c) NEAR MISS. Same van der Waals volumes and pressure, wrong temperature. -/
  vdW_wrong_temperature : ∀ a b A : ℝ, 0 < a → 0 < b → A ≠ vdWA a b →
    ¬ M (fun v => A / (v - b) - a / v ^ 2) (vdWvl b) (vdWvg b) (vdWps a b)
  /-- (c) NEAR MISS. Equal pressures at the outer roots but unequal areas (`d ≠ 0`). -/
  unequal_areas : ∀ ps k c x d : ℝ, 0 < k → 0 < x → x < c → d ≠ 0 →
    ¬ M (cubicLoop ps k c x d) (c - x) (c + x) ps
  /-- (c) NEAR MISS. Liquid root paired with the middle (unstable) root. -/
  liquid_middle : ∀ ps k c x : ℝ, 0 < k → 0 < x → x < c →
    ¬ M (cubicLoop ps k c x 0) (c - x) c ps
  /-- (c) NEAR MISS. Middle (unstable) root paired with the gas root. -/
  middle_gas : ∀ ps k c x : ℝ, 0 < k → 0 < x → x < c →
    ¬ M (cubicLoop ps k c x 0) c (c + x) ps
  /-- (c) NEAR MISS. Coincident volumes are never a coexisting pair. -/
  coincident : ∀ (p : ℝ → ℝ) (v ps : ℝ), PhysDomain p v v → ¬ M p v v ps
  /-- (c) NEAR MISS. Swapped order (gas volume first) is rejected. -/
  swapped : ∀ ps k c x : ℝ, 0 < k → 0 < x → x < c →
    ¬ M (cubicLoop ps k c x 0) (c + x) (c - x) ps
  /-- (c) Order is strict in general: at most one of `(vl, vg)`, `(vg, vl)` coexists. -/
  asymm : ∀ (p : ℝ → ℝ) (vl vg ps : ℝ), PhysDomain p vl vg → M p vl vg ps → ¬ M p vg vl ps
  /-- (c) NEAR MISS. Correct volumes, wrong pressure. -/
  wrong_pressure : ∀ ps ps' k c x : ℝ, 0 < k → 0 < x → x < c → ps' ≠ ps →
    ¬ M (cubicLoop ps k c x 0) (c - x) (c + x) ps'
  /-- (c) NEAR MISS. Equal areas but unequal endpoint pressures (a decreasing line). -/
  equal_area_unequal_pressure : ∀ ps c x : ℝ, 0 < x → x < c →
    ¬ M (fun v => ps - (v - c)) (c - x) (c + x) ps
  /-- (c) NEAR MISS. Sign-flipped area condition `∫ (p + ps) = 0` (e.g. from `μ = f − p v`
  or from `∂f/∂v = +p`): here `p(1) = p(3) = 1` and `∫₁³ p = −2 = −ps (vg − vl)`. -/
  sign_flipped_area : ¬ M (cubicLoop 1 6 2 1 (1 / 2)) 1 3 1
  /-- (c) The saturation pressure is determined by the coexisting volumes. -/
  pressure_unique : ∀ (p : ℝ → ℝ) (vl vg ps ps' : ℝ), PhysDomain p vl vg →
    M p vl vg ps → M p vl vg ps' → ps = ps'
  /-- (d) Locality: only the isotherm on a neighbourhood of `[vl, vg]` matters. -/
  local_ : ∀ (p q : ℝ → ℝ) (vl vg ps : ℝ) (U : Set ℝ), 0 < vl → 0 < vg → IsOpen U →
    Set.uIcc vl vg ⊆ U → ContinuousOn p U → Set.EqOn p q U →
    (M p vl vg ps ↔ M q vl vg ps)
  /-- (d) Shifting the pressure origin shifts the saturation pressure. -/
  add_const : ∀ (p : ℝ → ℝ) (vl vg ps c : ℝ), PhysDomain p vl vg →
    (M (fun v => p v + c) vl vg (ps + c) ↔ M p vl vg ps)
  /-- (d) Changing the pressure unit rescales the saturation pressure. -/
  smul_pos : ∀ (p : ℝ → ℝ) (vl vg ps k : ℝ), 0 < k → PhysDomain p vl vg →
    (M (fun v => k * p v) vl vg (k * ps) ↔ M p vl vg ps)
  /-- (d) Translating the volume axis translates the coexisting volumes. -/
  translate : ∀ (p : ℝ → ℝ) (vl vg ps s : ℝ), PhysDomain p vl vg → 0 < vl - s → 0 < vg - s →
    (M (fun v => p (v + s)) (vl - s) (vg - s) ps ↔ M p vl vg ps)
  /-- (d) Changing the volume unit rescales the coexisting volumes. -/
  rescale_volume : ∀ (p : ℝ → ℝ) (vl vg ps k : ℝ), 0 < k → PhysDomain p vl vg →
    (M (fun v => p (k * v)) (vl / k) (vg / k) ps ↔ M p vl vg ps)

/-! ## Reference definition (textbook) -/

/-- Textbook Maxwell construction: `vl < vg`, equal pressure `ps` at both volumes, and equal
areas `∫_{vl}^{vg} p dv = ps (vg − vl)`. -/
def MRef (p : ℝ → ℝ) (vl vg ps : ℝ) : Prop :=
  vl < vg ∧ p vl = ps ∧ p vg = ps ∧ ∫ v in vl..vg, p v = ps * (vg - vl)

/-! ### Domain lemmas -/

theorem PhysDomain.intervalIntegrable {p : ℝ → ℝ} {vl vg : ℝ} (h : PhysDomain p vl vg) :
    IntervalIntegrable p volume vl vg := by
  obtain ⟨-, -, U, -, hsub, hc⟩ := h
  exact (hc.mono hsub).intervalIntegrable

theorem physDomain_of_continuous {p : ℝ → ℝ} {vl vg : ℝ} (hp : Continuous p) (hl : 0 < vl)
    (hg : 0 < vg) : PhysDomain p vl vg :=
  ⟨hl, hg, univ, isOpen_univ, subset_univ _, hp.continuousOn⟩

/-! ### The cubic loop -/

/-- Antiderivative of `cubicLoop`. -/
noncomputable def loopAnti (ps k c x d : ℝ) (v : ℝ) : ℝ :=
  ps * v - k * ((v - c) ^ 4 / 4 - d * (v - c) ^ 3 / 3 - x ^ 2 * (v - c) ^ 2 / 2
    + d * x ^ 2 * (v - c))

theorem loopAnti_hasDerivAt (ps k c x d v : ℝ) :
    HasDerivAt (loopAnti ps k c x d) (cubicLoop ps k c x d v) v := by
  have hu : HasDerivAt (fun w : ℝ => w - c) 1 v := (hasDerivAt_id v).sub_const c
  have h4 := (hu.pow 4).div_const 4
  have h3 := ((hu.pow 3).const_mul d).div_const 3
  have h2 := ((hu.pow 2).const_mul (x ^ 2)).div_const 2
  have h1 := hu.const_mul (d * x ^ 2)
  have hG := ((h4.sub h3).sub h2).add h1
  have h := ((hasDerivAt_id v).const_mul ps).sub (hG.const_mul k)
  convert h using 1
  · funext w; simp [loopAnti]
  · simp [cubicLoop]; ring

theorem cubicLoop_continuous (ps k c x d : ℝ) : Continuous (cubicLoop ps k c x d) := by
  unfold cubicLoop; fun_prop

theorem loop_integral (ps k c x d a b : ℝ) :
    ∫ v in a..b, cubicLoop ps k c x d v = loopAnti ps k c x d b - loopAnti ps k c x d a :=
  integral_eq_sub_of_hasDerivAt (fun v _ => loopAnti_hasDerivAt ps k c x d v)
    ((cubicLoop_continuous ps k c x d).intervalIntegrable a b)

/-! ### The van der Waals anchor -/

theorem vdWr_gt : 7 < vdWr := by
  have h1 := Real.exp_one_gt_d9
  have : vdWr = Real.exp 1 * Real.exp 1 := by
    rw [vdWr, ← Real.exp_add]; norm_num
  rw [this]; nlinarith

theorem vdWu_pos : 0 < vdWu := by
  have h := vdWr_gt
  unfold vdWu
  apply div_pos _ (by linarith)
  nlinarith

theorem vdW_hasDerivAt (A a b v : ℝ) (hv : b < v) (hv0 : v ≠ 0) :
    HasDerivAt (fun w => A * Real.log (w - b) + a / w) (A / (v - b) - a / v ^ 2) v := by
  have hvb : v - b ≠ 0 := by linarith
  have h1 := (((hasDerivAt_id v).sub_const b).log hvb).const_mul A
  have h2 := (hasDerivAt_inv hv0).const_mul a
  convert h1.add h2 using 1
  · funext w; simp [div_eq_mul_inv]
  · simp; field_simp; ring

theorem vdW_continuousOn (A a b : ℝ) (hb : 0 < b) :
    ContinuousOn (fun v => A / (v - b) - a / v ^ 2) (Ioi b) := by
  intro v hv
  have hv' : b < v := hv
  apply ContinuousAt.continuousWithinAt
  have h1 : v - b ≠ 0 := by linarith
  have h2 : v ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith : (0:ℝ) < v).ne'
  fun_prop (disch := assumption)

theorem vdW_physDomain (A a b : ℝ) (hb : 0 < b) (vl vg : ℝ) (hl : b < vl) (hg : b < vg) :
    PhysDomain (fun v => A / (v - b) - a / v ^ 2) vl vg := by
  refine ⟨by linarith, by linarith, Ioi b, isOpen_Ioi, ?_, vdW_continuousOn A a b hb⟩
  intro v hv
  rcases Set.mem_uIcc.1 hv with ⟨h, -⟩ | ⟨h, -⟩
  · exact lt_of_lt_of_le hl h
  · exact lt_of_lt_of_le hg h

theorem vdW_integral (A a b vl vg : ℝ) (hb : 0 < b) (hl : b < vl) (hg : b < vg) :
    ∫ v in vl..vg, (A / (v - b) - a / v ^ 2)
      = A * Real.log (vg - b) + a / vg - (A * Real.log (vl - b) + a / vl) := by
  have hD := vdW_physDomain A a b hb vl vg hl hg
  apply integral_eq_sub_of_hasDerivAt (f := fun w => A * Real.log (w - b) + a / w)
  · intro v hv
    have : b < v := by
      rcases Set.mem_uIcc.1 hv with ⟨h, -⟩ | ⟨h, -⟩
      · exact lt_of_lt_of_le hl h
      · exact lt_of_lt_of_le hg h
    exact vdW_hasDerivAt A a b v this (by linarith : (0:ℝ) < v).ne'
  · exact hD.intervalIntegrable

theorem vdW_facts (b : ℝ) (hb : 0 < b) :
    b < vdWvl b ∧ b < vdWvg b ∧ vdWvl b < vdWvg b := by
  have hu := vdWu_pos
  have hr := vdWr_gt
  unfold vdWvl vdWvg
  refine ⟨by nlinarith, ?_, ?_⟩
  · have : 0 < vdWu * vdWr := by positivity
    nlinarith
  · have : vdWu < vdWu * vdWr := by nlinarith
    nlinarith

theorem ref_vdW_anchor (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    MRef (fun v => vdWA a b / (v - b) - a / v ^ 2) (vdWvl b) (vdWvg b) (vdWps a b) := by
  obtain ⟨hl, hg, hlg⟩ := vdW_facts b hb
  have hu := vdWu_pos
  have hr := vdWr_gt
  have hr0 : vdWr ≠ 0 := by positivity
  have hu0 : vdWu ≠ 0 := hu.ne'
  have hl0 : vdWvl b ≠ 0 := (by linarith : (0:ℝ) < vdWvl b).ne'
  have hg0 : vdWvg b ≠ 0 := (by linarith : (0:ℝ) < vdWvg b).ne'
  have hlb : vdWvl b - b ≠ 0 := by linarith
  have hgb : vdWvg b - b ≠ 0 := by linarith
  refine ⟨hlg, ?_, ?_, ?_⟩
  · simp only [vdWA, vdWps]
    field_simp
    ring
  · simp only [vdWA, vdWps]
    field_simp
    ring
  · simp only
    rw [vdW_integral _ _ _ _ _ hb hl hg]
    have hlog : Real.log (vdWvg b - b) - Real.log (vdWvl b - b) = 2 := by
      have e : vdWvg b - b = (vdWvl b - b) * vdWr := by unfold vdWvl vdWvg; ring
      rw [e, Real.log_mul hlb hr0, vdWr, Real.log_exp]; ring
    have key : vdWA a b * 2 + a / vdWvg b - a / vdWvl b
        = vdWps a b * (vdWvg b - vdWvl b) := by
      have hrel : 4 * vdWr * vdWu = vdWr ^ 2 - 4 * vdWr - 1 := by
        rw [vdWu]; field_simp
      have e : vdWA a b * 2 + a / vdWvg b - a / vdWvl b - vdWps a b * (vdWvg b - vdWvl b)
          = a * (2 * (vdWvg b + vdWvl b) * (vdWvl b - b) * (vdWvg b - b)
              + vdWvl b ^ 2 * vdWvg b - vdWvl b * vdWvg b ^ 2
              - (vdWvl b * vdWvg b - b * (vdWvl b + vdWvg b)) * (vdWvg b - vdWvl b))
            / (vdWvl b ^ 2 * vdWvg b ^ 2) := by
        unfold vdWA vdWps; field_simp
      have hN : a * (2 * (vdWvg b + vdWvl b) * (vdWvl b - b) * (vdWvg b - b)
              + vdWvl b ^ 2 * vdWvg b - vdWvl b * vdWvg b ^ 2
              - (vdWvl b * vdWvg b - b * (vdWvl b + vdWvg b)) * (vdWvg b - vdWvl b)) = 0 := by
        unfold vdWvl vdWvg
        linear_combination (a * b ^ 3 * vdWu ^ 2) * hrel
      rw [hN, zero_div] at e
      linarith
    have : vdWA a b * Real.log (vdWvg b - b) + a / vdWvg b
        - (vdWA a b * Real.log (vdWvl b - b) + a / vdWvl b)
        = vdWA a b * (Real.log (vdWvg b - b) - Real.log (vdWvl b - b))
          + a / vdWvg b - a / vdWvl b := by ring
    rw [this, hlog, key]

/-! ## The determining law implies the whole specification -/

section FromDetermining

variable {M : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop}
  (hM : ∀ (p : ℝ → ℝ) (vl vg ps : ℝ), PhysDomain p vl vg → (M p vl vg ps ↔ MRef p vl vg ps))
include hM

theorem det_equal_chemical_potential (p f : ℝ → ℝ) (vl vg ps : ℝ) (hD : PhysDomain p vl vg)
    (hf : ∀ v ∈ Set.uIcc vl vg, HasDerivAt f (-p v) v) :
    M p vl vg ps ↔ vl < vg ∧ p vl = ps ∧ p vg = ps ∧ f vl + ps * vl = f vg + ps * vg := by
  rw [hM p vl vg ps hD]
  have hI : ∫ v in vl..vg, -p v = f vg - f vl :=
    integral_eq_sub_of_hasDerivAt hf hD.intervalIntegrable.neg
  rw [intervalIntegral.integral_neg] at hI
  unfold MRef
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, by linarith⟩

theorem det_antisymmetric (p : ℝ → ℝ) (c x ps : ℝ) (hx : 0 < x)
    (hD : PhysDomain p (c - x) (c + x)) (hs : ∀ t, p (c + t) - ps = -(p (c - t) - ps))
    (hp : p (c + x) = ps) : M p (c - x) (c + x) ps := by
  rw [hM _ _ _ _ hD]
  have hpl : p (c - x) = ps := by have := hs x; linarith
  refine ⟨by linarith, hpl, hp, ?_⟩
  have hint := hD.intervalIntegrable
  have href : ∫ v in (c - x)..(c + x), p (2 * c - v) = ∫ v in (c - x)..(c + x), p v := by
    rw [intervalIntegral.integral_comp_sub_left (fun v => p v) (2 * c)]
    congr 1 <;> ring
  have hrefl : ∀ v, p (2 * c - v) = 2 * ps - p v := by
    intro v
    have := hs (c - v)
    rw [show c + (c - v) = 2 * c - v by ring, show c - (c - v) = v by ring] at this
    linarith
  simp only [hrefl] at href
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
    intervalIntegral.integral_const, smul_eq_mul] at href
  linarith

theorem det_loop_iff (ps k c x d vl vg ps' : ℝ) (hl : 0 < vl) (hg : 0 < vg) :
    M (cubicLoop ps k c x d) vl vg ps' ↔
      vl < vg ∧ cubicLoop ps k c x d vl = ps' ∧ cubicLoop ps k c x d vg = ps' ∧
        loopAnti ps k c x d vg - loopAnti ps k c x d vl = ps' * (vg - vl) := by
  rw [hM _ _ _ _ (physDomain_of_continuous (cubicLoop_continuous _ _ _ _ _) hl hg), MRef,
    loop_integral]

theorem det_cubic_loop (ps k c x : ℝ) (_hk : 0 < k) (hx : 0 < x) (hxc : x < c) :
    M (cubicLoop ps k c x 0) (c - x) (c + x) ps := by
  rw [det_loop_iff hM _ _ _ _ _ _ _ _ (by linarith) (by linarith)]
  refine ⟨by linarith, by simp [cubicLoop], by simp [cubicLoop], ?_⟩
  simp only [loopAnti]; ring

theorem det_unequal_areas (ps k c x d : ℝ) (hk : 0 < k) (hx : 0 < x) (hxc : x < c)
    (hd : d ≠ 0) : ¬ M (cubicLoop ps k c x d) (c - x) (c + x) ps := by
  rw [det_loop_iff hM _ _ _ _ _ _ _ _ (by linarith) (by linarith)]
  rintro ⟨-, -, -, h⟩
  have e : loopAnti ps k c x d (c + x) - loopAnti ps k c x d (c - x)
      = ps * (c + x - (c - x)) - 4 / 3 * k * d * x ^ 3 := by
    simp only [loopAnti]; ring
  rw [e] at h
  have : k * d * x ^ 3 = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hk.ne' h2
    · exact hd h2
  · exact (pow_pos hx 3).ne' h1

theorem det_liquid_middle (ps k c x : ℝ) (hk : 0 < k) (hx : 0 < x) (hxc : x < c) :
    ¬ M (cubicLoop ps k c x 0) (c - x) c ps := by
  rw [det_loop_iff hM _ _ _ _ _ _ _ _ (by linarith) (by linarith)]
  rintro ⟨-, -, -, h⟩
  have e : loopAnti ps k c x 0 c - loopAnti ps k c x 0 (c - x)
      = ps * (c - (c - x)) - k * x ^ 4 / 4 := by
    simp only [loopAnti]; ring
  rw [e] at h
  have : 0 < k * x ^ 4 := by positivity
  linarith

theorem det_middle_gas (ps k c x : ℝ) (hk : 0 < k) (hx : 0 < x) (hxc : x < c) :
    ¬ M (cubicLoop ps k c x 0) c (c + x) ps := by
  rw [det_loop_iff hM _ _ _ _ _ _ _ _ (by linarith) (by linarith)]
  rintro ⟨-, -, -, h⟩
  have e : loopAnti ps k c x 0 (c + x) - loopAnti ps k c x 0 c
      = ps * (c + x - c) + k * x ^ 4 / 4 := by
    simp only [loopAnti]; ring
  rw [e] at h
  have : 0 < k * x ^ 4 := by positivity
  linarith

theorem det_swapped (ps k c x : ℝ) (_hk : 0 < k) (hx : 0 < x) (hxc : x < c) :
    ¬ M (cubicLoop ps k c x 0) (c + x) (c - x) ps := by
  rw [det_loop_iff hM _ _ _ _ _ _ _ _ (by linarith) (by linarith)]
  rintro ⟨h, -⟩
  linarith

theorem det_wrong_pressure (ps ps' k c x : ℝ) (_hk : 0 < k) (hx : 0 < x) (hxc : x < c)
    (hne : ps' ≠ ps) : ¬ M (cubicLoop ps k c x 0) (c - x) (c + x) ps' := by
  rw [det_loop_iff hM _ _ _ _ _ _ _ _ (by linarith) (by linarith)]
  rintro ⟨-, h, -⟩
  apply hne
  rw [← h]
  simp [cubicLoop]

theorem det_sign_flipped : ¬ M (cubicLoop 1 6 2 1 (1 / 2)) 1 3 1 := by
  rw [det_loop_iff hM _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
  rintro ⟨-, -, -, h⟩
  norm_num [loopAnti] at h

end FromDetermining

/-! ### Invariances from the determining law -/

theorem mref_add_const (p : ℝ → ℝ) (vl vg ps c : ℝ) (hD : PhysDomain p vl vg) :
    MRef (fun v => p v + c) vl vg (ps + c) ↔ MRef p vl vg ps := by
  unfold MRef
  rw [intervalIntegral.integral_add hD.intervalIntegrable intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by linarith, by linarith, by linarith⟩

theorem physDomain_add_const {p : ℝ → ℝ} {vl vg : ℝ} (c : ℝ) (hD : PhysDomain p vl vg) :
    PhysDomain (fun v => p v + c) vl vg := by
  obtain ⟨h1, h2, U, hU, hs, hc⟩ := hD
  exact ⟨h1, h2, U, hU, hs, hc.add continuousOn_const⟩

theorem mref_smul (p : ℝ → ℝ) (vl vg ps k : ℝ) (hk : k ≠ 0) :
    MRef (fun v => k * p v) vl vg (k * ps) ↔ MRef p vl vg ps := by
  unfold MRef
  rw [intervalIntegral.integral_const_mul]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, mul_left_cancel₀ hk h2, mul_left_cancel₀ hk h3, mul_left_cancel₀ hk ?_⟩
    rw [h4]; ring
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by simp only; rw [h2], by simp only; rw [h3], by rw [h4]; ring⟩

theorem physDomain_smul {p : ℝ → ℝ} {vl vg : ℝ} (k : ℝ) (hD : PhysDomain p vl vg) :
    PhysDomain (fun v => k * p v) vl vg := by
  obtain ⟨h1, h2, U, hU, hs, hc⟩ := hD
  exact ⟨h1, h2, U, hU, hs, continuousOn_const.mul hc⟩

theorem mref_translate (p : ℝ → ℝ) (vl vg ps s : ℝ) :
    MRef (fun v => p (v + s)) (vl - s) (vg - s) ps ↔ MRef p vl vg ps := by
  unfold MRef
  rw [intervalIntegral.integral_comp_add_right (fun v => p v) s]
  simp only [sub_add_cancel]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, h2, h3, by rw [h4]; ring⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by linarith, h2, h3, by rw [h4]; ring⟩

theorem physDomain_translate {p : ℝ → ℝ} {vl vg : ℝ} (s : ℝ) (hD : PhysDomain p vl vg)
    (hl : 0 < vl - s) (hg : 0 < vg - s) :
    PhysDomain (fun v => p (v + s)) (vl - s) (vg - s) := by
  obtain ⟨-, -, U, hU, hs, hc⟩ := hD
  refine ⟨hl, hg, (fun v => v + s) ⁻¹' U, hU.preimage (continuous_id.add continuous_const), ?_, ?_⟩
  · intro v hv
    apply hs
    rcases Set.mem_uIcc.1 hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Set.mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩)
    · exact Set.mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
  · exact hc.comp (continuousOn_id.add continuousOn_const) (fun v hv => hv)

theorem mref_rescale (p : ℝ → ℝ) (vl vg ps k : ℝ) (hk : 0 < k) :
    MRef (fun v => p (k * v)) (vl / k) (vg / k) ps ↔ MRef p vl vg ps := by
  unfold MRef
  beta_reduce
  rw [intervalIntegral.integral_comp_mul_left (fun v => p v) hk.ne']
  have e1 : k * (vl / k) = vl := by field_simp
  have e2 : k * (vg / k) = vg := by field_simp
  rw [e1, e2, smul_eq_mul, div_lt_div_iff_of_pos_right hk]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    have : ∫ v in vl..vg, p v = k * (k⁻¹ * ∫ v in vl..vg, p v) := by field_simp
    rw [this, h4]; field_simp
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [h4]; field_simp

theorem physDomain_rescale {p : ℝ → ℝ} {vl vg : ℝ} {k : ℝ} (hk : 0 < k)
    (hD : PhysDomain p vl vg) : PhysDomain (fun v => p (k * v)) (vl / k) (vg / k) := by
  obtain ⟨hl, hg, U, hU, hs, hc⟩ := hD
  refine ⟨by positivity, by positivity, (fun v => k * v) ⁻¹' U,
    hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · intro v hv
    apply hs
    have e1 : k * (vl / k) = vl := by field_simp
    have e2 : k * (vg / k) = vg := by field_simp
    rcases Set.mem_uIcc.1 hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a1 := mul_le_mul_of_nonneg_left h1 hk.le
      have a2 := mul_le_mul_of_nonneg_left h2 hk.le
      rw [e1] at a1; rw [e2] at a2
      exact Set.mem_uIcc.2 (Or.inl ⟨a1, a2⟩)
    · have a1 := mul_le_mul_of_nonneg_left h1 hk.le
      have a2 := mul_le_mul_of_nonneg_left h2 hk.le
      rw [e2] at a1; rw [e1] at a2
      exact Set.mem_uIcc.2 (Or.inr ⟨a1, a2⟩)
  · exact hc.comp (continuousOn_const.mul continuousOn_id) (fun v hv => hv)

theorem mref_local (p q : ℝ → ℝ) (vl vg ps : ℝ) (U : Set ℝ) (hs : Set.uIcc vl vg ⊆ U)
    (he : Set.EqOn p q U) : MRef p vl vg ps ↔ MRef q vl vg ps := by
  have hl : p vl = q vl := he (hs Set.left_mem_uIcc)
  have hg : p vg = q vg := he (hs Set.right_mem_uIcc)
  have hI : ∫ v in vl..vg, p v = ∫ v in vl..vg, q v :=
    intervalIntegral.integral_congr (fun v hv => he (hs hv))
  unfold MRef
  rw [hl, hg, hI]

/-- Any `M` agreeing with the textbook `MRef` on the physical domain meets the whole spec. -/
theorem of_determining {M : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop}
    (hM : ∀ (p : ℝ → ℝ) (vl vg ps : ℝ), PhysDomain p vl vg →
      (M p vl vg ps ↔ MRef p vl vg ps)) : MaxwellSpec M where
  determining := hM
  equal_chemical_potential := det_equal_chemical_potential hM
  antisymmetric := det_antisymmetric hM
  cubic_loop := det_cubic_loop hM
  vdW_anchor := by
    intro a b ha hb
    obtain ⟨hl, hg, -⟩ := vdW_facts b hb
    exact (hM _ _ _ _ (vdW_physDomain _ a b hb _ _ hl hg)).2 (ref_vdW_anchor a b ha hb)
  vdW_wrong_pressure := by
    intro a b ps ha hb hne h
    obtain ⟨hl, hg, -⟩ := vdW_facts b hb
    obtain ⟨-, h1, -⟩ := (hM _ _ _ _ (vdW_physDomain _ a b hb _ _ hl hg)).1 h
    obtain ⟨-, h2, -⟩ := ref_vdW_anchor a b ha hb
    exact hne (h1.symm.trans h2)
  vdW_wrong_temperature := by
    intro a b A ha hb hne h
    obtain ⟨hl, hg, -⟩ := vdW_facts b hb
    obtain ⟨-, h1, -⟩ := (hM _ _ _ _ (vdW_physDomain _ a b hb _ _ hl hg)).1 h
    obtain ⟨-, h2, -⟩ := ref_vdW_anchor a b ha hb
    have hlb : vdWvl b - b ≠ 0 := by linarith
    apply hne
    have : A / (vdWvl b - b) = vdWA a b / (vdWvl b - b) := by
      simp only at h1 h2; linarith
    field_simp at this
    exact this
  unequal_areas := det_unequal_areas hM
  liquid_middle := det_liquid_middle hM
  middle_gas := det_middle_gas hM
  coincident := by
    intro p v ps hD h
    exact lt_irrefl v ((hM _ _ _ _ hD).1 h).1
  swapped := det_swapped hM
  asymm := by
    intro p vl vg ps hD h1 h2
    have hD' : PhysDomain p vg vl := by
      obtain ⟨a, b, U, hU, hs, hc⟩ := hD
      exact ⟨b, a, U, hU, Set.uIcc_comm vl vg ▸ hs, hc⟩
    exact lt_asymm ((hM _ _ _ _ hD).1 h1).1 ((hM _ _ _ _ hD').1 h2).1
  wrong_pressure := det_wrong_pressure hM
  equal_area_unequal_pressure := by
    intro ps c x hx hxc h
    have hD : PhysDomain (fun v => ps - (v - c)) (c - x) (c + x) :=
      physDomain_of_continuous (by fun_prop) (by linarith) (by linarith)
    obtain ⟨-, h1, -⟩ := (hM _ _ _ _ hD).1 h
    simp only at h1
    linarith
  sign_flipped_area := det_sign_flipped hM
  pressure_unique := by
    intro p vl vg ps ps' hD h1 h2
    exact ((hM _ _ _ _ hD).1 h1).2.1.symm.trans ((hM _ _ _ _ hD).1 h2).2.1
  local_ := by
    intro p q vl vg ps U hl hg hU hs hc he
    have hDp : PhysDomain p vl vg := ⟨hl, hg, U, hU, hs, hc⟩
    have hDq : PhysDomain q vl vg := ⟨hl, hg, U, hU, hs, hc.congr (fun v hv => (he hv).symm)⟩
    rw [hM _ _ _ _ hDp, hM _ _ _ _ hDq]
    exact mref_local p q vl vg ps U hs he
  add_const := by
    intro p vl vg ps c hD
    rw [hM _ _ _ _ (physDomain_add_const c hD), hM _ _ _ _ hD]
    exact mref_add_const p vl vg ps c hD
  smul_pos := by
    intro p vl vg ps k hk hD
    rw [hM _ _ _ _ (physDomain_smul k hD), hM _ _ _ _ hD]
    exact mref_smul p vl vg ps k hk.ne'
  translate := by
    intro p vl vg ps s hD hl hg
    rw [hM _ _ _ _ (physDomain_translate s hD hl hg), hM _ _ _ _ hD]
    exact mref_translate p vl vg ps s
  rescale_volume := by
    intro p vl vg ps k hk hD
    rw [hM _ _ _ _ (physDomain_rescale hk hD), hM _ _ _ _ hD]
    exact mref_rescale p vl vg ps k hk

/-- The textbook reference predicate satisfies the whole specification. -/
theorem ref_satisfies : MaxwellSpec MRef := of_determining (fun _ _ _ _ _ => Iff.rfl)

/-- PINNING. On the physical domain, any `M` meeting the spec coincides with `MRef`. -/
theorem pinning {M : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop} (hM : MaxwellSpec M)
    (p : ℝ → ℝ) (vl vg ps : ℝ) (hD : PhysDomain p vl vg) :
    M p vl vg ps ↔ MRef p vl vg ps :=
  hM.determining p vl vg ps hD

/-- The spec is equivalent to its determining law. -/
theorem spec_iff_determining {M : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop} :
    MaxwellSpec M ↔ ∀ (p : ℝ → ℝ) (vl vg ps : ℝ), PhysDomain p vl vg →
      (M p vl vg ps ↔ MRef p vl vg ps) :=
  ⟨fun h => pinning h, of_determining⟩

end Work.Fidelity.MaxwellSpec
