import Mathlib
import Work.Math.LaneEmden4

/-!
# Lane–Emden index 4: the blind restatement closed in Lean

The blind restatement (run 2026-11-19T0428Z, `runs/2026-11-19T0428Z/blind/LaneEmden4Blind.lean`,
statement copied verbatim below) assumes θ continuous on [0, 16], θ(0) = 1, a right derivative 0
at the centre (`HasDerivWithinAt θ 0 (Ici 0) 0`), and on the open interval (0, 16) that θ and
`deriv θ` are differentiable with `deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + θ ξ ^ 4 = 0`.
The program's theorem `Work.Math.LaneEmden4.core` assumes θ' = φ within [0, 15], φ continuous
within [0, 15] at 0, and φ' = −(2/ξ)φ − θ⁴ on (0, 15].

**The bridge** (adapted from the index-three `Work.Math.LEBlindBridge`). Take
φ ξ = if ξ = 0 then 0 else θ'(ξ). The equation gives (ξ² θ')' = −ξ² θ⁴ on (0, 16). With C a bound
of |θ| on [0, 16] (compactness), u = ξ² θ' satisfies |u(x) − u(a)| ≤ C⁴x³ for 0 < a ≤ x < 16
(mean value inequality), and boundedness of θ forces |u(x)| ≤ C⁴x³: otherwise θ(s) + m/s would be
monotone on (0, x] for some m > 0, making θ unbounded near 0 (`upper_u`). Hence
|θ'(x)| ≤ C⁴x on (0, 16), so φ is continuous at 0; at 0 itself θ has derivative φ 0 = 0 within
[0, 15] by the right-derivative hypothesis. `core` then gives ξ₁ ∈ (0, 15) with the bounds stated
for φ ξ₁ = θ'(ξ₁) and positivity of θ on [0, ξ₁), which yields the `IsLeast` form.
-/

namespace Work.Math.LaneEmden4BlindClosed
open Set Filter Topology

/-- If u = x²D stays above u(x) − K on (0, x] and θ (derivative D) is bounded there, then
u(x) ≤ K. -/
theorem upper_u {θ D : ℝ → ℝ} {C K x : ℝ} (hx : 0 < x) (hC : 0 ≤ C)
    (hθb : ∀ s ∈ Ioc 0 x, |θ s| ≤ C)
    (hθd : ∀ s ∈ Ioc 0 x, HasDerivAt θ (D s) s)
    (hu : ∀ a ∈ Ioc 0 x, x ^ 2 * D x - K ≤ a ^ 2 * D a) :
    x ^ 2 * D x ≤ K := by
  by_contra hcon
  rw [not_le] at hcon
  set m := x ^ 2 * D x - K with hm
  have hm0 : 0 < m := by linarith
  have hmx : 0 < m / x := div_pos hm0 hx
  set den := 2 * C + m / x + 1 with hden
  have hden0 : 0 < den := by rw [hden]; linarith
  set a := m / den with ha
  have ha0 : 0 < a := div_pos hm0 hden0
  have hma : m * a⁻¹ = den := by rw [ha]; field_simp
  have hax : a < x := by
    rw [ha, div_lt_iff₀ hden0]
    have : x * den = 2 * C * x + m + x := by rw [hden]; field_simp
    rw [this]; nlinarith
  have hgd : ∀ s ∈ Icc a x, HasDerivAt (fun s => θ s + m * s⁻¹) (D s + m * (-(s ^ 2)⁻¹)) s := by
    intro s hs
    have hs0 : 0 < s := ha0.trans_le hs.1
    exact (hθd s ⟨hs0, hs.2⟩).add ((hasDerivAt_inv hs0.ne').const_mul m)
  have hg : MonotoneOn (fun s => θ s + m * s⁻¹) (Icc a x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a x)
    · exact fun s hs => (hgd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hgd s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs0 : 0 < s := ha0.trans hs.1
      rw [(hgd s (Ioo_subset_Icc_self hs)).deriv]
      have hu' := hu s ⟨hs0, hs.2.le⟩
      have hs2 : 0 < s ^ 2 := by positivity
      have : m * (s ^ 2)⁻¹ ≤ D s := by
        rw [← div_eq_mul_inv, div_le_iff₀ hs2]; linarith
      linarith
  have hmono := hg ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax.le
  simp only at hmono
  rw [hma] at hmono
  have h1 := hθb a ⟨ha0, hax.le⟩
  have h2 := hθb x ⟨hx, le_rfl⟩
  rw [abs_le] at h1 h2
  have hmx' : m * x⁻¹ = m / x := (div_eq_mul_inv m x).symm
  rw [hmx'] at hmono
  rw [hden] at hmono
  linarith

theorem u_diff {θ : ℝ → ℝ} {C a x : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hax : a ≤ x) (hx7 : x < 16)
    (hCb : ∀ s ∈ Icc (0 : ℝ) 16, |θ s| ≤ C)
    (hode : ∀ ξ ∈ Ioo (0 : ℝ) 16, DifferentiableAt ℝ θ ξ ∧
      HasDerivAt (fun x => x ^ 2 * deriv θ x) (-(ξ ^ 2 * θ ξ ^ 4)) ξ) :
    |x ^ 2 * deriv θ x - a ^ 2 * deriv θ a| ≤ C ^ 4 * x ^ 3 := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => s ^ 2 * deriv θ s) (f' := fun s => -(s ^ 2 * θ s ^ 4)) (C := x ^ 2 * C ^ 4)
    (s := Icc a x)
    (fun s hs => (hode s ⟨ha.trans_le hs.1, hs.2.trans_lt hx7⟩).2.hasDerivWithinAt)
    (fun s hs => by
      have hs0 : 0 ≤ s := ha.le.trans hs.1
      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg s), abs_pow]
      have h1 : |θ s| ^ 4 ≤ C ^ 4 :=
        pow_le_pow_left₀ (abs_nonneg _) (hCb s ⟨hs0, hs.2.trans hx7.le⟩) 4
      have h2 : s ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hs0 hs.2 2
      exact mul_le_mul h2 h1 (by positivity) (by positivity))
    (convex_Icc a x) (left_mem_Icc.2 hax) (right_mem_Icc.2 hax)
  simp only [Real.norm_eq_abs] at h
  rw [abs_of_nonneg (by linarith : 0 ≤ x - a)] at h
  have hx0 : 0 < x := ha.trans_le hax
  calc |x ^ 2 * deriv θ x - a ^ 2 * deriv θ a| ≤ x ^ 2 * C ^ 4 * (x - a) := h
    _ ≤ x ^ 2 * C ^ 4 * x := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = C ^ 4 * x ^ 3 := by ring

/-- |θ'(x)| ≤ C⁴x on (0, 16) when |θ| ≤ C on [0, 16]. -/
theorem deriv_bound {θ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hCb : ∀ s ∈ Icc (0 : ℝ) 16, |θ s| ≤ C)
    (hode : ∀ ξ ∈ Ioo (0 : ℝ) 16, DifferentiableAt ℝ θ ξ ∧
      HasDerivAt (fun x => x ^ 2 * deriv θ x) (-(ξ ^ 2 * θ ξ ^ 4)) ξ) :
    ∀ x ∈ Ioo (0 : ℝ) 16, |deriv θ x| ≤ C ^ 4 * x := by
  intro x hx
  have hb : ∀ s ∈ Ioc 0 x, |θ s| ≤ C := fun s hs => hCb s ⟨hs.1.le, hs.2.trans hx.2.le⟩
  have hd : ∀ s ∈ Ioc 0 x, HasDerivAt θ (deriv θ s) s := fun s hs =>
    (hode s ⟨hs.1, hs.2.trans_lt hx.2⟩).1.hasDerivAt
  have hud : ∀ a ∈ Ioc 0 x, |x ^ 2 * deriv θ x - a ^ 2 * deriv θ a| ≤ C ^ 4 * x ^ 3 :=
    fun a ha => u_diff hC ha.1 ha.2 hx.2 hCb hode
  have up := upper_u (D := deriv θ) (K := C ^ 4 * x ^ 3) hx.1 hC hb hd
    (fun a ha => by have := (abs_le.1 (hud a ha)).2; linarith)
  have lo := upper_u (θ := fun s => -θ s) (D := fun s => -deriv θ s) (K := C ^ 4 * x ^ 3) hx.1 hC
    (fun s hs => by rw [abs_neg]; exact hb s hs) (fun s hs => (hd s hs).neg)
    (fun a ha => by have := (abs_le.1 (hud a ha)).1; linarith)
  have hx2 : 0 < x ^ 2 := pow_pos hx.1 2
  rw [abs_le]
  constructor
  · by_contra h
    rw [not_le] at h
    have : x ^ 2 * (C ^ 4 * x) < x ^ 2 * -deriv θ x := mul_lt_mul_of_pos_left (by linarith) hx2
    nlinarith
  · by_contra h
    rw [not_le] at h
    have : x ^ 2 * (C ^ 4 * x) < x ^ 2 * deriv θ x := mul_lt_mul_of_pos_left h hx2
    nlinarith

/-- The blind form of the equation gives (ξ² θ')' = −ξ² θ⁴ on (0, 16). -/
theorem ode_u (θ : ℝ → ℝ)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 16,
      DifferentiableAt ℝ θ ξ ∧ DifferentiableAt ℝ (deriv θ) ξ ∧
        deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + θ ξ ^ 4 = 0) :
    ∀ ξ ∈ Ioo (0 : ℝ) 16, DifferentiableAt ℝ θ ξ ∧
      HasDerivAt (fun x => x ^ 2 * deriv θ x) (-(ξ ^ 2 * θ ξ ^ 4)) ξ := by
  intro ξ hξ
  obtain ⟨h1, h2, h3⟩ := hode ξ hξ
  refine ⟨h1, ?_⟩
  have hd := (hasDerivAt_pow 2 ξ).mul h2.hasDerivAt
  convert hd using 1
  have hne : ξ ≠ 0 := hξ.1.ne'
  have h3' : deriv (deriv θ) ξ = -(2 / ξ * deriv θ ξ) - θ ξ ^ 4 := by linarith
  rw [h3']
  field_simp
  ring

/-- The bridge: the blind hypotheses give the program's hypotheses on [0, 15] for
φ = θ' (with φ 0 = 0). -/
theorem bridge (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Icc 0 16))
    (hd0 : HasDerivWithinAt θ 0 (Ici 0) 0)
    (hode : ∀ ξ ∈ Ioo (0 : ℝ) 16, DifferentiableAt ℝ θ ξ ∧
      HasDerivAt (fun x => x ^ 2 * deriv θ x) (-(ξ ^ 2 * θ ξ ^ 4)) ξ) :
    let φ : ℝ → ℝ := fun ξ => if ξ = 0 then 0 else deriv θ ξ
    (∀ ξ ∈ Icc (0 : ℝ) 15, HasDerivWithinAt θ (φ ξ) (Icc 0 15) ξ) ∧
    ContinuousWithinAt φ (Icc 0 15) 0 ∧
    (∀ ξ ∈ Ioc (0 : ℝ) 15,
      HasDerivWithinAt φ (-(2 / ξ * φ ξ) - θ ξ ^ 4) (Icc 0 15) ξ) := by
  intro φ
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set C := max C0 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  have hCb : ∀ s ∈ Icc (0 : ℝ) 16, |θ s| ≤ C := fun s hs =>
    (Real.norm_eq_abs _ ▸ hC0 s hs).trans (le_max_left _ _)
  have hbd := deriv_bound hC hCb hode
  refine ⟨fun ξ hξ => ?_, ?_, fun ξ hξ => ?_⟩
  · rcases eq_or_lt_of_le hξ.1 with h | h
    · subst h
      have : φ 0 = 0 := by simp [φ]
      rw [this]
      exact hd0.mono Icc_subset_Ici_self
    · have hne : ξ ≠ 0 := h.ne'
      have : φ ξ = deriv θ ξ := by simp [φ, hne]
      rw [this]
      exact (hode ξ ⟨h, by linarith [hξ.2]⟩).1.hasDerivAt.hasDerivWithinAt
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / (C ^ 4 + 1), by positivity, fun x hx hxd => ?_⟩
    have hφ0 : φ 0 = 0 := by simp [φ]
    rw [hφ0, Real.dist_eq, sub_zero]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1] at hxd
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; simp [φ, hε]
    · have hne : x ≠ 0 := h.ne'
      have : φ x = deriv θ x := by simp [φ, hne]
      rw [this]
      have hb := hbd x ⟨h, by linarith [hx.2]⟩
      have hC1 : 0 < C ^ 4 + 1 := by positivity
      have : x * (C ^ 4 + 1) < ε := by rwa [lt_div_iff₀ hC1] at hxd
      nlinarith [pow_nonneg hC 4]
  · have h0 : 0 < ξ := hξ.1
    have hξ7 : ξ ∈ Ioo (0 : ℝ) 16 := ⟨h0, by linarith [hξ.2]⟩
    have hne : ξ ≠ 0 := h0.ne'
    have hu := (hode ξ hξ7).2
    have hq := hu.div (hasDerivAt_pow 2 ξ) (pow_ne_zero 2 hne)
    have hev : φ =ᶠ[𝓝 ξ] fun x => x ^ 2 * deriv θ x / x ^ 2 := by
      filter_upwards [lt_mem_nhds h0] with x hx
      have hxne : x ≠ 0 := hx.ne'
      simp only [φ, hxne, ite_false]
      field_simp
    have hφξ : φ ξ = deriv θ ξ := by simp [φ, hne]
    have hfin := hq.congr_of_eventuallyEq hev
    apply HasDerivAt.hasDerivWithinAt
    convert hfin using 1
    rw [hφξ]
    field_simp
    ring

theorem blind_laneEmden4 (θ : ℝ → ℝ)
    (hcont : ContinuousOn θ (Set.Icc 0 16))
    (h0 : θ 0 = 1)
    (hd0 : HasDerivWithinAt θ 0 (Set.Ici 0) 0)
    (hode : ∀ ξ ∈ Set.Ioo (0 : ℝ) 16,
      DifferentiableAt ℝ θ ξ ∧ DifferentiableAt ℝ (deriv θ) ξ ∧
        deriv (deriv θ) ξ + 2 / ξ * deriv θ ξ + θ ξ ^ 4 = 0) :
    ∃ ξ₁ : ℝ,
      IsLeast {ξ : ℝ | ξ ∈ Set.Icc (0 : ℝ) 16 ∧ θ ξ = 0} ξ₁ ∧
      (14.97154634 ≤ ξ₁ ∧ ξ₁ ≤ 14.97154636) ∧
      (1.79722991 ≤ -ξ₁ ^ 2 * deriv θ ξ₁ ∧ -ξ₁ ^ 2 * deriv θ ξ₁ ≤ 1.79722992) ∧
      (622.407879 ≤ ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ∧
        ξ₁ ^ 3 / (3 * (-ξ₁ ^ 2 * deriv θ ξ₁)) ≤ 622.407886) := by
  obtain ⟨hθ1, hφ0, hφ⟩ := bridge θ hcont hd0 (ode_u θ hode)
  obtain ⟨ξ₁, ha, hb, hz, hpos, hω1, hω2, hc1, hc2⟩ :=
    Work.Math.LaneEmden4.core θ _ hθ1 hφ0 hφ h0
  have hne : ξ₁ ≠ 0 := by intro h; rw [h] at ha; norm_num at ha
  simp only [hne, ite_false] at hω1 hω2 hc1 hc2
  simp only [neg_mul]
  refine ⟨ξ₁, ⟨⟨⟨by linarith, by linarith⟩, hz⟩, fun ξ hξ => ?_⟩, ⟨ha, hb⟩, ⟨hω1, hω2⟩, ⟨hc1, hc2⟩⟩
  by_contra hlt
  rw [not_le] at hlt
  have := hpos ξ ⟨hξ.1.1, hlt⟩
  rw [hξ.2] at this
  exact lt_irrefl _ this

end Work.Math.LaneEmden4BlindClosed
