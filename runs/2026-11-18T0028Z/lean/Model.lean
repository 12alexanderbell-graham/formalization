import Checked.Trust.NecessityAP

namespace Checked.Trust.NCAQ

open Set Filter Topology MeasureTheory Real
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- The closed-form flat model with matter density above one (negative cosmological constant):
`a(s) = sin(s)^{2/3}`. -/
noncomputable def sa (s : ℝ) : ℝ := Real.sin s ^ (2 / 3 : ℝ)

theorem sin_pos_of (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) : 0 < Real.sin s :=
  Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])

theorem cos_pos_of (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) : 0 < Real.cos s :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

theorem sa_hasDerivAt (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) :
    HasDerivAt sa (Real.cos s * (2 / 3) * Real.sin s ^ ((2 / 3 : ℝ) - 1)) s :=
  (Real.hasDerivAt_sin s).rpow_const (Or.inl (sin_pos_of s h0 h1).ne')

theorem sa_pos (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) : 0 < sa s :=
  Real.rpow_pos_of_pos (sin_pos_of s h0 h1) _

theorem sa_hubble (s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) :
    hubble sa s = 2 / 3 * (Real.cos s / Real.sin s) := by
  have hS := sin_pos_of s h0 h1
  unfold hubble
  rw [(sa_hasDerivAt s h0 h1).deriv]
  simp only [sa]
  rw [Real.rpow_sub hS, Real.rpow_one]
  have : 0 < Real.sin s ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hS _
  field_simp

theorem cube23 (x : ℝ) (hx : 0 < x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

theorem sa_z3 (t₀ s : ℝ) (h0 : 0 < s) (h1 : s < π / 2) (h0' : 0 < t₀) (h1' : t₀ < π / 2) :
    (1 + redshift sa t₀ s) ^ 3 = Real.sin t₀ ^ 2 / Real.sin s ^ 2 := by
  have hS := sin_pos_of s h0 h1
  have hT := sin_pos_of t₀ h0' h1'
  unfold redshift
  rw [show 1 + (sa t₀ / sa s - 1) = sa t₀ / sa s by ring, div_pow]
  simp only [sa]
  rw [cube23 _ hS, cube23 _ hT]

/-- The flat law with `Ω cos² t₀ = 1` holds on `(0, t₀]`. -/
theorem sa_law (Ω t₀ : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) (hΩ : Ω * Real.cos t₀ ^ 2 = 1)
    (s : ℝ) (h0 : 0 < s) (hs : s ≤ t₀) :
    hubble sa s = hubble sa t₀ * √(Ω * (1 + redshift sa t₀ s) ^ 3 + 1 - Ω) := by
  have h1 : s < π / 2 := lt_of_le_of_lt hs h1'
  have hS := sin_pos_of s h0 h1
  have hT := sin_pos_of t₀ h0' h1'
  have hC := cos_pos_of s h0 h1
  have hCT := cos_pos_of t₀ h0' h1'
  rw [sa_z3 t₀ s h0 h1 h0' h1', sa_hubble s h0 h1, sa_hubble t₀ h0' h1']
  have e : Ω * (Real.sin t₀ ^ 2 / Real.sin s ^ 2) + 1 - Ω
      = (Real.sin t₀ / Real.cos t₀ * (Real.cos s / Real.sin s)) ^ 2 := by
    have hΩ' : Ω = 1 / Real.cos t₀ ^ 2 := by field_simp; linarith
    rw [hΩ']
    have := Real.sin_sq_add_cos_sq s
    have := Real.sin_sq_add_cos_sq t₀
    field_simp
    nlinarith
  rw [e, Real.sqrt_sq (by positivity)]
  field_simp

theorem sa_H0 (t₀ : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) : 0 < hubble sa t₀ := by
  rw [sa_hubble t₀ h0' h1']
  have := sin_pos_of t₀ h0' h1'; have := cos_pos_of t₀ h0' h1'; positivity

/-- A source time with `1 + z = Z` (any `Z ≥ 1`): `sin s = sin t₀ / Z^{3/2}`. -/
theorem sa_source (t₀ Z : ℝ) (h0' : 0 < t₀) (h1' : t₀ < π / 2) (hZ : 1 ≤ Z) :
    let s := Real.arcsin (Real.sin t₀ / Z ^ (3 / 2 : ℝ))
    0 < s ∧ s ≤ t₀ ∧ redshift sa t₀ s = Z - 1 := by
  intro s
  have hT := sin_pos_of t₀ h0' h1'
  have hZ0 : 0 < Z := by linarith
  have hZp : 1 ≤ Z ^ (3 / 2 : ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hZp0 : 0 < Z ^ (3 / 2 : ℝ) := by linarith
  set y := Real.sin t₀ / Z ^ (3 / 2 : ℝ) with hy
  have hy0 : 0 < y := div_pos hT hZp0
  have hyT : y ≤ Real.sin t₀ := div_le_self hT.le hZp
  have hT1 : Real.sin t₀ ≤ 1 := Real.sin_le_one _
  have hs0 : 0 < s := Real.arcsin_pos.2 hy0
  have hsT : s ≤ t₀ := by
    have := Real.arcsin_le_arcsin hyT
    rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)] at this
  have hss : Real.sin s = y := Real.sin_arcsin (by linarith) (by linarith)
  refine ⟨hs0, hsT, ?_⟩
  have h1 : s < π / 2 := lt_of_le_of_lt hsT h1'
  have h3 := sa_z3 t₀ s hs0 h1 h0' h1'
  rw [hss, hy, div_pow, ← Real.rpow_natCast (Z ^ (3 / 2 : ℝ)), ← Real.rpow_mul hZ0.le] at h3
  norm_num at h3
  have hT2 : Real.sin t₀ ^ 2 ≠ 0 := by positivity
  rw [div_div_eq_mul_div, mul_div_assoc, mul_div_cancel₀ _ hT2] at h3
  have hpos : 0 < 1 + redshift sa t₀ s := by
    unfold redshift; rw [show 1 + (sa t₀ / sa s - 1) = sa t₀ / sa s by ring]
    exact div_pos (sa_pos t₀ h0' h1') (sa_pos s hs0 h1)
  have : 1 + redshift sa t₀ s = Z := by
    have h3' : (1 + redshift sa t₀ s) ^ 3 = Z ^ 3 := by
      rw [h3]
    exact (pow_left_inj₀ hpos.le hZ0.le (by norm_num)).1 h3'
  linarith

end Checked.Trust.NCAQ
