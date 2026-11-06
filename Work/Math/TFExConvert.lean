import Mathlib
import Work.Math.TFExBase

/-!
# Thomas–Fermi existence: from t = √x back to x

A solution (U, Φ) of u' = 2tΦ, Φ' = 2u^{3/2} on [0, ∞) with U(0) = 1, U > 0 and U → 0 gives
y(x) = U(√x), φ(x) = Φ(√x) meeting every hypothesis of the Thomas–Fermi slope theorem.
-/

namespace Work.Math.TFExConvert
open Set Filter Topology Work.Math.TFExBase

theorem convert (U Φ : ℝ → ℝ)
    (hU : ∀ t, 0 ≤ t → HasDerivWithinAt U (2 * t * Φ t) (Ici 0) t)
    (hΦ : ∀ t, 0 ≤ t → HasDerivWithinAt Φ (2 * g (U t)) (Ici 0) t)
    (h0 : U 0 = 1) (hpos : ∀ t, 0 ≤ t → 0 < U t) (hlim : Tendsto U atTop (𝓝 0)) :
    ∃ y φ : ℝ → ℝ,
    (∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x) ∧
    (∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧ y 0 = 1 ∧ (∀ x, 0 ≤ x → 0 < y x) ∧
    Tendsto y atTop (𝓝 0) := by
  -- two-sided derivatives for t > 0
  have hU' : ∀ t, 0 < t → HasDerivAt U (2 * t * Φ t) t := fun t ht =>
    (hU t ht.le).hasDerivAt (Ici_mem_nhds ht)
  have hΦ' : ∀ t, 0 < t → HasDerivAt Φ (2 * g (U t)) t := fun t ht =>
    (hΦ t ht.le).hasDerivAt (Ici_mem_nhds ht)
  -- derivative of y for x > 0
  have hy' : ∀ x, 0 < x → HasDerivAt (fun x => U (Real.sqrt x)) (Φ (Real.sqrt x)) x := by
    intro x hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have h := (hU' _ hs).comp x (Real.hasDerivAt_sqrt hx.ne')
    refine h.congr_deriv ?_
    field_simp
  have hφ' : ∀ x, 0 < x → HasDerivAt (fun x => Φ (Real.sqrt x))
      (U (Real.sqrt x) ^ ((3 : ℝ) / 2) / Real.sqrt x) x := by
    intro x hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have h := (hΦ' _ hs).comp x (Real.hasDerivAt_sqrt hx.ne')
    refine h.congr_deriv ?_
    rw [g_eq_rpow (hpos _ hs.le).le]
    field_simp
  -- continuity at 0 from the right
  have hcU : ContinuousWithinAt (fun x => U (Real.sqrt x)) (Ici 0) 0 := by
    have h1 : ContinuousWithinAt U (Ici 0) (Real.sqrt 0) := by
      rw [Real.sqrt_zero]; exact (hU 0 le_rfl).continuousWithinAt
    exact h1.comp Real.continuous_sqrt.continuousWithinAt
      (fun x _ => Real.sqrt_nonneg x)
  have hcΦ : ContinuousWithinAt (fun x => Φ (Real.sqrt x)) (Ici 0) 0 := by
    have h1 : ContinuousWithinAt Φ (Ici 0) (Real.sqrt 0) := by
      rw [Real.sqrt_zero]; exact (hΦ 0 le_rfl).continuousWithinAt
    exact h1.comp Real.continuous_sqrt.continuousWithinAt
      (fun x _ => Real.sqrt_nonneg x)
  refine ⟨fun x => U (Real.sqrt x), fun x => Φ (Real.sqrt x), ?_, hφ', hcΦ, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx.lt_or_eq with hx | hx
    · exact (hy' x hx).hasDerivWithinAt
    · subst hx
      have hd : DifferentiableOn ℝ (fun x => U (Real.sqrt x)) (Ioi 0) :=
        fun x hx => (hy' x hx).differentiableAt.differentiableWithinAt
      have hlim' : Tendsto (fun x => deriv (fun x => U (Real.sqrt x)) x) (𝓝[>] 0)
          (𝓝 (Φ (Real.sqrt 0))) := by
        have h2 : Tendsto (fun x => Φ (Real.sqrt x)) (𝓝[>] 0) (𝓝 (Φ (Real.sqrt 0))) :=
          hcΦ.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
        refine h2.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hy' x hx).deriv.symm
      exact hasDerivWithinAt_Ici_of_tendsto_deriv hd
        (hcU.mono Ioi_subset_Ici_self) self_mem_nhdsWithin hlim'
  · simp [h0]
  · intro x hx; exact hpos _ (Real.sqrt_nonneg x)
  · exact hlim.comp Real.tendsto_sqrt_atTop

end Work.Math.TFExConvert
