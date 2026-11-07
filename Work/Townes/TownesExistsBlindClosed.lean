import Mathlib
import Work.Townes.TownesExistsBlind
import Work.Townes.TownesExists

/-!
# Townes existence: the blind restatement, closed

The blind restater's statement `Blind.TownesExists.ground_state_exists` (run 2026-11-07T0628Z:
θ is C² on all of ℝ, θ'(0) = 0, the radial ODE with `deriv` for r > 0, θ > 0 on [0, ∞),
θ → 0) follows from the program's frozen `Work.Townes.Exists.townes_exists` (one-sided
derivative at 0, φ continuous at 0, the ODE for φ on (0, ∞)): take the even extension
Θ(r) = θ(|r|). At 0, (rφ)' = r(θ − θ³) and l'Hôpital give φ(r)/r → (c − c³)/2, so the
second derivative extends continuously with Θ''(0) = (c − c³)/2.
-/

namespace Work.Townes.ExistsBlindClosed
open Set Filter Topology

/-- The program's conclusion data give the blind restater's radial profile. -/
theorem of_program (c : ℝ) (θ φ : ℝ → ℝ) (h0 : θ 0 = c) (hφ00 : φ 0 = 0)
    (hθ : ∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r)
    (hφc : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r)
    (hpos : ∀ r ∈ Ici (0 : ℝ), 0 < θ r) (hlim : Tendsto θ atTop (𝓝 0)) :
    ∃ Θ : ℝ → ℝ, Blind.TownesExists.IsRadialProfile Θ ∧ Θ 0 = c := by
  set ψ : ℝ → ℝ := fun s => -(1 / s * φ s) + θ s - θ s ^ 3 with hψ
  set L : ℝ := (c - c ^ 3) / 2 with hL
  -- continuity facts
  have hθc : ContinuousWithinAt θ (Ici 0) 0 := (hθ 0 (mem_Ici.2 le_rfl)).continuousWithinAt
  have hθat : ∀ r, 0 < r → HasDerivAt θ (φ r) r := fun r hr =>
    (hθ r (le_of_lt hr)).hasDerivAt (Ici_mem_nhds hr)
  have hθ0' : Tendsto θ (𝓝[>] 0) (𝓝 c) := by
    rw [← h0]; exact hθc.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hφ0' : Tendsto φ (𝓝[>] 0) (𝓝 0) := by
    have := hφc.tendsto; rw [hφ00] at this
    exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  -- l'Hôpital: φ s / s → L
  have hratio : Tendsto (fun s => φ s / s) (𝓝[>] 0) (𝓝 L) := by
    have hf : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s => s * φ s) (1 * φ x + x * ψ x) x :=
      fun x hx => (hasDerivAt_id x).mul (hφ x hx.1)
    have hg : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := fun x _ => by
      simpa using hasDerivAt_pow 2 x
    have hg' : ∀ x ∈ Ioo (0 : ℝ) 1, 2 * x ≠ 0 := fun x hx => by
      have := hx.1; positivity
    have hfa : Tendsto (fun s => s * φ s) (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto (0 : ℝ))).mul hφ0'
      simpa using this
    have hga : Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) ((continuous_pow 2).tendsto (0 : ℝ))
      simpa using this
    have hdiv : Tendsto (fun x => (1 * φ x + x * ψ x) / (2 * x)) (𝓝[>] 0) (𝓝 L) := by
      have hlim' : Tendsto (fun x => (θ x - θ x ^ 3) / 2) (𝓝[>] 0) (𝓝 L) :=
        ((hθ0'.sub (hθ0'.pow 3)).div_const 2)
      refine hlim'.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      simp only [hψ]
      field_simp
      ring
    have := HasDerivAt.lhopital_zero_right_on_Ioo (by norm_num : (0 : ℝ) < 1) hf hg hg' hfa hga
      hdiv
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp
  have hψlim : Tendsto ψ (𝓝[>] 0) (𝓝 L) := by
    have h := ((hratio.neg).add hθ0').sub (hθ0'.pow 3)
    have e : -L + c - c ^ 3 = L := by rw [hL]; ring
    rw [e] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [hψ]; ring
  -- the even extension and its derivatives
  set Θ : ℝ → ℝ := fun r => θ |r| with hΘ
  set D : ℝ → ℝ := fun r => if 0 ≤ r then φ r else -φ (-r) with hD
  set E : ℝ → ℝ := fun r => if r = 0 then L else ψ |r| with hE
  have hΘd : ∀ r, HasDerivAt Θ (D r) r := by
    intro r
    rcases lt_trichotomy r 0 with hr | hr | hr
    · have hc : HasDerivAt (fun x => θ (-x)) (φ (-r) * (-1)) r :=
        (hθat (-r) (by linarith)).comp r (hasDerivAt_neg r)
      have heq : (fun x => θ (-x)) =ᶠ[𝓝 r] Θ := by
        filter_upwards [Iio_mem_nhds hr] with x hx
        simp [hΘ, abs_of_neg (show x < 0 from hx)]
      have hDr : D r = φ (-r) * (-1) := by simp [hD, not_le.2 hr]
      rw [hDr]; exact hc.congr_of_eventuallyEq heq.symm
    · subst hr
      have hD0 : D 0 = 0 := by simp [hD, hφ00]
      rw [hD0]
      have hR : HasDerivWithinAt Θ 0 (Ici 0) 0 := by
        have := hθ 0 (mem_Ici.2 le_rfl)
        rw [hφ00] at this
        refine this.congr (fun x hx => ?_) (by simp [hΘ])
        simp [hΘ, abs_of_nonneg (show (0 : ℝ) ≤ x from hx)]
      have hLft : HasDerivWithinAt Θ 0 (Iic 0) 0 := by
        have h1 := hθ 0 (mem_Ici.2 le_rfl)
        rw [hφ00] at h1
        have h2 : HasDerivWithinAt (fun x => θ (-x)) (0 * (-1)) (Iic 0) 0 := by
          have h1' : HasDerivWithinAt θ 0 (Ici 0) (-(0 : ℝ)) := by rw [neg_zero]; exact h1
          have := h1'.comp (0 : ℝ) ((hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt (s := Iic 0))
            (fun x hx => by simp only [mem_Ici, mem_Iic] at hx ⊢; linarith)
          simpa [Function.comp_def] using this
        simp only [zero_mul] at h2
        refine h2.congr (fun x hx => ?_) (by simp [hΘ])
        simp [hΘ, abs_of_nonpos (show x ≤ 0 from hx)]
      have := hLft.union hR
      rw [Iic_union_Ici] at this
      exact this.hasDerivAt univ_mem
    · have heq : θ =ᶠ[𝓝 r] Θ := by
        filter_upwards [Ioi_mem_nhds hr] with x hx
        simp [hΘ, abs_of_pos (show 0 < x from hx)]
      have hDr : D r = φ r := by simp [hD, hr.le]
      rw [hDr]; exact (hθat r hr).congr_of_eventuallyEq heq.symm
  have hDd : ∀ r, HasDerivAt D (E r) r := by
    intro r
    rcases lt_trichotomy r 0 with hr | hr | hr
    · have hc : HasDerivAt (fun x => -φ (-x)) (-(ψ (-r) * (-1))) r :=
        ((hφ (-r) (by simp; linarith)).comp r (hasDerivAt_neg r)).neg
      have heq : (fun x => -φ (-x)) =ᶠ[𝓝 r] D := by
        filter_upwards [Iio_mem_nhds hr] with x hx
        simp [hD, not_le.2 (show x < 0 from hx)]
      have hEr : E r = -(ψ (-r) * (-1)) := by
        simp [hE, hr.ne, abs_of_neg hr]
      rw [hEr]; exact hc.congr_of_eventuallyEq heq.symm
    · subst hr
      have hE0 : E 0 = L := by simp [hE]
      rw [hE0]
      have hφd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt φ (ψ x) x := fun x hx => hφ x hx
      have hdiff : DifferentiableOn ℝ φ (Ioi 0) := fun x hx =>
        (hφd x hx).differentiableAt.differentiableWithinAt
      have hderiv : Tendsto (deriv φ) (𝓝[>] 0) (𝓝 L) := by
        refine hψlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact ((hφd x hx).deriv).symm
      have hR0 : HasDerivWithinAt φ L (Ici 0) 0 :=
        hasDerivWithinAt_Ici_of_tendsto_deriv hdiff (hφc.mono Ioi_subset_Ici_self)
          self_mem_nhdsWithin hderiv
      have hR : HasDerivWithinAt D L (Ici 0) 0 := by
        refine hR0.congr (fun x hx => ?_) (by simp [hD])
        simp [hD, show (0 : ℝ) ≤ x from hx]
      have hLft : HasDerivWithinAt D L (Iic 0) 0 := by
        have h2 : HasDerivWithinAt (fun x => -φ (-x)) (-(L * (-1))) (Iic 0) 0 := by
          have hR0' : HasDerivWithinAt φ L (Ici 0) (-(0 : ℝ)) := by rw [neg_zero]; exact hR0
          have := hR0'.comp (0 : ℝ) ((hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt (s := Iic 0))
            (fun x hx => by simp only [mem_Ici, mem_Iic] at hx ⊢; linarith)
          exact this.neg
        have e : -(L * (-1)) = L := by ring
        rw [e] at h2
        refine h2.congr (fun x hx => ?_) (by simp [hD, hφ00])
        rcases (show x ≤ 0 from hx).lt_or_eq with h | h
        · simp [hD, not_le.2 h]
        · subst h; simp [hD, hφ00]
      have := hLft.union hR
      rw [Iic_union_Ici] at this
      exact this.hasDerivAt univ_mem
    · have hEr : E r = ψ r := by simp [hE, hr.ne', abs_of_pos hr]
      have heq : φ =ᶠ[𝓝 r] D := by
        filter_upwards [Ioi_mem_nhds hr] with x hx
        simp [hD, (show 0 < x from hx).le]
      rw [hEr]; exact (hφ r hr).congr_of_eventuallyEq heq.symm
  -- continuity of E
  have hψc : ContinuousOn ψ (Ioi 0) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : ContinuousAt (fun s : ℝ => 1 / s) x :=
      continuousAt_const.div continuousAt_id hx0
    have h2 := ((h1.mul (hφ x hx).differentiableAt.continuousAt).neg.add
      (hθat x hx).continuousAt).sub ((hθat x hx).continuousAt.pow 3)
    exact h2.continuousWithinAt
  have hEc : Continuous E := by
    rw [continuous_iff_continuousAt]
    intro r
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      have habs : Tendsto (fun r : ℝ => |r|) (𝓝[≠] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
          simpa [Function.comp_def] using this
        · filter_upwards [self_mem_nhdsWithin] with x hx
          exact abs_pos.2 hx
      have h1 : Tendsto E (𝓝[≠] 0) (𝓝 L) := by
        refine (hψlim.comp habs).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        simp [hE, show x ≠ 0 from hx]
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, show E 0 = L by simp [hE]]
      exact h1
    · have hpos' : 0 < |r| := abs_pos.2 hr
      have hcont : ContinuousAt (fun x => ψ |x|) r :=
        ((hψc |r| hpos').continuousAt (Ioi_mem_nhds hpos')).comp continuous_abs.continuousAt
      refine hcont.congr ?_
      filter_upwards [isOpen_compl_singleton.mem_nhds hr] with x hx
      simp [hE, show x ≠ 0 from hx]
  -- assemble
  have hdΘ : deriv Θ = D := funext fun r => (hΘd r).deriv
  have hdD : deriv D = E := funext fun r => (hDd r).deriv
  have hC2 : ContDiff ℝ 2 Θ := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun r => (hΘd r).differentiableAt, by simp, ?_⟩
    rw [hdΘ, show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun r => (hDd r).differentiableAt, by simp, ?_⟩
    rw [hdD]; exact contDiff_zero.2 hEc
  refine ⟨Θ, ⟨hC2, ?_, ?_, ?_, ?_⟩, by simp [hΘ, h0]⟩
  · rw [hdΘ]; simp [hD, hφ00]
  · intro r hr
    rw [hdΘ, hdD]
    simp only [hE, hD, hΘ, hr.ne', hr.le, ite_false, ite_true, abs_of_pos hr, hψ]
    ring
  · intro r hr
    simp only [hΘ, abs_of_nonneg hr]; exact hpos r hr
  · refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    simp [hΘ, abs_of_nonneg hx]

/-- The blind restatement follows from the program's frozen `townes_exists`. -/
theorem closed : ∃ θ : ℝ → ℝ, Blind.TownesExists.IsRadialProfile θ ∧
    (2.2062008646 : ℝ) < θ 0 ∧ θ 0 < (2.2062008647 : ℝ) := by
  obtain ⟨c, hc, θ, φ, h0, hφ0, hθ, hφc, hφ, hpos, -, hlim⟩ := Work.Townes.Exists.townes_exists
  obtain ⟨Θ, hΘ, hΘ0⟩ := of_program c θ φ h0 hφ0 hθ hφc hφ hpos hlim
  exact ⟨Θ, hΘ, hΘ0 ▸ hc.1, hΘ0 ▸ hc.2⟩

end Work.Townes.ExistsBlindClosed
