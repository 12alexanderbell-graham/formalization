import Checked.Trust.NonVacuity
import Checked.FalknerSkan.NegWindow
import Checked.FalknerSkan.NegWallShear
import Checked.FalknerSkan.NegWallShearRows
import Checked.FalknerSkan.NegReversed
import Checked.FalknerSkan.NegReversedWallShear
import Checked.Records.FalknerSkan
import Checked.FalknerSkan.NegDecay
import Checked.Trust.NecessityE

/-! Hypothesis necessity for the Falkner–Skan window headlines with adverse pressure gradient, second batch
(run 2026-11-12T1628Z). The edge condition on the velocity follows from the other hypotheses (the velocity
increases, cannot stay below the edge value because the decay condition then forces a shear at least one,
and cannot pass above it because the equation then makes the shear decrease while the decay condition forces
it to grow); the relation between velocity and shear is needed (a velocity profile that reaches the edge value
at a finite height, the shear from the equation by an integrating factor); positivity of the shear is needed
where a reverse-flow solution is certified. -/

namespace Checked.Trust.NCS

open Set Filter Topology

theorem monoOn_of_deriv {g g' : ℝ → ℝ} {a : ℝ}
    (h : ∀ η ∈ Ici a, HasDerivWithinAt g (g' η) (Ici a) η) (h0 : ∀ η ∈ Ici a, 0 ≤ g' η) :
    MonotoneOn g (Ici a) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := g') (convex_Ici a)
    (HasDerivWithinAt.continuousOn (fun x hx => h x hx)) (fun x hx => ?_) (fun x hx => ?_)
  · exact (h x (interior_subset hx)).mono interior_subset
  · exact h0 x (interior_subset hx)

theorem restrict {g g' : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η) :
    ∀ η ∈ Ici a, HasDerivWithinAt g (g' η) (Ici a) η :=
  fun η hη => (h η (mem_Ici.2 (le_trans ha hη))).mono (Ici_subset_Ici.2 ha)

/-- With a nonpositive pressure-gradient coefficient, the edge condition on the velocity follows from the other
hypotheses of the window headlines. -/
theorem lim_one (β : ℝ) (hβ : β ≤ 0) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 ≤ q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    Tendsto p atTop (𝓝 1) := by
  have pmono : MonotoneOn p (Ici 0) := monoOn_of_deriv hp (fun η hη => hpos η hη)
  rw [tendsto_order]
  constructor
  · intro a ha
    by_contra hne
    have hle : ∀ η ∈ Ici (0 : ℝ), p η ≤ a := by
      intro η hη
      by_contra h
      push Not at h
      apply hne
      filter_upwards [eventually_ge_atTop η] with x hx
      exact lt_of_lt_of_le h (pmono hη (mem_Ici.2 (le_trans hη hx)) hx)
    have h1a : 0 < 1 - a := by linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((hdec (1 / (1 - a))).and (eventually_ge_atTop 0))
    have hN0 : 0 ≤ N := (hN N le_rfl).2
    have hq1 : ∀ η ∈ Ici N, 1 ≤ q η := by
      intro η hη
      obtain ⟨h, h0⟩ := hN η hη
      have : 1 ≤ 1 / (1 - a) * (1 - p η) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h1a]; linarith [hle η h0]
      linarith
    have hm : MonotoneOn (fun η => p η - η) (Ici N) := by
      refine monoOn_of_deriv (g' := fun η => q η - 1) (fun η hη => ?_)
        (fun η hη => by linarith [hq1 η hη])
      exact ((restrict hN0 hp) η hη).sub (hasDerivWithinAt_id η _)
    have hx : N ≤ N + (a - p N + 1) := by linarith [hle N hN0]
    have := hm (mem_Ici.2 le_rfl) hx hx
    simp only at this
    linarith [hle (N + (a - p N + 1)) (mem_Ici.2 (le_trans hN0 hx))]
  · intro b hb
    by_contra hne
    obtain ⟨η₀, h0, hη₀⟩ : ∃ η₀, 0 ≤ η₀ ∧ b ≤ p η₀ := by
      by_contra h
      push Not at h
      exact hne (Filter.eventually_atTop.2 ⟨0, fun η hη => h η hη⟩)
    have hge : ∀ η ∈ Ici η₀, b ≤ p η :=
      fun η hη => hη₀.trans (pmono (mem_Ici.2 h0) (mem_Ici.2 (le_trans h0 hη)) hη)
    have hfm : MonotoneOn (fun η => f η - η) (Ici η₀) := by
      refine monoOn_of_deriv (g' := fun η => p η - 1) (fun η hη => ?_)
        (fun η hη => by linarith [hge η hη])
      exact ((restrict h0 hf) η hη).sub (hasDerivWithinAt_id η _)
    obtain ⟨η₁, hη₁⟩ : ∃ η₁, η₁ = max η₀ (η₀ - f η₀ + 1) := ⟨_, rfl⟩
    have h10 : η₀ ≤ η₁ := hη₁ ▸ le_max_left _ _
    have h11 : η₀ - f η₀ + 1 ≤ η₁ := hη₁ ▸ le_max_right _ _
    have hfpos : ∀ η ∈ Ici η₁, 0 < f η := by
      intro η hη
      have hη' : η₁ ≤ η := hη
      have := hfm (mem_Ici.2 le_rfl) (mem_Ici.2 (le_trans h10 hη')) (le_trans h10 hη')
      simp only at this
      linarith
    have h1 : 0 ≤ η₁ := le_trans h0 h10
    have hqa : AntitoneOn q (Ici η₁) := by
      have hneg : MonotoneOn (fun η => -q η) (Ici η₁) := by
        refine monoOn_of_deriv (g' := fun η => -(-(f η * q η) - β * (1 - p η ^ 2)))
          (fun η hη => ((restrict h1 hq) η hη).neg) (fun η hη => ?_)
        have hη' : η₁ ≤ η := hη
        have hp1 : 1 ≤ p η := by linarith [hge η (mem_Ici.2 (le_trans h10 hη'))]
        have hqp := hpos η (mem_Ici.2 (le_trans h1 hη'))
        have hfp := hfpos η hη
        have hsq : 0 ≤ p η ^ 2 - 1 := by nlinarith
        have : 0 ≤ -β * (p η ^ 2 - 1) := mul_nonneg (by linarith) hsq
        nlinarith [mul_nonneg hfp.le hqp]
      intro x hx y hy hxy
      have := hneg hx hy hxy
      simp only at this
      linarith
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hdec (-(q η₁ + 1) / (b - 1)))
    obtain ⟨x, hxdef⟩ : ∃ x, x = max N η₁ := ⟨_, rfl⟩
    have hx1 : η₁ ≤ x := hxdef ▸ le_max_right _ _
    have hA := hN x (hxdef ▸ le_max_left _ _)
    have hB := hqa (mem_Ici.2 le_rfl) (mem_Ici.2 hx1) hx1
    have hpx : b ≤ p x := hge x (mem_Ici.2 (le_trans h10 hx1))
    have hb1 : 0 < b - 1 := by linarith
    have hQ : 0 < q η₁ + 1 := by linarith [hpos η₁ (mem_Ici.2 h1)]
    have : q η₁ + 1 ≤ -(q η₁ + 1) / (b - 1) * (1 - p x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hb1]; nlinarith
    linarith

/-! The edge condition on the velocity is redundant. -/

theorem fs_neg_tenth_window_r6 : dropped% Checked.FalknerSkan.NegWindow.fs_neg_tenth_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWindow.fs_neg_tenth_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

theorem fs_neg_wall_shear_window_r6 :
    dropped% Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

theorem fs_neg_wall_shear_17_window_r6 :
    dropped% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

theorem fs_neg_wall_shear_18_window_r6 :
    dropped% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

theorem fs_neg_wall_shear_19_window_r6 :
    dropped% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

theorem F13_wall_shear_r6 : dropped% Checked.Records.F13_wall_shear 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.Records.F13_wall_shear f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

/-! The relation between velocity and shear dropped: the velocity reaches the edge value at a finite height and stays
there, the stream function is its primitive, and the shear solves the equation by an integrating factor. -/

noncomputable def P2 (η : ℝ) : ℝ := min η 1
noncomputable def F2 (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, P2 s
noncomputable def G2 (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, F2 s
noncomputable def S2 (s : ℝ) : ℝ := Real.exp (G2 s) * (1 - P2 s ^ 2)
noncomputable def Q2 (c η : ℝ) : ℝ := Real.exp (-G2 η) * (1 + c * ∫ s in (0 : ℝ)..η, S2 s)

theorem P2_cont : Continuous P2 := continuous_id.min continuous_const

theorem F2_deriv (η : ℝ) : HasDerivAt F2 (P2 η) η :=
  (P2_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem F2_cont : Continuous F2 :=
  continuous_iff_continuousAt.2 fun η => (F2_deriv η).continuousAt

theorem G2_deriv (η : ℝ) : HasDerivAt G2 (F2 η) η :=
  (F2_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem G2_cont : Continuous G2 :=
  continuous_iff_continuousAt.2 fun η => (G2_deriv η).continuousAt

theorem S2_cont : Continuous S2 :=
  (Real.continuous_exp.comp G2_cont).mul (continuous_const.sub (P2_cont.pow 2))

theorem I2_deriv (η : ℝ) : HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, S2 s) (S2 η) η :=
  (S2_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem Q2_deriv (c η : ℝ) : HasDerivAt (Q2 c) (-(F2 η * Q2 c η) + c * (1 - P2 η ^ 2)) η := by
  have h := ((G2_deriv η).neg.exp).mul (((I2_deriv η).const_mul c).const_add 1)
  refine h.congr_deriv ?_
  simp only [S2, Q2]
  have e : Real.exp (-G2 η) * Real.exp (G2 η) = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination (c * (1 - P2 η ^ 2)) * e

theorem S2_nonneg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ S2 u := by
  have h0 : 0 ≤ P2 u := le_min hu zero_le_one
  have h1 : P2 u ≤ 1 := min_le_right _ _
  exact mul_nonneg (Real.exp_pos _).le (by nlinarith)

theorem Q2_pos (c : ℝ) (hc : 0 ≤ c) (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) : 0 < Q2 c η := by
  have hI : 0 ≤ ∫ s in (0 : ℝ)..η, S2 s :=
    intervalIntegral.integral_nonneg hη (fun u hu => S2_nonneg u hu.1)
  exact mul_pos (Real.exp_pos _) (by nlinarith)

theorem Q2_zero (c : ℝ) : Q2 c 0 = 1 := by simp [Q2, G2]
theorem F2_zero : F2 0 = 0 := by simp [F2]
theorem P2_zero : P2 0 = 0 := by simp [P2]

theorem P2_eq (η : ℝ) (hη : 1 ≤ η) : P2 η = 1 := min_eq_right hη

theorem P2_lim : Tendsto P2 atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with η hη; rw [P2_eq η hη])

theorem P2_decay (c : ℝ) (hc : 0 ≤ c) : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P2 η) ≤ Q2 c η := by
  intro M
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with η hη
  rw [P2_eq η hη, sub_self, mul_zero]
  exact (Q2_pos c hc η (mem_Ici.2 (by linarith))).le

theorem hf2 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F2 (P2 η) (Ici 0) η :=
  fun η _ => (F2_deriv η).hasDerivWithinAt

theorem hq2 (β : ℝ) : ∀ η ∈ Ici (0 : ℝ),
    HasDerivWithinAt (Q2 (-β)) (-(F2 η * Q2 (-β) η) - β * (1 - P2 η ^ 2)) (Ici 0) η :=
  fun η _ => ((Q2_deriv (-β) η).congr_deriv (by ring)).hasDerivWithinAt

theorem notWin2 (c a b : ℝ) (hb : b < 1) : ¬ (a < Q2 c 0 ∧ Q2 c 0 < b) := by
  rw [Q2_zero]; intro h; linarith [h.2]

/-- `p' = q` is needed in `fs_neg_tenth_window`. -/
theorem fs_neg_tenth_window_h2 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_window 2 :=
  ⟨F2, P2, Q2 (-(-1 / 10)), hf2, hq2 _, F2_zero, P2_zero, P2_lim, Q2_pos _ (by norm_num),
    P2_decay _ (by norm_num), notWin2 _ _ _ (by norm_num)⟩

/-- `p' = q` is needed in `fs_neg_wall_shear_window`. -/
theorem fs_neg_wall_shear_window_h2 :
    necessity% Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window 2 :=
  ⟨F2, P2, Q2 (-(-1988 / 10000)), hf2, hq2 _, F2_zero, P2_zero, P2_lim, Q2_pos _ (by norm_num),
    P2_decay _ (by norm_num), notWin2 _ _ _ (by norm_num)⟩

/-- `p' = q` is needed in `fs_neg_wall_shear_17_window`. -/
theorem fs_neg_wall_shear_17_window_h2 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_window 2 :=
  ⟨F2, P2, Q2 (-(-17 / 100)), hf2, hq2 _, F2_zero, P2_zero, P2_lim, Q2_pos _ (by norm_num),
    P2_decay _ (by norm_num), notWin2 _ _ _ (by norm_num)⟩

/-- `p' = q` is needed in `fs_neg_wall_shear_18_window`. -/
theorem fs_neg_wall_shear_18_window_h2 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_window 2 :=
  ⟨F2, P2, Q2 (-(-18 / 100)), hf2, hq2 _, F2_zero, P2_zero, P2_lim, Q2_pos _ (by norm_num),
    P2_decay _ (by norm_num), notWin2 _ _ _ (by norm_num)⟩

/-- `p' = q` is needed in `fs_neg_wall_shear_19_window`. -/
theorem fs_neg_wall_shear_19_window_h2 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_window 2 :=
  ⟨F2, P2, Q2 (-(-19 / 100)), hf2, hq2 _, F2_zero, P2_zero, P2_lim, Q2_pos _ (by norm_num),
    P2_decay _ (by norm_num), notWin2 _ _ _ (by norm_num)⟩

/-- `p' = q` is needed in `F13_wall_shear`. -/
theorem F13_wall_shear_h2 : necessity% Checked.Records.F13_wall_shear 2 := by
  refine ⟨F2, P2, Q2 (-(-1988 / 10000)), hf2, hq2 _, F2_zero, P2_zero, P2_lim, Q2_pos _ (by norm_num),
    P2_decay _ (by norm_num), ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioWall; rw [Q2_zero, abs_le]; norm_num

/-! Positivity of the shear dropped: the certified reverse-flow solutions. -/

/-- `0 < q` is needed in `fs_neg_tenth_window`. -/
theorem fs_neg_tenth_window_h7 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, _, a8, w1, w2⟩ :=
    Checked.FalknerSkan.NegReversed.fs_neg_tenth_reversed
  exact ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, fun h => by norm_num at h w2; linarith [h.1]⟩

/-- `0 < q` is needed in `fs_neg_wall_shear_window`. -/
theorem fs_neg_wall_shear_window_h7 :
    necessity% Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, _, a8, w1, w2⟩ :=
    Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_wall_shear_exists
  exact ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, fun h => by norm_num at h w2; linarith [h.1]⟩

/-- `0 < q` is needed in `F13_wall_shear`. -/
theorem F13_wall_shear_h7 : necessity% Checked.Records.F13_wall_shear 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, _, a8, w1, w2⟩ :=
    Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_wall_shear_exists
  refine ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioWall; rw [abs_le]
  intro h; norm_num at h w2; linarith [h.1]

/-! The separation family: the wall shear vanishes, so the equation at the wall gives the shear's slope there as
minus the pressure-gradient coefficient, and a positive shear to the right of the wall makes that coefficient
nonpositive; then the edge condition follows as above. -/

theorem beta_nonpos {β : ℝ} {f p q : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 0) (hpos : ∀ η ∈ Ioi (0 : ℝ), 0 < q η) : β ≤ 0 := by
  have h : HasDerivWithinAt q (-β) (Ioi 0) 0 :=
    ((hq 0 (mem_Ici.2 le_rfl)).congr_deriv (by rw [hf0, hp0, hq0]; ring)).mono Ioi_subset_Ici_self
  rw [hasDerivWithinAt_iff_tendsto_slope] at h
  have e : Ioi (0 : ℝ) \ {0} = Ioi 0 := by
    ext x; simp only [Set.mem_sdiff, mem_Ioi, mem_singleton_iff]; constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, h.ne'⟩
  rw [e] at h
  have : 0 ≤ -β := ge_of_tendsto h (by
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [slope_def_field, hq0, sub_zero, sub_zero]
    exact (div_pos (hpos η hη) hη).le)
  linarith

theorem lim_sep {β : ℝ} {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 0) (hpos : ∀ η ∈ Ioi (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) : Tendsto p atTop (𝓝 1) := by
  refine lim_one β (beta_nonpos hq hf0 hp0 hq0 hpos) f p q hf hp hq (fun η hη => ?_) hdec
  rcases (mem_Ici.1 hη).eq_or_lt with h | h
  · rw [← h, hq0]
  · exact (hpos η h).le

theorem fs_separation_below_printed_r7 :
    dropped% Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed 7 := by
  intro β f p q hf hp hq hf0 hp0 hq0 hpos hdec
  exact Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed hf hp hq hf0 hp0 hq0
    (lim_sep hf hp hq hf0 hp0 hq0 hpos hdec) hpos hdec

theorem F12_separation_r7 : dropped% Checked.Records.F12_separation 7 := by
  intro β f p q hf hp hq hf0 hp0 hq0 hpos hdec
  exact Checked.Records.F12_separation hf hp hq hf0 hp0 hq0 (lim_sep hf hp hq hf0 hp0 hq0 hpos hdec) hpos hdec

theorem fs_separation_equal_r7 : dropped% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 7 := by
  intro β₁ β₂ f₁ p₁ q₁ f₂ p₂ q₂ hf₁ hp₁ hq₁ hf₁0 hp₁0 hq₁0 hpos₁ hdec₁ hf₂ hp₂ hq₂ hf₂0 hp₂0 hq₂0 hl₂ hpos₂ hdec₂
  exact Checked.FalknerSkan.SeparationEqual.fs_separation_equal hf₁ hp₁ hq₁ hf₁0 hp₁0 hq₁0
    (lim_sep hf₁ hp₁ hq₁ hf₁0 hp₁0 hq₁0 hpos₁ hdec₁) hpos₁ hdec₁ hf₂ hp₂ hq₂ hf₂0 hp₂0 hq₂0 hl₂ hpos₂ hdec₂

theorem fs_separation_equal_r16 : dropped% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 16 := by
  intro β₁ β₂ f₁ p₁ q₁ f₂ p₂ q₂ hf₁ hp₁ hq₁ hf₁0 hp₁0 hq₁0 hl₁ hpos₁ hdec₁ hf₂ hp₂ hq₂ hf₂0 hp₂0 hq₂0 hpos₂ hdec₂
  exact Checked.FalknerSkan.SeparationEqual.fs_separation_equal hf₁ hp₁ hq₁ hf₁0 hp₁0 hq₁0 hl₁ hpos₁ hdec₁
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hq₂0 (lim_sep hf₂ hp₂ hq₂ hf₂0 hp₂0 hq₂0 hpos₂ hdec₂) hpos₂ hdec₂

/-- `p' = q` is needed for the first profile in `fs_separation_equal`: the profile of
`fs_separation_below_printed_h2` against the certified separation solution. -/
theorem fs_separation_equal_h2 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 2 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  refine ⟨-(1988376 / 10000000), β, NCP.f2, NCP.p2, NCP.q2, f, p, q,
    fun η _ => (NCP.f2_deriv η).hasDerivWithinAt, fun η _ => (NCP.q2_deriv η).hasDerivWithinAt,
    by simp [NCP.f2], by simp [NCP.p2], by simp [NCP.q2, NCP.G2], NCP.p2_lim, NCP.q2_pos, NCP.p2_decay,
    hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec, ?_⟩
  intro h; rw [← h] at hβ; norm_num at hβ

/-- `p' = q` is needed for the second profile in `fs_separation_equal`. -/
theorem fs_separation_equal_h11 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 11 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  refine ⟨β, -(1988376 / 10000000), f, p, q, NCP.f2, NCP.p2, NCP.q2,
    hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec,
    fun η _ => (NCP.f2_deriv η).hasDerivWithinAt, fun η _ => (NCP.q2_deriv η).hasDerivWithinAt,
    by simp [NCP.f2], by simp [NCP.p2], by simp [NCP.q2, NCP.G2], NCP.p2_lim, NCP.q2_pos, NCP.p2_decay, ?_⟩
  intro h; rw [h] at hβ; norm_num at hβ

/-! The decay pair with a negative pressure-gradient coefficient. -/

theorem fs_neg_decay_max_shear_r7 : dropped% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 7 := by
  intro β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hpos hdec hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂
  exact Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0
    (lim_one β hβ.le f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂

theorem fs_neg_decay_equal_r7 : dropped% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 7 := by
  intro β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hpos hdec hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂ hdec₂
  exact Checked.FalknerSkan.NegDecay.fs_neg_decay_equal β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0
    (lim_one β hβ.le f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂ hdec₂

theorem fs_neg_decay_equal_r15 : dropped% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 15 := by
  intro β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos hdec hf₂ hp₂ hq₂ hf₂0 hp₂0 hpos₂ hdec₂
  exact Checked.FalknerSkan.NegDecay.fs_neg_decay_equal β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos hdec
    hf₂ hp₂ hq₂ hf₂0 hp₂0 (lim_one β hβ.le f₂ p₂ q₂ hf₂ hp₂ hq₂ (fun η hη => (hpos₂ η hη).le) hdec₂) hpos₂ hdec₂

end Checked.Trust.NCS
