import Mathlib

/-!
# Townes existence: the clamped continuation from r = 1/5

Field `F t (θ, φ) = (cl 5 φ, −cl 5 φ / max t (1/5) + (cl 3 θ − (cl 3 θ)³))`: globally bounded
(54) and Lipschitz (31), continuous in t. Picard–Lindelöf (Mathlib) gives a flow on [1/5, T],
Lipschitz in the initial state. The clamped energy V = Ψ(φ) + W(θ), Ψ v = ∫₀^v cl 5,
W y = ∫₀^y ((cl 3)³ − cl 3), is non-increasing (dV/dt = −(cl 5 φ)²/max t (1/5)); from a start
with |θ| ≤ 5/2, |φ| ≤ 3 it stays below 11.15 < min(W(±3), Ψ(±5) − 1/4), so both clamps stay
inactive and the solution solves θ' = φ, φ' = −φ/t + θ − θ³.
-/

namespace Work.Townes.TExFlow
open Set

/-- Clamp of `y` to `[−c, c]`. -/
noncomputable def cl (c y : ℝ) : ℝ := max (-c) (min c y)

/-- The clamped Townes field (time clamped below by 1/5). -/
noncomputable def F (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cl 5 p.2, -(cl 5 p.2 / max t (1 / 5)) + (cl 3 p.1 - cl 3 p.1 ^ 3))

theorem cl_of_abs_le {c y : ℝ} (h : |y| ≤ c) : cl c y = y := by
  unfold cl; rw [abs_le] at h; rw [min_eq_right h.2, max_eq_right h.1]

theorem abs_cl_le {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : |cl c y| ≤ c := by
  unfold cl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem continuous_cl (c : ℝ) : Continuous (cl c) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem cl_sub (c y z : ℝ) : |cl c y - cl c z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem cl_nonneg {c y : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) : 0 ≤ cl c y := by
  unfold cl; exact le_max_of_le_right (le_min hc hy)

theorem cl_nonpos {c y : ℝ} (hc : 0 ≤ c) (hy : y ≤ 0) : cl c y ≤ 0 := by
  unfold cl; exact max_le (by linarith) ((min_le_right _ _).trans hy)

theorem one_le_cl {y : ℝ} (hy : 1 ≤ y) : 1 ≤ cl 3 y := by
  unfold cl; exact le_max_of_le_right (le_min (by norm_num) hy)

theorem cl_le_neg_one {y : ℝ} (hy : y ≤ -1) : cl 3 y ≤ -1 := by
  unfold cl; exact max_le (by norm_num) ((min_le_right _ _).trans hy)

theorem cubic_diff (u w : ℝ) (hu : |u| ≤ 3) (hw : |w| ≤ 3) :
    |(u - u ^ 3) - (w - w ^ 3)| ≤ 26 * |u - w| := by
  have hu' := abs_le.1 hu
  have hw' := abs_le.1 hw
  have hfac : (u - u ^ 3) - (w - w ^ 3) = (u - w) * (1 - (u ^ 2 + u * w + w ^ 2)) := by ring
  have hc0 : 0 ≤ u ^ 2 + u * w + w ^ 2 := by nlinarith [sq_nonneg (u + w)]
  have hc1 : u ^ 2 + u * w + w ^ 2 ≤ 27 := by nlinarith [sq_nonneg (u - w)]
  have hb : |1 - (u ^ 2 + u * w + w ^ 2)| ≤ 26 := by rw [abs_le]; constructor <;> linarith
  rw [hfac, abs_mul]
  nlinarith [abs_nonneg (u - w), abs_nonneg (1 - (u ^ 2 + u * w + w ^ 2))]

theorem abs_cubic_le (u : ℝ) (hu : |u| ≤ 3) : |u - u ^ 3| ≤ 24 := by
  have hu' := abs_le.1 hu
  rw [abs_le]; constructor
  · have h1 : 0 ≤ (3 - u) * (u ^ 2 + 3 * u + 8) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (u + 3 / 2)])
    nlinarith
  · have h1 : 0 ≤ (u + 3) * (u ^ 2 - 3 * u + 8) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (u - 3 / 2)])
    nlinarith

theorem max_pos' (t : ℝ) : (1 / 5 : ℝ) ≤ max t (1 / 5) := le_max_right _ _

theorem abs_div_max_le (t v : ℝ) : |cl 5 v / max t (1 / 5)| ≤ 25 := by
  have hm : (0 : ℝ) < max t (1 / 5) := lt_of_lt_of_le (by norm_num) (max_pos' t)
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  have := abs_cl_le (by norm_num : (0 : ℝ) ≤ 5) v
  nlinarith [max_pos' t]

theorem lipF (t : ℝ) : LipschitzWith 31 (F t) := by
  have hm : (0 : ℝ) < max t (1 / 5) := lt_of_lt_of_le (by norm_num) (max_pos' t)
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  simp only [F, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (31 : ℝ) * _
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hv : |cl 5 p.2 - cl 5 q.2| ≤ |p.2 - q.2| := cl_sub _ _ _
  refine max_le (by nlinarith [abs_nonneg (p.2 - q.2)]) ?_
  have hu := abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) p.1
  have hw := abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) q.1
  have hc := cubic_diff _ _ hu hw
  have huw : |cl 3 p.1 - cl 3 q.1| ≤ |p.1 - q.1| := cl_sub _ _ _
  have hre : -(cl 5 p.2 / max t (1 / 5)) + (cl 3 p.1 - cl 3 p.1 ^ 3) -
      (-(cl 5 q.2 / max t (1 / 5)) + (cl 3 q.1 - cl 3 q.1 ^ 3)) =
      -((cl 5 p.2 - cl 5 q.2) / max t (1 / 5)) +
        ((cl 3 p.1 - cl 3 p.1 ^ 3) - (cl 3 q.1 - cl 3 q.1 ^ 3)) := by ring
  rw [hre]
  have h1 : |(cl 5 p.2 - cl 5 q.2) / max t (1 / 5)| ≤ 5 * |p.2 - q.2| := by
    rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
    nlinarith [max_pos' t, abs_nonneg (cl 5 p.2 - cl 5 q.2), abs_nonneg (p.2 - q.2)]
  calc |-((cl 5 p.2 - cl 5 q.2) / max t (1 / 5)) +
        ((cl 3 p.1 - cl 3 p.1 ^ 3) - (cl 3 q.1 - cl 3 q.1 ^ 3))|
      ≤ |(cl 5 p.2 - cl 5 q.2) / max t (1 / 5)| +
          |(cl 3 p.1 - cl 3 p.1 ^ 3) - (cl 3 q.1 - cl 3 q.1 ^ 3)| := by
        have := abs_add_le (-((cl 5 p.2 - cl 5 q.2) / max t (1 / 5)))
          ((cl 3 p.1 - cl 3 p.1 ^ 3) - (cl 3 q.1 - cl 3 q.1 ^ 3))
        rwa [abs_neg] at this
    _ ≤ 5 * |p.2 - q.2| + 26 * |p.1 - q.1| := by nlinarith
    _ ≤ 31 * max |p.1 - q.1| |p.2 - q.2| := by nlinarith [abs_nonneg (p.1 - q.1)]

theorem normF (t : ℝ) (p : ℝ × ℝ) : ‖F t p‖ ≤ 54 := by
  simp only [F, Prod.norm_def, Real.norm_eq_abs]
  refine max_le ((abs_cl_le (by norm_num) _).trans (by norm_num)) ?_
  have h1 := abs_div_max_le t p.2
  have h2 := abs_cubic_le _ (abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) p.1)
  calc |-(cl 5 p.2 / max t (1 / 5)) + (cl 3 p.1 - cl 3 p.1 ^ 3)|
      ≤ |cl 5 p.2 / max t (1 / 5)| + |cl 3 p.1 - cl 3 p.1 ^ 3| := by
        have := abs_add_le (-(cl 5 p.2 / max t (1 / 5))) (cl 3 p.1 - cl 3 p.1 ^ 3)
        rwa [abs_neg] at this
    _ ≤ 54 := by linarith

theorem contF (x : ℝ × ℝ) : Continuous (fun t => F t x) := by
  unfold F
  refine continuous_const.prodMk ?_
  refine Continuous.add (Continuous.neg ?_) continuous_const
  exact continuous_const.div (continuous_id.max continuous_const)
    (fun t => ne_of_gt (lt_of_lt_of_le (by norm_num) (max_pos' t)))

theorem exists_flow (T : ℝ) (hT : 1 / 5 < T) : ∃ α : ℝ × ℝ → ℝ → ℝ × ℝ,
    (∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) 3, α p (1 / 5) = p ∧
      ∀ t ∈ Icc (1 / 5 : ℝ) T, HasDerivWithinAt (α p) (F t (α p t)) (Icc (1 / 5) T) t) ∧
    ∃ L : ℝ, ∀ t ∈ Icc (1 / 5 : ℝ) T, ∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) 3,
      ∀ q ∈ Metric.closedBall (0 : ℝ × ℝ) 3, dist (α p t) (α q t) ≤ L * dist p q := by
  have hA : (0 : ℝ) ≤ 3 + 54 * (T - 1 / 5) := by nlinarith
  have hPL : IsPicardLindelof F (tmin := 1 / 5) (tmax := T)
      ⟨1 / 5, le_rfl, hT.le⟩ (0 : ℝ × ℝ) (Real.toNNReal (3 + 54 * (T - 1 / 5))) 3 54 31 :=
    { lipschitzOnWith := fun t _ => (lipF t).lipschitzOnWith
      continuousOn := fun x _ => (contF x).continuousOn
      norm_le := fun t _ p _ => by
        have := normF t p; exact_mod_cast this
      mul_max_le := by
        rw [Real.coe_toNNReal _ hA]
        simp only [NNReal.coe_ofNat, sub_self]
        rw [max_eq_left (by linarith)]
        linarith }
  obtain ⟨α, hα, L', hlip⟩ := hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨α, fun p hp => hα p (by simpa using hp), L', fun t ht p hp q hq => ?_⟩
  exact (hlip t ht).dist_le_mul p (by simpa using hp) q (by simpa using hq)

theorem consistent {T T' : ℝ} (hTT' : T ≤ T') (f g : ℝ → ℝ × ℝ) (h0 : f (1 / 5) = g (1 / 5))
    (hf : ∀ t ∈ Icc (1 / 5 : ℝ) T, HasDerivWithinAt f (F t (f t)) (Icc (1 / 5) T) t)
    (hg : ∀ t ∈ Icc (1 / 5 : ℝ) T', HasDerivWithinAt g (F t (g t)) (Icc (1 / 5) T') t) :
    EqOn f g (Icc (1 / 5) T) := by
  refine ODE_solution_unique_of_mem_Icc_right (v := F) (s := fun _ => univ)
    (K := 31)
    (fun t _ => (lipF t).lipschitzOnWith)
    (fun t ht => (hf t ht).continuousWithinAt) (fun t ht => ?_) (fun _ _ => mem_univ _)
    (fun t ht => ((hg t ⟨ht.1, ht.2.trans hTT'⟩).continuousWithinAt.mono
      (Icc_subset_Icc_right hTT'))) (fun t ht => ?_) (fun _ _ => mem_univ _) h0
  · have hmem : t ∈ Icc (1 / 5) T := ⟨ht.1, ht.2.le⟩
    refine (hf t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  · have hmem : t ∈ Icc (1 / 5) T' := ⟨ht.1, ht.2.le.trans hTT'⟩
    refine (hg t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE (lt_of_lt_of_le ht.2 hTT'))
      (Icc_subset_Icc_left ht.1)

theorem equilibrium_backward {T t₀ : ℝ} (e : ℝ × ℝ) (he : ∀ t, F t e = 0)
    (ht₀ : t₀ ∈ Icc (1 / 5 : ℝ) T) (f : ℝ → ℝ × ℝ)
    (hf : ∀ t ∈ Icc (1 / 5 : ℝ) T, HasDerivWithinAt f (F t (f t)) (Icc (1 / 5) T) t)
    (h0 : f t₀ = e) : f (1 / 5) = e := by
  have h := ODE_solution_unique_of_mem_Icc_left (v := F) (s := fun _ => univ)
    (K := 31) (a := 1 / 5) (b := t₀) (f := f) (g := fun _ => e)
    (fun t _ => (lipF t).lipschitzOnWith)
    (fun t ht => (hf t ⟨ht.1, ht.2.trans ht₀.2⟩).continuousWithinAt.mono
      (Icc_subset_Icc_right ht₀.2))
    (fun t ht => ?_) (fun _ _ => mem_univ _) continuousOn_const
    (fun t _ => by rw [he]; exact hasDerivWithinAt_const _ _ _) (fun _ _ => mem_univ _) h0
  · exact h ⟨le_rfl, ht₀.1⟩
  · have hmem : t ∈ Icc (1 / 5) T := ⟨ht.1.le, ht.2.trans ht₀.2⟩
    refine (hf t hmem).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right hmem.2)

theorem F_zero (t : ℝ) : F t 0 = 0 := by
  have h3 : cl 3 0 = 0 := cl_of_abs_le (by norm_num)
  have h5 : cl 5 0 = 0 := cl_of_abs_le (by norm_num)
  simp only [F, Prod.fst_zero, Prod.snd_zero, h3, h5]
  ext <;> simp

theorem F_one (t : ℝ) : F t (1, 0) = 0 := by
  have h3 : cl 3 1 = 1 := cl_of_abs_le (by norm_num)
  have h5 : cl 5 0 = 0 := cl_of_abs_le (by norm_num)
  simp only [F, h3, h5]
  ext <;> simp

theorem F_eq {t : ℝ} (ht : 1 / 5 ≤ t) {p : ℝ × ℝ} (h1 : |p.1| < 3) (h2 : |p.2| < 5) :
    F t p = (p.2, -(1 / t * p.2) + p.1 - p.1 ^ 3) := by
  simp only [F, max_eq_left ht, cl_of_abs_le h1.le, cl_of_abs_le h2.le]
  ext
  · rfl
  · simp only; ring

/-! ## The clamped energy -/

theorem fst_derivW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α d s t) : HasDerivWithinAt (fun r => (α r).1) d.1 s t := by
  have := h.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa using this

theorem snd_derivW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α d s t) : HasDerivWithinAt (fun r => (α r).2) d.2 s t := by
  have := h.hasFDerivWithinAt.snd.hasDerivWithinAt
  simpa using this

/-- Kinetic part of the clamped energy. -/
noncomputable def Ψ (v : ℝ) : ℝ := ∫ s in (0 : ℝ)..v, cl 5 s

/-- Potential part of the clamped energy. -/
noncomputable def W (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, (cl 3 s ^ 3 - cl 3 s)

theorem contW : Continuous fun s => cl 3 s ^ 3 - cl 3 s :=
  ((continuous_cl _).pow 3).sub (continuous_cl _)

theorem hasDerivAt_Ψ (v : ℝ) : HasDerivAt Ψ (cl 5 v) v :=
  ((continuous_cl _).integral_hasStrictDerivAt 0 v).hasDerivAt

theorem hasDerivAt_W (x : ℝ) : HasDerivAt W (cl 3 x ^ 3 - cl 3 x) x :=
  (contW.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem mono_parts {G g : ℝ → ℝ} (hG : ∀ y, HasDerivAt G (g y) y) (hpos : ∀ y, 0 ≤ y → 0 ≤ g y)
    (hneg : ∀ y, y ≤ 0 → g y ≤ 0) : MonotoneOn G (Ici 0) ∧ AntitoneOn G (Iic 0) := by
  have hc : Continuous G := continuous_iff_continuousAt.2 fun y => (hG y).continuousAt
  refine ⟨monotoneOn_of_deriv_nonneg (convex_Ici 0) hc.continuousOn
      (fun y _ => (hG y).differentiableAt.differentiableWithinAt) fun y hy => ?_,
    antitoneOn_of_deriv_nonpos (convex_Iic 0) hc.continuousOn
      (fun y _ => (hG y).differentiableAt.differentiableWithinAt) fun y hy => ?_⟩
  · rw [interior_Ici] at hy; rw [(hG y).deriv]; exact hpos y (le_of_lt hy)
  · rw [interior_Iic] at hy; rw [(hG y).deriv]; exact hneg y (le_of_lt hy)

theorem Ψ_parts : MonotoneOn Ψ (Ici 0) ∧ AntitoneOn Ψ (Iic 0) :=
  mono_parts hasDerivAt_Ψ (fun y hy => cl_nonneg (by norm_num) hy)
    (fun y hy => cl_nonpos (by norm_num) hy)

theorem W_mono : MonotoneOn W (Ici 1) := by
  have hc : Continuous W := continuous_iff_continuousAt.2 fun y => (hasDerivAt_W y).continuousAt
  refine monotoneOn_of_deriv_nonneg (convex_Ici 1) hc.continuousOn
    (fun y _ => (hasDerivAt_W y).differentiableAt.differentiableWithinAt) fun y hy => ?_
  rw [interior_Ici] at hy
  rw [(hasDerivAt_W y).deriv]
  have h := one_le_cl (le_of_lt hy)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ cl 3 y) (by nlinarith : (0 : ℝ) ≤ cl 3 y ^ 2 - 1)]

theorem W_anti : AntitoneOn W (Iic (-1)) := by
  have hc : Continuous W := continuous_iff_continuousAt.2 fun y => (hasDerivAt_W y).continuousAt
  refine antitoneOn_of_deriv_nonpos (convex_Iic (-1)) hc.continuousOn
    (fun y _ => (hasDerivAt_W y).differentiableAt.differentiableWithinAt) fun y hy => ?_
  rw [interior_Iic] at hy
  rw [(hasDerivAt_W y).deriv]
  have h := cl_le_neg_one (le_of_lt hy)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -cl 3 y) (by nlinarith : (0 : ℝ) ≤ cl 3 y ^ 2 - 1)]

theorem Ψ_zero : Ψ 0 = 0 := by simp [Ψ]

theorem mem_of_uIcc {b c s : ℝ} (hb : |b| ≤ c) (hs : s ∈ uIcc 0 b) : |s| ≤ c := by
  rw [Set.uIcc, Set.mem_Icc] at hs
  rw [abs_le] at hb ⊢
  constructor
  · have := hs.1; rcases le_total 0 b with h | h <;> simp_all <;> linarith
  · have := hs.2; rcases le_total 0 b with h | h <;> simp_all <;> linarith

theorem Ψ_val {b : ℝ} (hb : |b| ≤ 5) : Ψ b = b ^ 2 / 2 := by
  unfold Ψ
  rw [intervalIntegral.integral_congr (g := fun s => s)
    (fun s hs => cl_of_abs_le (mem_of_uIcc hb hs)), integral_id]
  ring

theorem W_val {b : ℝ} (hb : |b| ≤ 3) : W b = b ^ 4 / 4 - b ^ 2 / 2 := by
  unfold W
  rw [intervalIntegral.integral_congr (g := fun s => s ^ 3 - s) (fun s hs => by
      simp only
      rw [cl_of_abs_le (mem_of_uIcc hb hs)])]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x ^ 3) (g := fun x : ℝ => x)
    ((continuous_pow 3).intervalIntegrable 0 b) (continuous_id.intervalIntegrable 0 b)]
  simp only [integral_pow, integral_id]
  ring

theorem Ψ_nonneg (v : ℝ) : 0 ≤ Ψ v := by
  rcases le_total 0 v with h | h
  · rw [← Ψ_zero]; exact Ψ_parts.1 (le_refl (0 : ℝ)) h h
  · rw [← Ψ_zero]; exact Ψ_parts.2 h (le_refl (0 : ℝ)) h

theorem W_ge_of_three {x : ℝ} (hx : 3 ≤ |x|) : 63 / 4 ≤ W x := by
  rcases le_total 0 x with h0 | h0
  · have hx' : 3 ≤ x := by rwa [abs_of_nonneg h0] at hx
    have := W_mono (show (1 : ℝ) ≤ 3 by norm_num) (show (1 : ℝ) ≤ x by linarith) hx'
    rw [W_val (by norm_num)] at this; linarith
  · have hx' : x ≤ -3 := by rw [abs_of_nonpos h0] at hx; linarith
    have := W_anti (show x ≤ -1 by linarith) (show (-3 : ℝ) ≤ -1 by norm_num) hx'
    rw [W_val (by norm_num)] at this; linarith

theorem W_ge (x : ℝ) : -(1 / 4) ≤ W x := by
  rcases le_total |x| 3 with h | h
  · rw [W_val h]; nlinarith [sq_nonneg (x ^ 2 - 1)]
  · linarith [W_ge_of_three h]

theorem Ψ_ge_of_five {v : ℝ} (hv : 5 ≤ |v|) : 25 / 2 ≤ Ψ v := by
  rcases le_total 0 v with h0 | h0
  · have hv' : 5 ≤ v := by rwa [abs_of_nonneg h0] at hv
    have := Ψ_parts.1 (show (0 : ℝ) ≤ 5 by norm_num) h0 hv'
    rw [Ψ_val (by norm_num)] at this; linarith
  · have hv' : v ≤ -5 := by rw [abs_of_nonpos h0] at hv; linarith
    have := Ψ_parts.2 h0 (show (-5 : ℝ) ≤ 0 by norm_num) hv'
    rw [Ψ_val (by norm_num)] at this; linarith

theorem start_energy {θ₀ φ₀ : ℝ} (hθ : |θ₀| ≤ 5 / 2) (hφ : |φ₀| ≤ 3) :
    Ψ φ₀ + W θ₀ ≤ 1115 / 100 := by
  rw [Ψ_val (hφ.trans (by norm_num)), W_val (hθ.trans (by norm_num))]
  have h1 : θ₀ ^ 2 ≤ (5 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  have h2 : φ₀ ^ 2 ≤ 3 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hφ 2
  have h3 : 0 ≤ θ₀ ^ 2 := sq_nonneg _
  have h4 : (θ₀ ^ 2 - 25 / 4) * (θ₀ ^ 2 + 17 / 4) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num at h1 ⊢; linarith) (by positivity)
  nlinarith

theorem bounds {T : ℝ} (f : ℝ → ℝ × ℝ)
    (hf : ∀ t ∈ Icc (1 / 5 : ℝ) T, HasDerivWithinAt f (F t (f t)) (Icc (1 / 5) T) t)
    (h1 : |(f (1 / 5)).1| ≤ 5 / 2) (h2 : |(f (1 / 5)).2| ≤ 3) :
    ∀ t ∈ Icc (1 / 5 : ℝ) T, |(f t).1| < 3 ∧ |(f t).2| < 5 := by
  set H : ℝ → ℝ := fun t => Ψ (f t).2 + W (f t).1 with hH
  have hcont : ContinuousOn H (Icc (1 / 5) T) := by
    intro t ht
    have hc := (hf t ht).continuousWithinAt
    have h1 : ContinuousWithinAt (fun r => (f r).2) (Icc (1 / 5) T) t :=
      continuous_snd.continuousAt.comp_continuousWithinAt hc
    have h2 : ContinuousWithinAt (fun r => (f r).1) (Icc (1 / 5) T) t :=
      continuous_fst.continuousAt.comp_continuousWithinAt hc
    exact ((hasDerivAt_Ψ _).continuousAt.comp_continuousWithinAt h1).add
      ((hasDerivAt_W _).continuousAt.comp_continuousWithinAt h2)
  have hD : ∀ t ∈ interior (Icc (1 / 5 : ℝ) T),
      HasDerivWithinAt H (-(cl 5 (f t).2 ^ 2 / max t (1 / 5))) (interior (Icc (1 / 5) T)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have hd : HasDerivAt f (F t (f t)) t :=
      (hf t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hdu := hd.hasDerivWithinAt (s := univ)
    have hh1 := (hasDerivAt_Ψ _).comp t (hasDerivWithinAt_univ.1 (snd_derivW hdu))
    have hh2 := (hasDerivAt_W _).comp t (hasDerivWithinAt_univ.1 (fst_derivW hdu))
    have := hh1.add hh2
    refine HasDerivAt.hasDerivWithinAt ?_
    convert this using 1
    · rfl
    simp only [F]
    have hm : (0 : ℝ) < max t (1 / 5) := lt_of_lt_of_le (by norm_num) (max_pos' t)
    field_simp
    ring
  have hanti : AntitoneOn H (Icc (1 / 5) T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcont hD (fun t _ => ?_)
    have hm : (0 : ℝ) < max t (1 / 5) := lt_of_lt_of_le (by norm_num) (max_pos' t)
    have : 0 ≤ cl 5 (f t).2 ^ 2 / max t (1 / 5) := div_nonneg (sq_nonneg _) hm.le
    linarith
  intro t ht
  have hT : (1 / 5 : ℝ) ∈ Icc (1 / 5) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have h := hanti hT ht ht.1
  have hH0 := start_energy h1 h2
  simp only [hH] at h
  constructor
  · by_contra hc; push Not at hc
    have := W_ge_of_three hc
    linarith [Ψ_nonneg (f t).2]
  · by_contra hc; push Not at hc
    have := Ψ_ge_of_five hc
    linarith [W_ge (f t).1]

end Work.Townes.TExFlow
