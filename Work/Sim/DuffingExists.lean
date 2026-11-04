import Mathlib

/-!
# Existence of the Duffing solution on [0, 6/5] (non-vacuity of `duffing_first_zero`)

Picard–Lindelöf (Mathlib) for the clamped Hamiltonian field
G(x, v) = (cl V v, −(cl X x + (cl X x)³)), cl c y = max (−c) (min c y), X = 11/10, V = 13/10,
which is globally Lipschitz and bounded. Its exact invariant H = Ψ(v) + U(x),
Ψ(v) = ∫₀^v cl V, U(x) = ∫₀^x (cl X + (cl X)³), equals 3/4 along the solution from (1, 0);
Ψ(±V) = V²/2 > 3/4 and U(±X) = X²/2 + X⁴/4 > 3/4 keep the solution where both clamps are
inactive, so it solves x'' + x + x³ = 0.
-/

namespace Work.Sim.DuffingExists
open Set

/-- Clamp of `y` to [−c, c]. -/
noncomputable def cl (c y : ℝ) : ℝ := max (-c) (min c y)

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

/-- Clamped Duffing field. -/
noncomputable def G (p : ℝ × ℝ) : ℝ × ℝ :=
  (cl (13 / 10) p.2, -(cl (11 / 10) p.1 + cl (11 / 10) p.1 ^ 3))

theorem lipG : LipschitzWith 5 G := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  simp only [G, Prod.dist_eq, Real.dist_eq]
  change _ ≤ (5 : ℝ) * _
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  refine max_le (by nlinarith [cl_sub (13 / 10) p.2 q.2, abs_nonneg (p.2 - q.2)]) ?_
  set u := cl (11 / 10) p.1
  set w := cl (11 / 10) q.1
  have hu := abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 11 / 10) p.1)
  have hw := abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 11 / 10) q.1)
  have huw : |u - w| ≤ |p.1 - q.1| := cl_sub _ _ _
  have hfac : -(u + u ^ 3) - -(w + w ^ 3) = -(u - w) * (1 + u ^ 2 + u * w + w ^ 2) := by ring
  have hc0 : 0 ≤ 1 + u ^ 2 + u * w + w ^ 2 := by nlinarith [sq_nonneg (u + w)]
  have hc1 : 1 + u ^ 2 + u * w + w ^ 2 ≤ 5 := by nlinarith [sq_nonneg (u - w)]
  rw [hfac, abs_mul, abs_neg, abs_of_nonneg hc0]
  calc |u - w| * (1 + u ^ 2 + u * w + w ^ 2) ≤ |p.1 - q.1| * 5 :=
        mul_le_mul huw hc1 hc0 (abs_nonneg _)
    _ ≤ 5 * max |p.1 - q.1| |p.2 - q.2| := by nlinarith [abs_nonneg (p.1 - q.1)]

theorem normG (p : ℝ × ℝ) : ‖G p‖ ≤ 5 / 2 := by
  simp only [G, Prod.norm_def, Real.norm_eq_abs]
  have hu := abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 11 / 10) p.1)
  refine max_le ((abs_cl_le (by norm_num) _).trans (by norm_num)) ?_
  rw [abs_neg, abs_le]
  constructor <;> nlinarith [sq_nonneg (cl (11 / 10) p.1)]

theorem fst_deriv {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {t : ℝ} (h : HasDerivAt α d t) :
    HasDerivAt (fun s => (α s).1) d.1 t := by
  have := h.hasFDerivAt.fst.hasDerivAt
  simpa using this

theorem snd_deriv {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {t : ℝ} (h : HasDerivAt α d t) :
    HasDerivAt (fun s => (α s).2) d.2 t := by
  have := h.hasFDerivAt.snd.hasDerivAt
  simpa using this

/-- Kinetic part of the clamped Hamiltonian. -/
noncomputable def Ψ (v : ℝ) : ℝ := ∫ s in (0 : ℝ)..v, cl (13 / 10) s

/-- Potential part of the clamped Hamiltonian. -/
noncomputable def U (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, (cl (11 / 10) s + cl (11 / 10) s ^ 3)

theorem contU : Continuous fun s => cl (11 / 10) s + cl (11 / 10) s ^ 3 :=
  (continuous_cl _).add ((continuous_cl _).pow 3)

theorem hasDerivAt_Ψ (v : ℝ) : HasDerivAt Ψ (cl (13 / 10) v) v :=
  ((continuous_cl _).integral_hasStrictDerivAt 0 v).hasDerivAt

theorem hasDerivAt_U (x : ℝ) : HasDerivAt U (cl (11 / 10) x + cl (11 / 10) x ^ 3) x :=
  (contU.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- A function with derivative `g` whose sign is that of the variable is antitone on
(−∞, 0] and monotone on [0, ∞). -/
theorem mono_parts {F g : ℝ → ℝ} (hF : ∀ y, HasDerivAt F (g y) y) (hpos : ∀ y, 0 ≤ y → 0 ≤ g y)
    (hneg : ∀ y, y ≤ 0 → g y ≤ 0) : MonotoneOn F (Ici 0) ∧ AntitoneOn F (Iic 0) := by
  have hc : Continuous F := continuous_iff_continuousAt.2 fun y => (hF y).continuousAt
  refine ⟨monotoneOn_of_deriv_nonneg (convex_Ici 0) hc.continuousOn
      (fun y _ => (hF y).differentiableAt.differentiableWithinAt) fun y hy => ?_,
    antitoneOn_of_deriv_nonpos (convex_Iic 0) hc.continuousOn
      (fun y _ => (hF y).differentiableAt.differentiableWithinAt) fun y hy => ?_⟩
  · rw [interior_Ici] at hy; rw [(hF y).deriv]; exact hpos y (le_of_lt hy)
  · rw [interior_Iic] at hy; rw [(hF y).deriv]; exact hneg y (le_of_lt hy)

theorem Ψ_parts : MonotoneOn Ψ (Ici 0) ∧ AntitoneOn Ψ (Iic 0) :=
  mono_parts hasDerivAt_Ψ (fun y hy => cl_nonneg (by norm_num) hy)
    (fun y hy => cl_nonpos (by norm_num) hy)

theorem U_parts : MonotoneOn U (Ici 0) ∧ AntitoneOn U (Iic 0) :=
  mono_parts hasDerivAt_U
    (fun y hy => by have := cl_nonneg (c := 11 / 10) (by norm_num) hy; positivity)
    (fun y hy => by
      have h := cl_nonpos (c := 11 / 10) (by norm_num) hy
      nlinarith [pow_two_nonneg (cl (11 / 10) y), sq_nonneg (cl (11 / 10) y)])

theorem Ψ_zero : Ψ 0 = 0 := by simp [Ψ]
theorem U_zero : U 0 = 0 := by simp [U]

theorem Ψ_val {b : ℝ} (hb : |b| ≤ 13 / 10) : Ψ b = b ^ 2 / 2 := by
  unfold Ψ
  rw [intervalIntegral.integral_congr (g := fun s => s) (fun s hs => cl_of_abs_le ?_),
    integral_id]
  · ring
  · rw [Set.uIcc, Set.mem_Icc] at hs
    rw [abs_le] at hb ⊢
    constructor
    · have := hs.1; simp only [inf_le_iff] at this ⊢; rcases le_total 0 b with h | h <;>
        simp_all <;> linarith
    · have := hs.2; rcases le_total 0 b with h | h <;> simp_all <;> linarith

theorem U_val {b : ℝ} (hb : |b| ≤ 11 / 10) : U b = b ^ 2 / 2 + b ^ 4 / 4 := by
  unfold U
  rw [intervalIntegral.integral_congr (g := fun s => s + s ^ 3) (fun s hs => by
      simp only
      rw [cl_of_abs_le ?_]
      rw [Set.uIcc, Set.mem_Icc] at hs
      rw [abs_le] at hb ⊢
      constructor
      · have := hs.1; rcases le_total 0 b with h | h <;> simp_all <;> linarith
      · have := hs.2; rcases le_total 0 b with h | h <;> simp_all <;> linarith),
    intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
      ((continuous_pow 3).intervalIntegrable _ _), integral_id, integral_pow]
  ring

theorem Ψ_nonneg (v : ℝ) : 0 ≤ Ψ v := by
  rcases le_total 0 v with h | h
  · rw [← Ψ_zero]; exact Ψ_parts.1 (le_refl (0 : ℝ)) h h
  · rw [← Ψ_zero]; exact Ψ_parts.2 h (le_refl (0 : ℝ)) h

theorem U_nonneg (x : ℝ) : 0 ≤ U x := by
  rcases le_total 0 x with h | h
  · rw [← U_zero]; exact U_parts.1 (le_refl (0 : ℝ)) h h
  · rw [← U_zero]; exact U_parts.2 h (le_refl (0 : ℝ)) h

theorem abs_lt_of_Ψ {v : ℝ} (h : Ψ v ≤ 3 / 4) : |v| < 13 / 10 := by
  by_contra hc
  push Not at hc
  rcases le_total 0 v with h0 | h0
  · have hv : 13 / 10 ≤ v := by rw [abs_of_nonneg h0] at hc; exact hc
    have := Ψ_parts.1 (show (0 : ℝ) ≤ 13 / 10 by norm_num) h0 hv
    rw [Ψ_val (by norm_num)] at this; linarith
  · have hv : v ≤ -(13 / 10) := by rw [abs_of_nonpos h0] at hc; linarith
    have := Ψ_parts.2 h0 (show -(13 / 10 : ℝ) ≤ 0 by norm_num) hv
    rw [Ψ_val (by norm_num)] at this; linarith

theorem abs_lt_of_U {x : ℝ} (h : U x ≤ 3 / 4) : |x| < 11 / 10 := by
  by_contra hc
  push Not at hc
  rcases le_total 0 x with h0 | h0
  · have hx : 11 / 10 ≤ x := by rw [abs_of_nonneg h0] at hc; exact hc
    have := U_parts.1 (show (0 : ℝ) ≤ 11 / 10 by norm_num) h0 hx
    rw [U_val (by norm_num)] at this; linarith
  · have hx : x ≤ -(11 / 10) := by rw [abs_of_nonpos h0] at hc; linarith
    have := U_parts.2 h0 (show -(11 / 10 : ℝ) ≤ 0 by norm_num) hx
    rw [U_val (by norm_num)] at this; linarith

/-- The solution of the clamped field from (1, 0), defined on [−1/10, 13/10]. -/
theorem exists_G_solution : ∃ α : ℝ → ℝ × ℝ, α 0 = (1, 0) ∧
    ∀ t ∈ Icc (-1 / 10 : ℝ) (13 / 10), HasDerivWithinAt α (G (α t)) (Icc (-1 / 10) (13 / 10)) t := by
  have hPL : IsPicardLindelof (fun _ => G) (tmin := -1 / 10) (tmax := 13 / 10)
      ⟨0, by norm_num, by norm_num⟩ ((1 : ℝ), (0 : ℝ)) 4 0 (5 / 2) 5 :=
    { lipschitzOnWith := fun _ _ => lipG.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ p _ => by
        have := normG p; exact_mod_cast this
      mul_max_le := by
        simp only [NNReal.coe_ofNat, NNReal.coe_zero, sub_zero]
        norm_num }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hα⟩

/-- Existence: a solution of x'' + x + x³ = 0, x(0) = 1, x'(0) = 0 on [0, 6/5], with
two-sided derivatives at every time of [0, 6/5]. -/
theorem exists_solution : ∃ x v : ℝ → ℝ, x 0 = 1 ∧ v 0 = 0 ∧
    ∀ t ∈ Icc (0 : ℝ) (6 / 5), HasDerivAt x (v t) t ∧ HasDerivAt v (-1 * x t - 1 * x t ^ 3) t := by
  obtain ⟨α, h0, hα⟩ := exists_G_solution
  have hD : ∀ t ∈ Icc (0 : ℝ) (6 / 5), HasDerivAt α (G (α t)) t := fun t ht =>
    (hα t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
  set H : ℝ → ℝ := fun t => Ψ (α t).2 + U (α t).1 with hH
  have hHd : ∀ t ∈ Icc (0 : ℝ) (6 / 5), HasDerivAt H 0 t := by
    intro t ht
    have h1 := (hasDerivAt_Ψ _).comp t (snd_deriv (hD t ht))
    have h2 := (hasDerivAt_U _).comp t (fst_deriv (hD t ht))
    convert h1.add h2 using 1
    · funext s; simp [hH]
    · simp only [G]; ring
  have hc : ∀ t ∈ Icc (0 : ℝ) (6 / 5), H t = H 0 :=
    constant_of_has_deriv_right_zero
      (fun t ht => (hHd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hHd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
  have hH0 : H 0 = 3 / 4 := by
    simp only [hH, h0, Ψ_zero]
    rw [U_val (by norm_num)]; norm_num
  have hin : ∀ t ∈ Icc (0 : ℝ) (6 / 5), |(α t).2| < 13 / 10 ∧ |(α t).1| < 11 / 10 := by
    intro t ht
    have h := hc t ht
    rw [hH0] at h
    simp only [hH] at h
    exact ⟨abs_lt_of_Ψ (by linarith [U_nonneg (α t).1]),
      abs_lt_of_U (by linarith [Ψ_nonneg (α t).2])⟩
  refine ⟨fun t => (α t).1, fun t => (α t).2, by simp [h0], by simp [h0], fun t ht => ⟨?_, ?_⟩⟩
  · have := fst_deriv (hD t ht)
    simp only [G] at this
    rwa [cl_of_abs_le (hin t ht).1.le] at this
  · have := snd_deriv (hD t ht)
    simp only [G] at this
    rw [cl_of_abs_le (hin t ht).2.le] at this
    convert this using 1; ring

end Work.Sim.DuffingExists
