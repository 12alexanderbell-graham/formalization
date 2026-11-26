import Checked.Townes.TExFlow
import Mathlib.Analysis.ODE.Gronwall
/-!
# H₂⁺ route step 2, second piece: the clamped radial flow with the parameters in the state (run 2026-11-26T2228Z)

Route of `runs/2026-11-26T1628Z/README.md`, step 2. Past ξ = 2 the radial equation ((ξ² − 1)L′)′ + (4ξ − kξ² + A)L = 0
is the first-order system L′ = P/(ξ² − 1), P′ = −(4ξ − kξ² + A) L (P = (ξ² − 1)L′). To get continuity in the
parameter for free from Picard–Lindelöf (Lipschitz dependence on the initial point), k and A are state components
with zero derivative: the state is x = (L, P, k, A). Clamps (`Checked.Townes.TExFlow.cl`) make the field globally
Lipschitz and bounded on [2, T] (`G`, `lipG`, `normG`); `exists_flow` is Mathlib's Picard–Lindelöf.

The clamps are inactive (`flow_solves`): k and A stay constant (`flow_param_const`), and by Gronwall
max(|L|, |P|) ≤ δ e^{NB (ξ − 2)} with NB = 4T + 3T² + 3 (`flow_bound`), so with B ≥ δ e^{NB (T − 2)} and
k, A ∈ [0, 3] the flow solves the unclamped system on [2, T]. No numerics.
-/

namespace Work.Quantum.RadialFlow
open Set Filter Topology NNReal
open Checked.Townes.TExFlow (cl cl_of_abs_le abs_cl_le continuous_cl cl_sub)

/-- The state (L, P, k, A). -/
abbrev E := ℝ × ℝ × ℝ × ℝ

/-- The clamped field (L and P clamped at B, k and A at 3). -/
noncomputable def G (B t : ℝ) (x : E) : E :=
  (cl B x.2.1 / (t ^ 2 - 1), -((4 * t - cl 3 x.2.2.1 * t ^ 2 + cl 3 x.2.2.2) * cl B x.1), 0, 0)

/-- The bound of |4t − ct² + a| for |c|, |a| ≤ 3 and 0 ≤ t ≤ T. -/
def NB (T : ℝ) : ℝ := 4 * T + 3 * T ^ 2 + 3

/-- The Lipschitz constant. -/
def KL (B T : ℝ) : ℝ := NB T + B * T ^ 2 + B + 1

theorem coef_bound {T t c a : ℝ} (ht : t ∈ Icc 2 T) (hc : |c| ≤ 3) (ha : |a| ≤ 3) :
    |4 * t - c * t ^ 2 + a| ≤ NB T := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have h1 : |c * t ^ 2| ≤ 3 * T ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ t ^ 2)]
    have : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
    nlinarith [abs_nonneg c]
  have h2 : |4 * t| ≤ 4 * T := by rw [abs_of_nonneg (by positivity)]; linarith [ht.2]
  unfold NB
  calc |4 * t - c * t ^ 2 + a| ≤ |4 * t - c * t ^ 2| + |a| := abs_add_le _ _
    _ ≤ |4 * t| + |c * t ^ 2| + |a| := by gcongr; exact abs_sub _ _
    _ ≤ _ := by linarith

theorem sq_sub_one_ge {T t : ℝ} (ht : t ∈ Icc 2 T) : 3 ≤ t ^ 2 - 1 := by nlinarith [ht.1]

theorem NB_ge {T : ℝ} (hT : 2 ≤ T) : 23 ≤ NB T := by unfold NB; nlinarith

theorem lipG {B T t : ℝ} (hB : 0 ≤ B) (ht : t ∈ Icc 2 T) (x y : E) :
    dist (G B t x) (G B t y) ≤ KL B T * dist x y := by
  have hT : 2 ≤ T := ht.1.trans ht.2
  have h3 := sq_sub_one_ge ht
  have hT2 : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by linarith [ht.1]) ht.2 2
  simp only [G, Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, max_self]
  set d := max |x.1 - y.1| (max |x.2.1 - y.2.1| (max |x.2.2.1 - y.2.2.1| |x.2.2.2 - y.2.2.2|)) with hd
  have d1 : |x.1 - y.1| ≤ d := le_max_left _ _
  have d2 : |x.2.1 - y.2.1| ≤ d := (le_max_left _ _).trans (le_max_right _ _)
  have d3 : |x.2.2.1 - y.2.2.1| ≤ d := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have d4 : |x.2.2.2 - y.2.2.2| ≤ d := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hd0 : 0 ≤ d := (abs_nonneg _).trans d1
  have hNB := NB_ge hT
  have hK : KL B T = NB T + B * T ^ 2 + B + 1 := rfl
  have hBT : 0 ≤ B * T ^ 2 := by positivity
  have hKd : 0 ≤ KL B T * d := mul_nonneg (by rw [hK]; linarith) hd0
  refine max_le ?_ (max_le ?_ hKd)
  · -- the L component
    rw [← _root_.sub_div, abs_div, abs_of_pos (show (0 : ℝ) < t ^ 2 - 1 by linarith),
      div_le_iff₀ (show (0 : ℝ) < t ^ 2 - 1 by linarith)]
    have := cl_sub B x.2.1 y.2.1
    nlinarith
  · -- the P component
    have cx := abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) x.2.2.1
    have cy := abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) y.2.2.1
    have ax := abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) x.2.2.2
    have ay := abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) y.2.2.2
    have Ny := abs_cl_le hB y.1
    have hN := coef_bound ht cx ax
    set Nx := 4 * t - cl 3 x.2.2.1 * t ^ 2 + cl 3 x.2.2.2
    set Ny' := 4 * t - cl 3 y.2.2.1 * t ^ 2 + cl 3 y.2.2.2
    have hdiff : |Nx - Ny'| ≤ T ^ 2 * d + d := by
      have e : Nx - Ny' = -((cl 3 x.2.2.1 - cl 3 y.2.2.1) * t ^ 2) + (cl 3 x.2.2.2 - cl 3 y.2.2.2) := by
        simp only [Nx, Ny']; ring
      rw [e]
      have s1 := cl_sub 3 x.2.2.1 y.2.2.1
      have s2 := cl_sub 3 x.2.2.2 y.2.2.2
      calc _ ≤ |-((cl 3 x.2.2.1 - cl 3 y.2.2.1) * t ^ 2)| + |cl 3 x.2.2.2 - cl 3 y.2.2.2| := abs_add_le _ _
        _ ≤ T ^ 2 * d + d := by
          rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t ^ 2)]
          have : |cl 3 x.2.2.1 - cl 3 y.2.2.1| * t ^ 2 ≤ d * T ^ 2 :=
            mul_le_mul (s1.trans d3) hT2 (by positivity) hd0
          linarith
    have e : -(Nx * cl B x.1) - -(Ny' * cl B y.1) = -(Nx * (cl B x.1 - cl B y.1) + (Nx - Ny') * cl B y.1) := by
      ring
    rw [e, abs_neg]
    have s := cl_sub B x.1 y.1
    calc |Nx * (cl B x.1 - cl B y.1) + (Nx - Ny') * cl B y.1|
        ≤ |Nx| * |cl B x.1 - cl B y.1| + |Nx - Ny'| * |cl B y.1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ NB T * d + (T ^ 2 * d + d) * B := by
          gcongr
          · exact s.trans d1
      _ ≤ KL B T * d := by rw [hK]; nlinarith

theorem normG {B T t : ℝ} (hB : 0 ≤ B) (ht : t ∈ Icc 2 T) (x : E) : ‖G B t x‖ ≤ NB T * B := by
  have hT : 2 ≤ T := ht.1.trans ht.2
  have h3 := sq_sub_one_ge ht
  have hNB := NB_ge hT
  simp only [G, Prod.norm_def, Real.norm_eq_abs, norm_zero, max_self]
  refine max_le ?_ (max_le ?_ (mul_nonneg (by linarith) hB))
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < t ^ 2 - 1 by linarith),
      div_le_iff₀ (show (0 : ℝ) < t ^ 2 - 1 by linarith)]
    have := abs_cl_le hB x.2.1
    have h69 : 1 ≤ NB T * (t ^ 2 - 1) := by nlinarith
    have := mul_le_mul_of_nonneg_left h69 hB
    linarith
  · rw [abs_neg, abs_mul]
    have hN := coef_bound ht (abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) x.2.2.1)
      (abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) x.2.2.2)
    exact mul_le_mul hN (abs_cl_le hB x.1) (abs_nonneg _) (by linarith)

theorem contG {B T : ℝ} (x : E) : ContinuousOn (fun t => G B t x) (Icc 2 T) := by
  have hne : ∀ t ∈ Icc (2 : ℝ) T, t ^ 2 - 1 ≠ 0 := fun t ht => by linarith [sq_sub_one_ge ht]
  unfold G
  refine ContinuousOn.prodMk ?_ (ContinuousOn.prodMk ?_ continuousOn_const)
  · exact continuousOn_const.div (by fun_prop) hne
  · exact (Continuous.continuousOn (by fun_prop))

theorem exists_flow {B T r : ℝ} (hB : 0 ≤ B) (hT : 2 < T) (hr : 0 ≤ r) : ∃ α : E → ℝ → E,
    (∀ p ∈ Metric.closedBall (0 : E) r, α p 2 = p ∧
      ∀ t ∈ Icc (2 : ℝ) T, HasDerivWithinAt (α p) (G B t (α p t)) (Icc 2 T) t) ∧
    ∃ L : ℝ, ∀ t ∈ Icc (2 : ℝ) T, ∀ p ∈ Metric.closedBall (0 : E) r,
      ∀ q ∈ Metric.closedBall (0 : E) r, dist (α p t) (α q t) ≤ L * dist p q := by
  have hNB := NB_ge hT.le
  have hA : (0 : ℝ) ≤ r + NB T * B * (T - 2) := by
    have : 0 ≤ NB T * B * (T - 2) := mul_nonneg (mul_nonneg (by linarith) hB) (by linarith)
    linarith
  have hK : (0 : ℝ) ≤ KL B T := by
    unfold KL; have : 0 ≤ B * T ^ 2 := by positivity
    linarith
  have hL : (0 : ℝ) ≤ NB T * B := mul_nonneg (by linarith) hB
  have hPL : IsPicardLindelof (G B) (tmin := 2) (tmax := T) ⟨2, le_rfl, hT.le⟩ (0 : E)
      (Real.toNNReal (r + NB T * B * (T - 2))) (Real.toNNReal r) (Real.toNNReal (NB T * B))
      (Real.toNNReal (KL B T)) :=
    { lipschitzOnWith := fun t ht => by
        refine (LipschitzWith.of_dist_le_mul fun x y => ?_).lipschitzOnWith
        rw [Real.coe_toNNReal _ hK]
        exact lipG hB ht x y
      continuousOn := fun x _ => contG x
      norm_le := fun t ht x _ => by
        rw [Real.coe_toNNReal _ hL]
        exact normG hB ht x
      mul_max_le := by
        rw [Real.coe_toNNReal _ hA, Real.coe_toNNReal _ hr, Real.coe_toNNReal _ hL]
        simp only [sub_self]
        rw [max_eq_left (by linarith)]
        linarith }
  obtain ⟨α, hα, L', hlip⟩ := hPL.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨α, fun p hp => hα p (by simpa [Real.coe_toNNReal _ hr] using hp), L', fun t ht p hp q hq => ?_⟩
  exact (hlip t ht).dist_le_mul p (by simpa [Real.coe_toNNReal _ hr] using hp) q
    (by simpa [Real.coe_toNNReal _ hr] using hq)

/-! ## The clamps are inactive -/

theorem mono_Ici {f : ℝ → E} {d : E} {T x : ℝ} (h : HasDerivWithinAt f d (Icc 2 T) x) (hx : x ∈ Ico (2 : ℝ) T) :
    HasDerivWithinAt f d (Ici x) x :=
  h.mono_of_mem_nhdsWithin (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1))

/-- A solution of the clamped system on [2, T] keeps its k and A. -/
theorem flow_param_const {B T : ℝ} {α : ℝ → E}
    (hα : ∀ t ∈ Icc (2 : ℝ) T, HasDerivWithinAt α (G B t (α t)) (Icc 2 T) t) :
    ∀ t ∈ Icc (2 : ℝ) T, (α t).2.2 = (α 2).2.2 := by
  have hc : ContinuousOn (fun t => (α t).2.2) (Icc 2 T) := fun t ht =>
    (continuous_snd.comp continuous_snd).continuousAt.comp_continuousWithinAt (hα t ht).continuousWithinAt
  refine constant_of_has_deriv_right_zero hc (fun t ht => ?_)
  have h := mono_Ici (hα t (Ico_subset_Icc_self ht)) ht
  refine h.hasFDerivWithinAt.snd.snd.hasDerivWithinAt.congr_deriv ?_
  simp [G]

/-- Gronwall: max(|L|, |P|) grows at most like e^{NB (ξ − 2)} along a solution of the clamped system. -/
theorem flow_bound {B T δ : ℝ} (hB : 0 ≤ B) {α : ℝ → E}
    (hα : ∀ t ∈ Icc (2 : ℝ) T, HasDerivWithinAt α (G B t (α t)) (Icc 2 T) t)
    (h0 : ‖((α 2).1, (α 2).2.1)‖ ≤ δ) :
    ∀ t ∈ Icc (2 : ℝ) T, ‖((α t).1, (α t).2.1)‖ ≤ δ * Real.exp (NB T * (t - 2)) := by
  intro t ht
  have hT : 2 ≤ T := ht.1.trans ht.2
  have hNB := NB_ge hT
  set f : ℝ → ℝ × ℝ := fun s => ((α s).1, (α s).2.1)
  have hf' : ∀ s ∈ Icc (2 : ℝ) T, HasDerivWithinAt f ((G B s (α s)).1, (G B s (α s)).2.1) (Icc 2 T) s := by
    intro s hs
    have h := (hα s hs).hasFDerivWithinAt
    exact (h.fst.prodMk h.snd.fst).hasDerivWithinAt.congr_deriv (by simp)
  have hc : ContinuousOn f (Icc 2 T) := fun s hs => (hf' s hs).continuousWithinAt
  have := norm_le_gronwallBound_of_norm_deriv_right_le (K := NB T) (ε := 0) hc
    (fun s hs => (hf' s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) h0
    (fun s hs => ?_) t ht
  · rwa [gronwallBound_ε0] at this
  · have hs' := Ico_subset_Icc_self hs
    have h3 := sq_sub_one_ge hs'
    simp only [G, f, Prod.norm_def, Real.norm_eq_abs, add_zero]
    have hP : |(α s).2.1| ≤ max |(α s).1| |(α s).2.1| := le_max_right _ _
    have hLm : |(α s).1| ≤ max |(α s).1| |(α s).2.1| := le_max_left _ _
    refine max_le ?_ ?_
    · rw [abs_div, abs_of_pos (show (0 : ℝ) < s ^ 2 - 1 by linarith),
        div_le_iff₀ (show (0 : ℝ) < s ^ 2 - 1 by linarith)]
      have := (abs_le_abs_cl (B := B) hB (α s).2.1)
      have h69 : 1 ≤ NB T * (s ^ 2 - 1) := by nlinarith
      have hm0 : 0 ≤ max |(α s).1| |(α s).2.1| := (abs_nonneg _).trans hP
      have := mul_le_mul_of_nonneg_left h69 hm0
      linarith
    · rw [abs_neg, abs_mul]
      have hN := coef_bound hs' (abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) (α s).2.2.1)
        (abs_cl_le (by norm_num : (0 : ℝ) ≤ 3) (α s).2.2.2)
      have := abs_le_abs_cl (B := B) hB (α s).1
      exact mul_le_mul hN (this.trans hLm) (abs_nonneg _) (by linarith)
where
  /-- |cl B y| ≤ |y|. -/
  abs_le_abs_cl {B : ℝ} (hB : 0 ≤ B) (y : ℝ) : |cl B y| ≤ |y| := by
    have := cl_sub B y 0
    have h0 : cl B 0 = 0 := cl_of_abs_le (by simpa using hB)
    simpa [h0] using this

/-- **The clamps are inactive.** A solution of the clamped system on [2, T] with k, A ∈ [0, 3] and
max(|L(2)|, |P(2)|) ≤ δ, δ e^{NB (T − 2)} ≤ B, solves L′ = P/(ξ² − 1), P′ = −(4ξ − kξ² + A) L on [2, T]. -/
theorem flow_solves {B T δ : ℝ} (hB : 0 ≤ B) (hδB : δ * Real.exp (NB T * (T - 2)) ≤ B) {α : ℝ → E}
    (hα : ∀ t ∈ Icc (2 : ℝ) T, HasDerivWithinAt α (G B t (α t)) (Icc 2 T) t)
    (h0 : ‖((α 2).1, (α 2).2.1)‖ ≤ δ) (hk : |(α 2).2.2.1| ≤ 3) (hA : |(α 2).2.2.2| ≤ 3) :
    ∀ t ∈ Icc (2 : ℝ) T,
      HasDerivWithinAt (fun s => (α s).1) ((α t).2.1 / (t ^ 2 - 1)) (Icc 2 T) t ∧
      HasDerivWithinAt (fun s => (α s).2.1)
        (-((4 * t - (α 2).2.2.1 * t ^ 2 + (α 2).2.2.2) * (α t).1)) (Icc 2 T) t := by
  intro t ht
  have hT : 2 ≤ T := ht.1.trans ht.2
  have hNB := NB_ge hT
  have hb := flow_bound hB hα h0 t ht
  have hexp : Real.exp (NB T * (t - 2)) ≤ Real.exp (NB T * (T - 2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by linarith))
  have hδ : 0 ≤ δ := (norm_nonneg _).trans h0
  have hn : ‖((α t).1, (α t).2.1)‖ ≤ B := hb.trans ((mul_le_mul_of_nonneg_left hexp hδ).trans hδB)
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hn
  have hL : cl B (α t).1 = (α t).1 := cl_of_abs_le ((le_max_left _ _).trans hn)
  have hP : cl B (α t).2.1 = (α t).2.1 := cl_of_abs_le ((le_max_right _ _).trans hn)
  have hc := flow_param_const hα t ht
  have hk' : cl 3 (α t).2.2.1 = (α 2).2.2.1 := by rw [hc]; exact cl_of_abs_le hk
  have hA' : cl 3 (α t).2.2.2 = (α 2).2.2.2 := by rw [hc]; exact cl_of_abs_le hA
  have h := (hα t ht).hasFDerivWithinAt
  refine ⟨?_, ?_⟩
  · have := h.fst.hasDerivWithinAt
    simpa [G, hP] using this
  · have := h.snd.fst.hasDerivWithinAt
    simpa [G, hL, hk', hA'] using this

end Work.Quantum.RadialFlow
