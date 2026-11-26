import Work.Quantum.RadialStart
import Work.Quantum.RadialFlow
/-!
# H₂⁺ route step 2, assembled: the radial solution past ξ = 2, continuous in k (run 2026-11-26T2228Z)

Route of `runs/2026-11-26T1628Z/README.md`, step 2. Along a continuous A(k) ∈ [0, 3] (the angular root of
`AngularAssembly.angular_root`), the Frobenius solution of `RadialStart` gives at ξ = 2 the state
p₀(k) = (L(2), P(2), k, A(k)) with P = (ξ² − 1) L′ = 3 L′(2) (`p0`, continuous). `radial_flow`: for every horizon
T > 2 there is one clamped flow (`RadialFlow.exists_flow`) whose trajectories from p₀(k) solve the unclamped radial
system on [2, T] for every k ∈ [k₁, k₂], and whose state at each ξ ∈ [2, T] is continuous in k — the continuity the
events of route step 3 need. The radius r of the initial states comes from compactness of [k₁, k₂], the clamp
B = r e^{NB (T − 2)} from Gronwall (`RadialFlow.flow_solves`). No numerics.
-/

namespace Work.Quantum.RadialAssemble
open Set Filter Topology
open Work.Quantum.RadialStart Work.Quantum.RadialFlow

/-- The state at ξ = 2 of the solution regular at ξ = 1, with the parameters. -/
noncomputable def p0 (R : ℝ → ℝ) (k : ℝ) : E := (RL k (R k) 1, 3 * RLd k (R k) 1, k, R k)

theorem p0_continuousOn {k₁ k₂ : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : k₂ ≤ 3) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc k₁ k₂)) (hR3 : ∀ k ∈ Icc k₁ k₂, R k ∈ Icc (0 : ℝ) 3) :
    ContinuousOn (p0 R) (Icc k₁ k₂) := by
  obtain ⟨c0, c1⟩ := start_continuousOn hk₁ hk₂ hR hR3
  unfold p0
  exact c0.prodMk ((continuousOn_const.mul c1).prodMk (continuousOn_id.prodMk hR))

theorem radial_flow {k₁ k₂ T : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : k₂ ≤ 3) (hT : 2 < T) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc k₁ k₂)) (hR3 : ∀ k ∈ Icc k₁ k₂, R k ∈ Icc (0 : ℝ) 3) :
    ∃ α : E → ℝ → E, (∀ k ∈ Icc k₁ k₂, α (p0 R k) 2 = p0 R k ∧
      (∀ t ∈ Icc (2 : ℝ) T,
        HasDerivWithinAt (fun s => (α (p0 R k) s).1) ((α (p0 R k) t).2.1 / (t ^ 2 - 1)) (Icc 2 T) t ∧
        HasDerivWithinAt (fun s => (α (p0 R k) s).2.1)
          (-((4 * t - k * t ^ 2 + R k) * (α (p0 R k) t).1)) (Icc 2 T) t)) ∧
      ∀ t ∈ Icc (2 : ℝ) T, ContinuousOn (fun k => α (p0 R k) t) (Icc k₁ k₂) := by
  have hpc := p0_continuousOn hk₁ hk₂ hR hR3
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc
  set r := max C 0 with hr
  have hr0 : 0 ≤ r := le_max_right _ _
  have hmem : ∀ k ∈ Icc k₁ k₂, p0 R k ∈ Metric.closedBall (0 : E) r := fun k hk => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact (hC k hk).trans (le_max_left _ _)
  set B := r * Real.exp (NB T * (T - 2)) with hB
  have hB0 : 0 ≤ B := mul_nonneg hr0 (Real.exp_pos _).le
  obtain ⟨α, hα, L, hL⟩ := exists_flow hB0 hT hr0
  refine ⟨α, fun k hk => ⟨(hα _ (hmem k hk)).1, fun t ht => ?_⟩, fun t ht => ?_⟩
  · -- the clamps are inactive
    have h2 := (hα _ (hmem k hk)).1
    have hn : ‖((α (p0 R k) 2).1, (α (p0 R k) 2).2.1)‖ ≤ r := by
      rw [h2]
      have := hmem k hk
      rw [Metric.mem_closedBall, dist_zero_right] at this
      refine le_trans ?_ this
      simp only [p0, Prod.norm_def]
      exact max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
    have hk3 : |(α (p0 R k) 2).2.2.1| ≤ 3 := by
      rw [h2]; simp only [p0]; exact abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩
    have hA3 : |(α (p0 R k) 2).2.2.2| ≤ 3 := by
      rw [h2]; simp only [p0]; exact abs_le.mpr ⟨by linarith [(hR3 k hk).1], (hR3 k hk).2⟩
    have := flow_solves hB0 le_rfl (hα _ (hmem k hk)).2 hn hk3 hA3 t ht
    rw [h2] at this
    simpa only [p0] using this
  · -- continuity in k through the Lipschitz dependence on the initial point
    have hlip : LipschitzOnWith (Real.toNNReal L) (fun p => α p t) (Metric.closedBall (0 : E) r) := by
      refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => (hL t ht p hp q hq).trans ?_
      exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) dist_nonneg
    exact hlip.continuousOn.comp hpc (fun k hk => hmem k hk)

end Work.Quantum.RadialAssemble
