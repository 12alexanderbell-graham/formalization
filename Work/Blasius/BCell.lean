import Mathlib
import Checked.Sim.ODETools
import Checked.Math.LECell

/-!
# Blasius: one validated Grönwall cell for g''' + g g''/2 = 0 (run 2026-11-07T1228Z)

The system g' = p, p' = q, q' = −g q/2 on ℝ × ℝ × ℝ (sup norm), confined to a slab |g| ≤ GH,
|q| ≤ QH where it is Lipschitz with constant max(1, (GH + QH)/2). `cell` is
`Checked.Math.LECell.tube_cell_t` (confinement by the enclosure itself) for this field, with
Taylor polynomials `pg`, `pp`, `pq` in σ = t − t0 as the approximate solution.
-/

namespace Work.Blasius.BCell
open Set Checked.Sim Checked.Math.LECell

/-- The Blasius field (g, p, q) ↦ (p, q, −g q/2). -/
noncomputable def blF (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (y.2.1, y.2.2, -(y.1 * y.2.2 / 2))

/-- The slab |g| ≤ GH, |q| ≤ QH. -/
def slab (GH QH : ℝ) : Set (ℝ × ℝ × ℝ) := {y | |y.1| ≤ GH ∧ |y.2.2| ≤ QH}

theorem lip_slab {GH QH K : ℝ} (hK1 : 1 ≤ K) (hK : (GH + QH) / 2 ≤ K) :
    LipschitzOnWith (Real.toNNReal K) blF (slab GH QH) := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  have hK0 : (0 : ℝ) ≤ K := by linarith
  rw [Real.coe_toNNReal _ hK0]
  simp only [blF, Prod.dist_eq, Real.dist_eq]
  set m := max |y.1 - z.1| (max |y.2.1 - z.2.1| |y.2.2 - z.2.2|)
  have hd1 : |y.1 - z.1| ≤ m := le_max_left _ _
  have hd2 : |y.2.1 - z.2.1| ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hd3 : |y.2.2 - z.2.2| ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  obtain ⟨hy1, hy3⟩ := hy
  obtain ⟨hz1, hz3⟩ := hz
  refine max_le (by nlinarith) (max_le (by nlinarith) ?_)
  have e : -(y.1 * y.2.2 / 2) - -(z.1 * z.2.2 / 2) =
      -((y.1 - z.1) * y.2.2 + z.1 * (y.2.2 - z.2.2)) / 2 := by ring
  rw [e, abs_div, abs_neg, abs_two]
  have h1 : |(y.1 - z.1) * y.2.2| ≤ QH * m := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul hy3 hd1 (abs_nonneg _) ((abs_nonneg _).trans hy3)
  have h2 : |z.1 * (y.2.2 - z.2.2)| ≤ GH * m := by
    rw [abs_mul]
    exact mul_le_mul hz1 hd3 (abs_nonneg _) ((abs_nonneg _).trans hz1)
  have h3 := abs_add_le ((y.1 - z.1) * y.2.2) (z.1 * (y.2.2 - z.2.2))
  have h4 : (GH + QH) * m ≤ 2 * K * m := by nlinarith
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- One validated step on the cell [t₀, t₀ + h] ⊆ [0, T] for every solution (g, p, q) of the
Blasius system (derivatives within [0, T]). -/
theorem cell (pg pp pq : List ℚ) {g p q : ℝ → ℝ} {T t0 h δ ε B GH QH K : ℝ}
    (ht0 : 0 ≤ t0) (hT : t0 + h ≤ T) (hh : 0 < h) (hK1 : 1 ≤ K)
    (hK : (GH + QH) / 2 ≤ K) (hKh : K * h < 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hg : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt g (p t) (Icc 0 T) t)
    (hp : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt p (q t) (Icc 0 T) t)
    (hq : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt q (-(g t * q t / 2)) (Icc 0 T) t)
    (hg1 : ∀ σ ∈ Icc 0 h, -(GH - 1 / 100) ≤ evalQ pg σ)
    (hg2 : ∀ σ ∈ Icc 0 h, evalQ pg σ ≤ GH - 1 / 100)
    (hq1 : ∀ σ ∈ Icc 0 h, -(QH - 1 / 100) ≤ evalQ pq σ)
    (hq2 : ∀ σ ∈ Icc 0 h, evalQ pq σ ≤ QH - 1 / 100)
    (hd1 : ∀ σ ∈ Icc 0 h, |dEvalQ pg σ - evalQ pp σ| ≤ ε)
    (hd2 : ∀ σ ∈ Icc 0 h, |dEvalQ pp σ - evalQ pq σ| ≤ ε)
    (hd3 : ∀ σ ∈ Icc 0 h, |dEvalQ pq σ + evalQ pg σ * evalQ pq σ / 2| ≤ ε)
    (h0 : |g t0 - evalQ pg 0| ≤ δ) (h0' : |p t0 - evalQ pp 0| ≤ δ)
    (h0'' : |q t0 - evalQ pq 0| ≤ δ)
    (hB : δ * (1 / (1 - K * h)) + ε / K * (1 / (1 - K * h) - 1) ≤ B)
    (hBM : B < 1 / 100) :
    ∀ t ∈ Icc t0 (t0 + h), |g t - evalQ pg (t - t0)| ≤ B ∧ |p t - evalQ pp (t - t0)| ≤ B ∧
      |q t - evalQ pq (t - t0)| ≤ B := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hT0 : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0 hT
  have hs : ∀ t ∈ Icc t0 (t0 + h), t - t0 ∈ Icc 0 h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set f : ℝ → ℝ × ℝ × ℝ := fun t => (g t, p t, q t) with hfdef
  set a : ℝ → ℝ × ℝ × ℝ := fun t => (evalQ pg (t - t0), evalQ pp (t - t0), evalQ pq (t - t0))
    with ha
  have hfd : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt f (blF (f t)) (Icc 0 T) t :=
    fun t ht => (hg t ht).prodMk ((hp t ht).prodMk (hq t ht))
  have key := tube_cell_t (F := fun _ => blF) (K := Real.toNNReal K) (S := slab GH QH) (f := f)
    (g := a)
    (g' := fun t => (dEvalQ pg (t - t0), dEvalQ pp (t - t0), dEvalQ pq (t - t0)))
    (a := t0) (b := t0 + h) (δ := δ) (ε := ε) (B := B) (B' := 1 / 100)
    (fun _ _ => lip_slab hK1 hK) (by linarith)
    (fun t ht => ((hfd t ht).continuousWithinAt).mono hT0)
    (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht0], by linarith [ht.2]⟩))
    (((continuous_evalQ pg).comp (continuous_sub_right t0)).prodMk
      (((continuous_evalQ pp).comp (continuous_sub_right t0)).prodMk
        ((continuous_evalQ pq).comp (continuous_sub_right t0)))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ pg (t - t0)).comp_sub_const t t0).prodMk
      (((hasDerivAt_evalQ pp (t - t0)).comp_sub_const t t0).prodMk
        ((hasDerivAt_evalQ pq (t - t0)).comp_sub_const t t0))).hasDerivWithinAt)
    (fun t ht => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      simp only [ha, blF, Prod.dist_eq, Real.dist_eq]
      refine max_le (hd1 _ hσ) (max_le (hd2 _ hσ) ?_)
      have e : dEvalQ pq (t - t0) - -(evalQ pg (t - t0) * evalQ pq (t - t0) / 2) =
          dEvalQ pq (t - t0) + evalQ pg (t - t0) * evalQ pq (t - t0) / 2 := by ring
      rw [e]; exact hd3 _ hσ)
    (fun t ht z hz => by
      simp only [ha, Prod.dist_eq, Real.dist_eq, max_lt_iff] at hz
      have g1 := hg1 _ (hs t ht)
      have g2 := hg2 _ (hs t ht)
      have q1 := hq1 _ (hs t ht)
      have q2 := hq2 _ (hs t ht)
      have a1 := abs_lt.1 hz.1
      have a3 := abs_lt.1 hz.2.2
      refine ⟨?_, ?_⟩
      · rw [abs_le]; constructor <;> linarith [a1.1, a1.2]
      · rw [abs_le]; constructor <;> linarith [a3.1, a3.2])
    hBM
    (by
      simp only [hfdef, ha, sub_self, Prod.dist_eq, Real.dist_eq]
      exact max_le h0 (max_le h0' h0''))
    (fun t ht => by
      rw [Real.coe_toNNReal _ hK0.le]
      have := gronwallBound_le_cell (K := K) hδ hε hK0
        (show t - t0 ≤ h by linarith [ht.2]) hh hKh
      exact this.trans hB)
  intro t ht
  have h1 := key t ht
  simp only [hfdef, ha, Prod.dist_eq, Real.dist_eq] at h1
  exact ⟨(le_max_left _ _).trans h1, ((le_max_left _ _).trans (le_max_right _ _)).trans h1,
    ((le_max_right _ _).trans (le_max_right _ _)).trans h1⟩

end Work.Blasius.BCell
