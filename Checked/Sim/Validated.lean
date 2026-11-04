import Mathlib.Analysis.ODE.Gronwall

/-!
# Generic validated cell step for any vector field (no invariant needed)

THE RESULT part 1 ("rigorous simulators"), generalising the Duffing simulator of run
2026-11-04T0628Z, which needed a hand-made energy invariant to keep every solution inside the
box where the field is Lipschitz. Here the confinement comes from the enclosure itself
(continuous induction): if an approximate trajectory `g` stays a distance `B'` inside the set
`S` where the field `F` is `K`-Lipschitz, and the Grönwall bound `B` of the cell is below `B'`,
then every true solution starting within `δ` of `g` stays within `B` of `g` on the whole cell —
and hence in `S`. Works in any real normed space (e.g. ℝ × ℝ with the sup norm).
-/

namespace Checked.Sim.Validated
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Validated cell step with confinement by the enclosure itself. -/
theorem tube_cell {F : E → E} {K : NNReal} {S : Set E} (hF : LipschitzOnWith K F S)
    {f g g' : ℝ → E} {a b δ ε B B' : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (F (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (hdef : ∀ t ∈ Ico a b, dist (g' t) (F (g t)) ≤ ε)
    (htube : ∀ t ∈ Icc a b, ∀ y, dist y (g t) < B' → y ∈ S)
    (hBB : B < B') (h0 : dist (f a) (g a) ≤ δ)
    (hgron : ∀ t ∈ Icc a b, gronwallBound δ K ε (t - a) ≤ B) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ B := by
  have hB0 : 0 ≤ B := by
    have := hgron a ⟨le_rfl, hab⟩
    rw [sub_self, gronwallBound_x0] at this
    exact dist_nonneg.trans (h0.trans this)
  have hB'0 : 0 < B' := lt_of_le_of_lt hB0 hBB
  -- Grönwall on [a, c] once f is known to stay in S on [a, c)
  have gr : ∀ c ∈ Icc a b, (∀ u ∈ Ico a c, f u ∈ S) →
      ∀ t ∈ Icc a c, dist (f t) (g t) ≤ B := by
    intro c hc hS t ht
    have hsub : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hc.2
    have hsub' : Ico a c ⊆ Ico a b := Ico_subset_Ico le_rfl hc.2
    have key := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => F) (s := fun _ => S)
      (K := K) (f := f) (f' := fun t => F (f t)) (εf := 0) (g := g) (g' := g') (εg := ε)
      (δ := δ) (a := a) (b := c)
      (fun _ _ => hF) (hf.mono hsub) (fun t ht => hf' t (hsub' ht)) (fun t _ => by simp)
      hS (hg.mono hsub) (fun t ht => hg' t (hsub' ht)) (fun t ht => hdef t (hsub' ht))
      (fun t ht => htube t (hsub (Ico_subset_Icc_self ht)) _ (by rw [dist_self]; exact hB'0))
      h0 t ht
    rw [zero_add] at key
    exact key.trans (hgron t (hsub ht))
  set A : Set ℝ := {c | c ∈ Icc a b ∧ ∀ u ∈ Ico a c, f u ∈ S} with hA
  have haA : a ∈ A := ⟨⟨le_rfl, hab⟩, fun u hu => absurd hu.2 (not_lt.2 hu.1)⟩
  have hbdd : BddAbove A := ⟨b, fun c hc => hc.1.2⟩
  set T := sSup A with hT
  have hTa : a ≤ T := le_csSup hbdd haA
  have hTb : T ≤ b := csSup_le ⟨a, haA⟩ fun c hc => hc.1.2
  have hTS : ∀ u ∈ Ico a T, f u ∈ S := by
    intro u hu
    obtain ⟨c, hcA, huc⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ hu.2
    exact hcA.2 u ⟨hu.1, huc⟩
  have hTmem : T ∈ Icc a b := ⟨hTa, hTb⟩
  have hTB : dist (f T) (g T) ≤ B := gr T hTmem hTS T ⟨hTa, le_rfl⟩
  rcases eq_or_lt_of_le hTb with hTb' | hTb'
  · have h := gr T hTmem hTS
    rw [hTb'] at h
    exact h
  · exfalso
    have hcont : ContinuousWithinAt (fun t => dist (f t) (g t)) (Icc a b) T :=
      ((hf T hTmem).dist (hg T hTmem))
    obtain ⟨η, hη, hηb⟩ := Metric.continuousWithinAt_iff.1 hcont (B' - B) (by linarith)
    set c := min (T + η / 2) b with hc
    have hTc : T < c := lt_min (by linarith) hTb'
    have hcA : c ∈ A := by
      refine ⟨⟨by linarith, min_le_right _ _⟩, fun u hu => ?_⟩
      rcases lt_or_ge u T with huT | huT
      · exact hTS u ⟨hu.1, huT⟩
      · have huc : u < c := hu.2
        have hub : u ∈ Icc a b := ⟨hu.1, le_trans huc.le (min_le_right _ _)⟩
        have hdu : dist u T < η := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith)]
          linarith [min_le_left (T + η / 2) b]
        have h1 := hηb hub hdu
        rw [Real.dist_eq] at h1
        have h2 : dist (f u) (g u) < B' := by
          have := (abs_lt.1 h1).2
          linarith
        exact htube u hub (f u) h2
    have := le_csSup hbdd hcA
    linarith

end Checked.Sim.Validated
