import Work.FSRev.RCell
import Work.FSAtt.AAssemble

/-! Falkner–Skan adverse pressure gradient with a free coefficient K: strict clamp enclosures on checked
cells, and the identification of an unclamped solution with a clamped one that stays strictly inside the
clamps (first-exit argument with forward uniqueness of the clamped field). Run 2026-11-11T1228Z. -/

namespace Work.FSRev.RIdent
open Set Filter Topology Checked.Sim Checked.Sim.QPoly Checked.FSSep.SCellWC Checked.FSNeg.NBase
  Checked.FSSep.SBase Work.FSRev.RCell

/-- Strictly inside the clamps of `vS`. -/
def PhiS (g p q : ℝ → ℝ) (t : ℝ) : Prop := |g t| < t + 2 ∧ |p t| < 2 ∧ |q t| < 2

/-- On a checked cell the enclosed solution lies strictly inside the clamps. -/
theorem cell_box_lt {K T : ℚ} (c : Cell) (hok : cellOK K T c = true) {g p q : ℝ → ℝ}
    (hs : SolC (K : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), PhiS g p q t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, kg1, kg2, kp1, kp2, kq1, kq2, -⟩ :
    CellProp K T c := of_decide_eq_true hok
  intro t ht
  obtain ⟨b1, b2, b3⟩ := encl c hok hs h0 t ht
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have lg := lower_q c.pg (h := c.h) hσ.1 hσ.2
  have ug := upper_q c.pg (h := c.h) hσ.1 hσ.2
  have lp := lower_q c.pp (h := c.h) hσ.1 hσ.2
  have up := upper_q c.pp (h := c.h) hσ.1 hσ.2
  have lq := lower_q c.pq (h := c.h) hσ.1 hσ.2
  have uq := upper_q c.pq (h := c.h) hσ.1 hσ.2
  have kg1' : ((-(c.t0 + 2) : ℚ) : ℝ) < ((glo c - c.r1 : ℚ) : ℝ) := by exact_mod_cast kg1
  have kg2' : ((ghi c + c.r1 : ℚ) : ℝ) < ((c.t0 + 2 : ℚ) : ℝ) := by exact_mod_cast kg2
  have kp1' : ((-2 : ℚ) : ℝ) < ((plo c - c.r2 : ℚ) : ℝ) := by exact_mod_cast kp1
  have kp2' : ((phi c + c.r2 : ℚ) : ℝ) < ((2 : ℚ) : ℝ) := by exact_mod_cast kp2
  have kq1' : ((-2 : ℚ) : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast kq1
  have kq2' : ((qhi c + c.B : ℚ) : ℝ) < ((2 : ℚ) : ℝ) := by exact_mod_cast kq2
  simp only [glo, ghi, plo, phi, qlo, qhi] at kg1' kg2' kp1' kp2' kq1' kq2'
  push_cast at kg1' kg2' kp1' kp2' kq1' kq2' lg ug lp up lq uq
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  refine ⟨abs_lt.2 ⟨by linarith [ht.1], by linarith [ht.1]⟩, abs_lt.2 ⟨by linarith, by linarith⟩,
    abs_lt.2 ⟨by linarith, by linarith⟩⟩

/-- The unclamped coefficient-K field. -/
def uS (K : ℝ) (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (y.2.1, y.2.2, -(K * y.1 * y.2.2) + 1 - y.2.1 ^ 2)

theorem vS_eq {K t : ℝ} (ht : 0 ≤ t) {y : ℝ × ℝ × ℝ} (h1 : |y.1| ≤ t + 2) (h2 : |y.2.1| ≤ 2)
    (h3 : |y.2.2| ≤ 2) : vS K t y = uS K y := by
  simp only [vS, uS, max_eq_left ht, cl_of_abs_le h1, cl_of_abs_le h2, cl_of_abs_le h3]

/-- Identification: a solution `Z` of the unclamped field on [0, T] with the initial value of a solution `Y`
of the clamped field that stays strictly inside the clamps on [0, T] equals `Y` on [0, T]. -/
theorem ident {K T : ℝ} (hT : 0 ≤ T) {Y Z : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 T) t)
    (hYb : ∀ t ∈ Icc 0 T, PhiS (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) t)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (uS K (Z t)) (Icc 0 T) t)
    (h0 : Y 0 = Z 0) : EqOn Y Z (Icc 0 T) := by
  set S : Set ℝ := {τ | τ ∈ Icc 0 T ∧ EqOn Y Z (Icc 0 τ)} with hSd
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT⟩, fun u hu => by
    have : u = 0 := le_antisymm hu.2 hu.1
    rw [this]; exact h0⟩
  have hbdd : BddAbove S := ⟨T, fun τ hτ => hτ.1.2⟩
  set σ := sSup S with hσ
  have hσ0 : 0 ≤ σ := le_csSup hbdd h0S
  have hσT : σ ≤ T := csSup_le ⟨0, h0S⟩ (fun τ hτ => hτ.1.2)
  have cY : ContinuousOn Y (Icc 0 T) := fun t ht => (hY t ht).continuousWithinAt
  have cZ : ContinuousOn Z (Icc 0 T) := fun t ht => (hZ t ht).continuousWithinAt
  -- equality on [0, σ)
  have hlt : EqOn Y Z (Ico 0 σ) := by
    intro u hu
    obtain ⟨τ, hτS, huτ⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ hu.2
    exact hτS.2 ⟨hu.1, huτ.le⟩
  have hσS : σ ∈ S := by
    refine ⟨⟨hσ0, hσT⟩, ?_⟩
    rcases eq_or_lt_of_le hσ0 with h | h
    · intro u hu
      have : u = 0 := le_antisymm (h ▸ hu.2) hu.1
      rw [this]; exact h0
    · exact hlt.of_subset_closure (cY.mono (Icc_subset_Icc_right hσT))
        (cZ.mono (Icc_subset_Icc_right hσT)) Ico_subset_Icc_self
        (by rw [closure_Ico h.ne])
  by_contra hne
  have hσT' : σ < T := by
    rcases eq_or_lt_of_le hσT with h | h
    · exact absurd (h ▸ hσS.2) hne
    · exact h
  -- Z is strictly inside the clamps at σ, hence inside them on [σ, σ + ε]
  obtain ⟨b1, b2, b3⟩ := hYb σ ⟨hσ0, hσT⟩
  have hYZσ : Y σ = Z σ := hσS.2 ⟨hσ0, le_rfl⟩
  set m := min (min (σ + 2 - |(Z σ).1|) (2 - |(Z σ).2.1|)) (2 - |(Z σ).2.2|) with hm
  have hm0 : 0 < m := by
    simp only [hYZσ] at b1 b2 b3
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have m1 : m ≤ σ + 2 - |(Z σ).1| := (min_le_left _ _).trans (min_le_left _ _)
  have m2 : m ≤ 2 - |(Z σ).2.1| := (min_le_left _ _).trans (min_le_right _ _)
  have m3 : m ≤ 2 - |(Z σ).2.2| := min_le_right _ _
  obtain ⟨δ, hδ, hcl⟩ := Metric.continuousWithinAt_iff.1 (cZ σ ⟨hσ0, hσT⟩) m hm0
  set ε := min (δ / 2) (T - σ) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεT : σ + ε ≤ T := by linarith [min_le_right (δ / 2) (T - σ)]
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hZb : ∀ u ∈ Icc 0 (σ + ε), |(Z u).1| ≤ u + 2 ∧ |(Z u).2.1| ≤ 2 ∧ |(Z u).2.2| ≤ 2 := by
    intro u hu
    rcases le_total u σ with h | h
    · have e := hσS.2 ⟨hu.1, h⟩
      obtain ⟨c1, c2, c3⟩ := hYb u ⟨hu.1, h.trans hσT⟩
      simp only [e] at c1 c2 c3
      exact ⟨c1.le, c2.le, c3.le⟩
    · have hd : dist u σ < δ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.2]
      have k := hcl ⟨hu.1, hu.2.trans hεT⟩ hd
      have k0 := (Work.FSAtt.AAssemble.dist_c0 (a := Z u) (b := Z σ)).trans_lt k
      have k1 := (Work.FSAtt.AAssemble.dist_c1 (a := Z u) (b := Z σ)).trans_lt k
      have k2 := (Work.FSAtt.AAssemble.dist_c2 (a := Z u) (b := Z σ)).trans_lt k
      have t0 := abs_sub_abs_le_abs_sub (Z u).1 (Z σ).1
      have t1 := abs_sub_abs_le_abs_sub (Z u).2.1 (Z σ).2.1
      have t2 := abs_sub_abs_le_abs_sub (Z u).2.2 (Z σ).2.2
      exact ⟨by linarith, by linarith, by linarith⟩
  have hZc : ∀ t ∈ Icc 0 (σ + ε), HasDerivWithinAt Z (vS K t (Z t)) (Icc 0 (σ + ε)) t := by
    intro t ht
    obtain ⟨c1, c2, c3⟩ := hZb t ht
    rw [vS_eq ht.1 c1 c2 c3]
    exact (hZ t ⟨ht.1, ht.2.trans hεT⟩).mono (Icc_subset_Icc_right hεT)
  have hYc : ∀ t ∈ Icc 0 (σ + ε), HasDerivWithinAt Y (vS K t (Y t)) (Icc 0 (σ + ε)) t :=
    fun t ht => (hY t ⟨ht.1, ht.2.trans hεT⟩).mono (Icc_subset_Icc_right hεT)
  have E := Checked.FSSep.SFlow.unique_right (by linarith) hYc hZc h0
  have : σ + ε ∈ S := ⟨⟨by linarith, hεT⟩, E⟩
  have := le_csSup hbdd this
  linarith

end Work.FSRev.RIdent
