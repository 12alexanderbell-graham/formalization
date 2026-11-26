import Checked.FSRev.RCell

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient: a side condition for the checked weighted cells that, from a time `a` on, keeps the q-component positive, below a bound `X` wherever the g-component is not positive, and at `a` makes the g-component negative. Used to locate the return of the reversed-flow solution's g to zero (run 2026-11-26T0628Z). Module `RZero`. -/

namespace Checked.FSRev.RZero
open Set Checked.Sim Checked.Sim.QPoly Checked.FSSep.SCellWC Checked.FSRev.RCell

/-- From `a` on, 0 < q, and q < X wherever g ≤ 0; at `a`, g < 0. -/
def PhiZ (a X : ℝ) (g _p q : ℝ → ℝ) (t : ℝ) : Prop :=
  (a ≤ t → 0 < q t) ∧ (t = a → g t < 0) ∧ (a ≤ t → g t ≤ 0 → q t < X)

/-- The cell condition behind `PhiZ`: a cell reaching `a` has q > 0 on it, and q < X unless g > 0 on it;
a cell containing `a` has g < 0 on it. -/
def sideZ (a X : ℚ) (c : Cell) : Bool :=
  decide ((a ≤ c.t0 + c.h → 0 < qlo c - c.B) ∧
    (c.t0 ≤ a ∧ a ≤ c.t0 + c.h → ghi c + c.r1 < 0) ∧
    (a ≤ c.t0 + c.h → glo c - c.r1 ≤ 0 → qhi c + c.B < X))

theorem sideZ_spec {K T : ℚ} (a X : ℚ) (c : Cell) (hok : cellOK K T c = true) (hside : sideZ a X c = true)
    {g p q : ℝ → ℝ} (hs : SolC (K : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), PhiZ (a : ℝ) (X : ℝ) g p q t := by
  intro t ht
  obtain ⟨b1, -, b3⟩ := encl c hok hs h0 t ht
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have lg := lower_q c.pg (h := c.h) hσ.1 hσ.2
  have ug := upper_q c.pg (h := c.h) hσ.1 hσ.2
  have lq := lower_q c.pq (h := c.h) hσ.1 hσ.2
  have uq := upper_q c.pq (h := c.h) hσ.1 hσ.2
  obtain ⟨k1, k2, k3⟩ := of_decide_eq_true hside
  have a1 := abs_le.1 b1
  have a3 := abs_le.1 b3
  have hle : (a : ℝ) ≤ t → a ≤ c.t0 + c.h := fun hat => by
    have : ((a : ℚ) : ℝ) ≤ ((c.t0 + c.h : ℚ) : ℝ) := by push_cast; linarith [ht.2]
    exact_mod_cast this
  refine ⟨fun hat => ?_, fun hta => ?_, fun hat hg => ?_⟩
  · have m1' : (0 : ℝ) < ((qlo c - c.B : ℚ) : ℝ) := by exact_mod_cast k1 (hle hat)
    simp only [qlo] at m1'
    push_cast at m1' lq
    linarith
  · have hin : c.t0 ≤ a ∧ a ≤ c.t0 + c.h := by
      have e1 : ((c.t0 : ℚ) : ℝ) ≤ ((a : ℚ) : ℝ) := by rw [← hta]; exact ht.1
      have e2 : ((a : ℚ) : ℝ) ≤ ((c.t0 + c.h : ℚ) : ℝ) := by push_cast; rw [← hta]; exact ht.2
      exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
    have m3' : ((ghi c + c.r1 : ℚ) : ℝ) < 0 := by exact_mod_cast k2 hin
    simp only [ghi] at m3'
    push_cast at m3' ug
    linarith
  · have hglo : ¬ (0 < glo c - c.r1) := by
      intro hpos
      have m4 : (0 : ℝ) < ((glo c - c.r1 : ℚ) : ℝ) := by exact_mod_cast hpos
      simp only [glo] at m4
      push_cast at m4 lg
      linarith
    have m2' : ((qhi c + c.B : ℚ) : ℝ) < ((X : ℚ) : ℝ) := by exact_mod_cast k3 (hle hat) (not_lt.1 hglo)
    simp only [qhi] at m2'
    push_cast at m2' uq
    linarith

end Checked.FSRev.RZero
