import Checked.Trust.NecessityAS

/-!
# Tools for `Checked.Trust.NecessityBX`: step bounds for one closed model below the density bound

Run 2026-11-25T1828Z. The witness of `Checked.Trust.NCBX` is the closed model of matter density one hundred
twenty-one ten-thousandths and curvature term minus one tenth (total density eleven tenths). Its radicand
`y(v) = m + k v² + (1 − m − k) v⁶` increases from twenty-one fiftieths to one (`bx_mono`), so the integrand
`2/√y` decreases there: a cell contributes at least its width times the integrand at its right end and at most
its width times the integrand at its left end (`bx_cell_lo`, `bx_cell_up`); the sums over a list of break points
are `bx_sum_lo`, `bx_sum_up`.
-/

namespace Checked.Trust.NCBX

open Set MeasureTheory Checked.Cosmography.B1L19CurvedTools

/-- The radicand of the witness increases on `[21/50, 1]`. -/
lemma bx_mono {v w : ℝ} (hv : 21 / 50 ≤ v) (hvw : v ≤ w) (_hw : w ≤ 1) :
    yC (121 / 10000) (-1 / 10) v ≤ yC (121 / 10000) (-1 / 10) w := by
  have e : yC (121 / 10000) (-1 / 10) w - yC (121 / 10000) (-1 / 10) v
      = (w ^ 2 - v ^ 2) * (-1 / 10 + 10879 / 10000 * (w ^ 4 + w ^ 2 * v ^ 2 + v ^ 4)) := by
    unfold yC; ring
  have hv0 : 0 ≤ v := by linarith
  have hv2 : 441 / 2500 ≤ v ^ 2 := by nlinarith
  have hw2 : 441 / 2500 ≤ w ^ 2 := by nlinarith
  have h1 : 0 ≤ w ^ 2 - v ^ 2 := by nlinarith
  have hv4 : (441 / 2500) ^ 2 ≤ v ^ 4 := by
    rw [show v ^ 4 = (v ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (by norm_num) hv2 2
  have hw4 : (441 / 2500) ^ 2 ≤ w ^ 4 := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (by norm_num) hw2 2
  have hvw2 : (441 / 2500) ^ 2 ≤ w ^ 2 * v ^ 2 := by
    rw [sq]; exact mul_le_mul hw2 hv2 (by norm_num) (by positivity)
  have h2 : 0 ≤ -1 / 10 + 10879 / 10000 * (w ^ 4 + w ^ 2 * v ^ 2 + v ^ 4) := by
    norm_num at hv4 hw4 hvw2 ⊢; linarith
  have := mul_nonneg h1 h2
  linarith

lemma bx_pos {v : ℝ} (hv : 13139 / 31250 ≤ v) (hv1 : v ≤ 1) : 0 < yC (121 / 10000) (-1 / 10) v :=
  lt_of_lt_of_le (by unfold yC; norm_num) (bx_mono (by norm_num) hv hv1)

lemma bx_cont : ContinuousOn (gC (121 / 10000) (-1 / 10)) (Icc (13139 / 31250) 1) := by
  intro v hv
  have hp := bx_pos hv.1 hv.2
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.div
  · exact (by unfold yC; fun_prop : Continuous fun v : ℝ => yC (121 / 10000) (-1 / 10) v).continuousAt.sqrt
  · exact (Real.sqrt_pos.2 hp).ne'

lemma bx_int {α β : ℝ} (hα : 13139 / 31250 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    IntervalIntegrable (gC (121 / 10000) (-1 / 10)) volume α β :=
  (bx_cont.mono (Icc_subset_Icc hα hβ)).intervalIntegrable_of_Icc hαβ

/-- A cell from below: width times the integrand bound at the right end. -/
lemma bx_cell_lo (α β s : ℝ) (hα : 13139 / 31250 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) (hs : 0 < s)
    (hy : yC (121 / 10000) (-1 / 10) β ≤ s ^ 2) :
    2 / s * (β - α) ≤ ∫ v in α..β, gC (121 / 10000) (-1 / 10) v := by
  have h := intervalIntegral.integral_mono_on hαβ intervalIntegrable_const (bx_int hα hαβ hβ)
    (fun v hv => by
      have hp := bx_pos (le_trans hα hv.1) (le_trans hv.2 hβ)
      have hyv := le_trans (bx_mono (by linarith [hv.1]) hv.2 hβ) hy
      have hsq : √(yC (121 / 10000) (-1 / 10) v) ≤ s := by
        rw [show s = √(s ^ 2) from (Real.sqrt_sq hs.le).symm]; exact Real.sqrt_le_sqrt hyv
      unfold gC
      exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hp) hsq)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-- A cell from above: width times the integrand bound at the left end. -/
lemma bx_cell_up (α β s : ℝ) (hα : 13139 / 31250 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) (hs : 0 < s)
    (hy : s ^ 2 ≤ yC (121 / 10000) (-1 / 10) α) :
    ∫ v in α..β, gC (121 / 10000) (-1 / 10) v ≤ 2 / s * (β - α) := by
  have h := intervalIntegral.integral_mono_on hαβ (bx_int hα hαβ hβ) intervalIntegrable_const
    (fun v hv => by
      have hyv := le_trans hy (bx_mono (by linarith) hv.1 (le_trans hv.2 hβ))
      have hsq : s ≤ √(yC (121 / 10000) (-1 / 10) v) := Real.le_sqrt_of_sq_le hyv
      unfold gC
      exact div_le_div_of_nonneg_left (by norm_num) hs hsq)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

/-- Summing cells from below over break points `b 0 ≤ … ≤ b N`. -/
lemma bx_sum_lo (b s : ℕ → ℝ) (N : ℕ) (hb : ∀ i ≤ N, 13139 / 31250 ≤ b i ∧ b i ≤ 1)
    (hm : ∀ i < N, b i ≤ b (i + 1)) (hs : ∀ i < N, 0 < s i)
    (hy : ∀ i < N, yC (121 / 10000) (-1 / 10) (b (i + 1)) ≤ s i ^ 2) :
    ∑ i ∈ Finset.range N, 2 / s i * (b (i + 1) - b i)
      ≤ ∫ v in b 0..b N, gC (121 / 10000) (-1 / 10) v := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ih' := ih (fun i hi => hb i (by omega)) (fun i hi => hm i (by omega))
      (fun i hi => hs i (by omega)) (fun i hi => hy i (by omega))
    have hc := bx_cell_lo (b n) (b (n + 1)) (s n) (hb n (by omega)).1 (hm n (by omega))
      (hb (n + 1) le_rfl).2 (hs n (by omega)) (hy n (by omega))
    have h0n : b 0 ≤ b n := by
      have : ∀ j ≤ n, b 0 ≤ b j := by
        intro j hj
        induction j with
        | zero => exact le_rfl
        | succ j ihj => exact le_trans (ihj (by omega)) (hm j (by omega))
      exact this n le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (bx_int (hb 0 (by omega)).1 h0n (hb n (by omega)).2)
      (bx_int (hb n (by omega)).1 (hm n (by omega)) (hb (n + 1) le_rfl).2)]
    linarith

/-- Summing cells from above over break points `b 0 ≤ … ≤ b N`. -/
lemma bx_sum_up (b s : ℕ → ℝ) (N : ℕ) (hb : ∀ i ≤ N, 13139 / 31250 ≤ b i ∧ b i ≤ 1)
    (hm : ∀ i < N, b i ≤ b (i + 1)) (hs : ∀ i < N, 0 < s i)
    (hy : ∀ i < N, s i ^ 2 ≤ yC (121 / 10000) (-1 / 10) (b i)) :
    ∫ v in b 0..b N, gC (121 / 10000) (-1 / 10) v
      ≤ ∑ i ∈ Finset.range N, 2 / s i * (b (i + 1) - b i) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ih' := ih (fun i hi => hb i (by omega)) (fun i hi => hm i (by omega))
      (fun i hi => hs i (by omega)) (fun i hi => hy i (by omega))
    have hc := bx_cell_up (b n) (b (n + 1)) (s n) (hb n (by omega)).1 (hm n (by omega))
      (hb (n + 1) le_rfl).2 (hs n (by omega)) (hy n (by omega))
    have h0n : b 0 ≤ b n := by
      have : ∀ j ≤ n, b 0 ≤ b j := by
        intro j hj
        induction j with
        | zero => exact le_rfl
        | succ j ihj => exact le_trans (ihj (by omega)) (hm j (by omega))
      exact this n le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (bx_int (hb 0 (by omega)).1 h0n (hb n (by omega)).2)
      (bx_int (hb n (by omega)).1 (hm n (by omega)) (hb (n + 1) le_rfl).2)]
    linarith

end Checked.Trust.NCBX
