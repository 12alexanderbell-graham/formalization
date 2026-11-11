import Checked.FSSep.SCellWC
import Checked.FSRev.RBase

/-! Falkner–Skan adverse pressure gradient with a free scaled coefficient: checked weighted cells of the clamped field and the segment lemmas used by the reversed-flow chains. Module `RCell`, promoted from `Work/FSRev/RCell.lean`. -/

namespace Checked.FSRev.RCell
open Set Checked.Sim Checked.Sim.QPoly Checked.FSSep.SCellWC Checked.FSNeg.NBase Checked.FSRev.RBase

/-- Enclosure of the three components on a checked cell. -/
theorem encl {K T : ℚ} (c : Cell) (hok : cellOK K T c = true) {g p q : ℝ → ℝ}
    (hs : SolC (K : ℝ) T c.t0 g p q) (h0 : InBox c g p q) (t : ℝ) (ht : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h)) :
    |g t - evalQ c.pg (t - c.t0)| ≤ c.r1 ∧ |p t - evalQ c.pp (t - c.t0)| ≤ c.r2 ∧
      |q t - evalQ c.pq (t - c.t0)| ≤ c.B := by
  obtain ⟨-, -, -, kw1, kw2, -, -, -, -, -, kr1, kBr, kr2, kBr2, -⟩ : CellProp K T c :=
    of_decide_eq_true hok
  have hw1 : (0 : ℝ) < c.w1 := by exact_mod_cast kw1
  have hw2 : (0 : ℝ) < c.w2 := by exact_mod_cast kw2
  have hr1 : (0 : ℝ) ≤ c.r1 := by exact_mod_cast kr1
  have hr2 : (0 : ℝ) ≤ c.r2 := by exact_mod_cast kr2
  have hBr : (c.B : ℝ) ^ 2 ≤ c.w1 * (c.r1 : ℝ) ^ 2 := by exact_mod_cast kBr
  have hBr2 : (c.B : ℝ) ^ 2 ≤ c.w2 * (c.r2 : ℝ) ^ 2 := by exact_mod_cast kBr2
  have hB0 : (0 : ℝ) ≤ c.B := (cell_pos c hok).2.2.1.le
  have e := cell_all c hok hs h0 t ht
  unfold V at e
  have n1 := mul_nonneg hw1.le (sq_nonneg (g t - evalQ c.pg (t - c.t0)))
  have n2 := mul_nonneg hw2.le (sq_nonneg (p t - evalQ c.pp (t - c.t0)))
  have n3 := sq_nonneg (q t - evalQ c.pq (t - c.t0))
  exact ⟨comp_le hw1 hr1 (by linarith) hBr, comp_le hw2 hr2 (by linarith) hBr2,
    comp_le (w := 1) (B := (c.B : ℝ)) one_pos hB0 (by linarith) (by linarith)⟩

/-- On a checked cell the enclosed solution lies inside the clamps of `vN`. -/
theorem cell_box {K T : ℚ} (c : Cell) (hok : cellOK K T c = true) {g p q : ℝ → ℝ}
    (hs : SolC (K : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), |g t| ≤ t + 2 ∧ |p t| ≤ 2 ∧ |q t| ≤ 2 := by
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
  refine ⟨abs_le.2 ⟨by linarith [ht.1], by linarith [ht.1]⟩, abs_le.2 ⟨by linarith, by linarith⟩,
    abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- Side condition p > −1/2 on the cell. -/
def sideP (c : Cell) : Bool := decide (-1 / 2 < plo c - c.r2)

theorem sideP_spec {K T : ℚ} (c : Cell) (hok : cellOK K T c = true) (hside : sideP c = true)
    {g p q : ℝ → ℝ} (hs : SolC (K : ℝ) T c.t0 g p q) (h0 : InBox c g p q) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), PhiT g p q t := by
  intro t ht
  refine ⟨cell_box c hok hs h0 t ht, ?_⟩
  obtain ⟨-, b2, -⟩ := encl c hok hs h0 t ht
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have lp := lower_q c.pp (h := c.h) hσ.1 hσ.2
  have k : ((-1 / 2 : ℚ) : ℝ) < ((plo c - c.r2 : ℚ) : ℝ) := by exact_mod_cast (of_decide_eq_true hside)
  simp only [plo] at k
  push_cast at k lp
  linarith [(abs_le.1 b2).1]

/-- End of a tube chain: the last cell ends at `T` with 0 < g < 1, 0 < p < 1, 0 < q < 6/5. -/
def endT (T : ℚ) (c : Cell) : Bool :=
  decide (c.t0 + c.h = T ∧ 0 < qeval c.pg c.h - c.r1 ∧ qeval c.pg c.h + c.r1 < 1 ∧
    0 < qeval c.pp c.h - c.r2 ∧ qeval c.pp c.h + c.r2 < 1 ∧
    0 < qeval c.pq c.h - c.B ∧ qeval c.pq c.h + c.B < 6 / 5)

/-- End of the lower Slow chain: the last cell ends at `T` with 1/3 < p, 0 < q < 3(1 − p),
g > 11/15. -/
def endSR (T : ℚ) (c : Cell) : Bool :=
  decide (c.t0 + c.h = T ∧ 1 / 3 < qeval c.pp c.h - c.r2 ∧ 0 < qeval c.pq c.h - c.B ∧
    qeval c.pq c.h + c.B < 3 * (1 - (qeval c.pp c.h + c.r2)) ∧ 11 / 15 < qeval c.pg c.h - c.r1)

/-- The enclosure at the end of a chain ending at `T`. -/
theorem end_encl {K T : ℚ} {side term : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOK K T c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolC (K : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (hterm : ∀ e, term e = true → e.t0 + e.h = T)
    (l : List Cell) (c : Cell) (hok : chainS K T side term (c :: l) = true) {g p q : ℝ → ℝ}
    (hs : SolC (K : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    ∃ e : Cell, term e = true ∧
      |g T - ((qeval e.pg e.h : ℚ) : ℝ)| ≤ e.r1 ∧ |p T - ((qeval e.pp e.h : ℚ) : ℝ)| ≤ e.r2 ∧
      |q T - ((qeval e.pq e.h : ℚ) : ℝ)| ≤ e.B ∧ ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  have k := (cellOK_basic c (chainS_head c l hok)).1
  obtain ⟨e, hke, he, hend, hΦ⟩ := chainS_gen hside l c hok (hs.mono (by exact_mod_cast k)) h0
  obtain ⟨-, -, -, kw1, kw2, -, -, -, -, -, kr1, kBr, kr2, kBr2, -⟩ : CellProp K T e :=
    of_decide_eq_true hke
  obtain ⟨hw1, hw2, hB, hr2, hBr2⟩ := cell_pos e hke
  have hr1 : (0 : ℝ) ≤ e.r1 := by exact_mod_cast kr1
  have hBr : (e.B : ℝ) ^ 2 ≤ e.w1 * (e.r1 : ℝ) ^ 2 := by exact_mod_cast kBr
  have hT : ((e.t0 + e.h : ℚ) : ℝ) = (T : ℝ) := by exact_mod_cast (hterm e he)
  push_cast at hT
  unfold AtEnd V at hend
  rw [hT] at hend hΦ
  have n1 := mul_nonneg hw1.le (sq_nonneg (g T - ((qeval e.pg e.h : ℚ) : ℝ)))
  have n2 := mul_nonneg hw2.le (sq_nonneg (p T - ((qeval e.pp e.h : ℚ) : ℝ)))
  have n3 := sq_nonneg (q T - ((qeval e.pq e.h : ℚ) : ℝ))
  exact ⟨e, he, comp_le hw1 hr1 (by linarith) hBr, comp_le hw2 hr2 (by linarith) hBr2,
    comp_le (w := 1) (B := (e.B : ℝ)) one_pos hB.le (by linarith) (by linarith), hΦ⟩

theorem endT_q0 {K T : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOK K T c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolC (K : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (l : List Cell) (c : Cell) (hok : chainS K T side (endT T) (c :: l) = true)
    {g p q : ℝ → ℝ} (hs : SolC (K : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    (0 < g T ∧ g T < 1 ∧ 0 < p T ∧ p T < 1 ∧ 0 < q T ∧ q T < 6 / 5) ∧
      ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  obtain ⟨e, he, b1, b2, b3, hΦ⟩ := end_encl hside
    (fun e he => (of_decide_eq_true he).1) l c hok hs h0
  obtain ⟨-, k1, k2, k3, k4, k5, k6⟩ := of_decide_eq_true he
  have k1' : (0 : ℝ) < ((qeval e.pg e.h - e.r1 : ℚ) : ℝ) := by exact_mod_cast k1
  have k2' : ((qeval e.pg e.h + e.r1 : ℚ) : ℝ) < 1 := by exact_mod_cast k2
  have k3' : (0 : ℝ) < ((qeval e.pp e.h - e.r2 : ℚ) : ℝ) := by exact_mod_cast k3
  have k4' : ((qeval e.pp e.h + e.r2 : ℚ) : ℝ) < 1 := by exact_mod_cast k4
  have k5' : (0 : ℝ) < ((qeval e.pq e.h - e.B : ℚ) : ℝ) := by exact_mod_cast k5
  have k6' : ((qeval e.pq e.h + e.B : ℚ) : ℝ) < ((6 / 5 : ℚ) : ℝ) := by exact_mod_cast k6
  push_cast at k1' k2' k3' k4' k5' k6'
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  exact ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩, hΦ⟩

theorem endSR_q0 {K T : ℚ} {side : Cell → Bool} {Φ : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → Prop}
    (hside : ∀ c, cellOK K T c = true → side c = true → ∀ {g p q : ℝ → ℝ}, SolC (K : ℝ) T c.t0 g p q →
      InBox c g p q → ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), Φ g p q t)
    (l : List Cell) (c : Cell) (hok : chainS K T side (endSR T) (c :: l) = true)
    {g p q : ℝ → ℝ} (hs : SolC (K : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    (1 / 3 < p T ∧ 0 < q T ∧ q T < 3 * (1 - p T) ∧ 11 / 15 < g T) ∧
      ∀ t ∈ Icc (c.t0 : ℝ) T, Φ g p q t := by
  obtain ⟨e, he, b1, b2, b3, hΦ⟩ := end_encl hside
    (fun e he => (of_decide_eq_true he).1) l c hok hs h0
  obtain ⟨-, k1, k2, k3, k4⟩ := of_decide_eq_true he
  have k1' : ((1 / 3 : ℚ) : ℝ) < ((qeval e.pp e.h - e.r2 : ℚ) : ℝ) := by exact_mod_cast k1
  have k2' : (0 : ℝ) < ((qeval e.pq e.h - e.B : ℚ) : ℝ) := by exact_mod_cast k2
  have k3' : ((qeval e.pq e.h + e.B : ℚ) : ℝ) < ((3 * (1 - (qeval e.pp e.h + e.r2)) : ℚ) : ℝ) := by
    exact_mod_cast k3
  have k4' : ((11 / 15 : ℚ) : ℝ) < ((qeval e.pg e.h - e.r1 : ℚ) : ℝ) := by exact_mod_cast k4
  push_cast at k1' k2' k3' k4'
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  exact ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, hΦ⟩

end Checked.FSRev.RCell
