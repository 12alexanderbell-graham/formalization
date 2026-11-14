import Checked.FSNeg.LAssemble
import Checked.FSNeg.LCell
import Checked.FSRev.RFlowCells

/-! Falkner–Skan with the adverse pressure-gradient coefficient of minus one tenth, reversed-flow branch: the solution of `LAssemble.core_lower` together with its scaled wall value and the clamped flow it comes from (so that the certified cells of its tube enclose it), and the enclosures that a chain of checked cells gives on each of its cells and on sub-intervals of a cell. The cell-level counterpart of `Checked.FSRev.RFlowCells` for the older cells of `Checked.FSNeg.NCellWC`. Used to classify wall conditions by translates (`Checked/Trust/NecessityAB.lean`). Module `LFlowCells`, run 2026-11-14T0228Z. -/

namespace Checked.FSNeg.LFlowCells
open Set Filter Topology Checked.FSNeg.NBase Checked.FSNeg.NFlow Checked.FSNeg.NAssemble Checked.FSNeg.LCell
  Checked.FalknerSkan.LimitCore Checked.FSNeg.LAssemble Checked.Sim Checked.Sim.QPoly Checked.FSNeg.NCellWC

/-- `LAssemble.core_lower` with the wall value `a` of the clamped flow exposed: the solution is the
rescaled clamped flow from (0, 0, a), lo < a < hi. -/
theorem core_lower_flow {lo hi : ℝ} (hlh : lo < hi) (hO : ChainTo lo Over) (hS : ChainTo hi SlowL)
    (hT : TubeTo lo hi) :
    ∃ a : ℝ, lo < a ∧ a < hi ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => Real.sqrt 10 * (flow a (s / Real.sqrt 10)).1)
        ((fun s => (flow a (s / Real.sqrt 10)).2.1) η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (flow a (s / Real.sqrt 10)).2.1)
        ((fun s => (flow a (s / Real.sqrt 10)).2.2 / Real.sqrt 10) η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (flow a (s / Real.sqrt 10)).2.2 / Real.sqrt 10)
        (-((fun s => Real.sqrt 10 * (flow a (s / Real.sqrt 10)).1) η *
            (fun s => (flow a (s / Real.sqrt 10)).2.2 / Real.sqrt 10) η) -
          (-1 / 10) * (1 - (fun s => (flow a (s / Real.sqrt 10)).2.1) η ^ 2)) (Ici 0) η) ∧
      Tendsto (fun s => (flow a (s / Real.sqrt 10)).2.1) atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 / 2 < (flow a (η / Real.sqrt 10)).2.1 ∧ (flow a (η / Real.sqrt 10)).2.1 < 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - (flow a (η / Real.sqrt 10)).2.1) ≤ (flow a (η / Real.sqrt 10)).2.2 / Real.sqrt 10) := by
  have over_lo : Over (flow lo) := of_chain hO
  have slow_hi : SlowL (flow hi) := of_chain hS
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ Over (flow α)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, over_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun α hα => hα.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hS2⟩ := slowL_open hi slow_hi
  have ha_lt : a < hi := by
    have hub : ∀ α ∈ S, α ≤ hi - δ2 / 2 := by
      intro α hα
      by_contra hc
      push Not at hc
      exact slowL_not_over (hS2 α (by rw [abs_lt]; constructor <;> linarith [hα.1.2])) hα.2
    have := csSup_le hne hub
    linarith
  have hnO : ¬ Over (flow a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open a hOa
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hOa' α' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hα'S
    linarith
  have hnS : ¬ SlowL (flow a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slowL_open a hSa
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact slowL_not_over (hSa' α (by rw [abs_lt]; constructor <;> linarith)) hαS.2
  have hlo_lt : lo < a := by
    rcases eq_or_lt_of_le hloa with h | h
    · exact absurd (by rw [ha, ← h]; exact over_lo) hnO
    · exact h
  obtain ⟨tF, tP, tQ, hlim, hpb, hdec⟩ :=
    neither_classL hT ⟨hloa, ha_lt.le⟩ hnS hnO
  set F := fun t => (flow a t).1
  set P := fun t => (flow a t).2.1
  set Q := fun t => (flow a t).2.2
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  have hc2 : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(10 * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨a, hlo_lt, ha_lt, A, B, fun s hs => ?_, Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => hpb _ (hm hs), fun M => ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have hd := (tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt 10))
    filter_upwards [hd] with s hs
    simp only [id] at hs
    rw [le_div_iff₀ hc]
    linarith

/-- Every cell of a checked chain entered at its first cell's ball: each cell is checked and the
solution enters its ball. -/
theorem chain_box {T : ℚ} {side term : Cell → Bool} :
    ∀ (l : List Cell) (c : Cell), chainS T side term (c :: l) = true →
    ∀ {g p q : ℝ → ℝ}, SolC T 0 g p q → InBox c g p q →
    ∀ d ∈ c :: l, cellOK T d = true ∧ InBox d g p q := by
  intro l
  induction l with
  | nil =>
    intro c hok g p q hs h0 d hd
    simp only [chainS, Bool.and_eq_true] at hok
    simp only [List.mem_singleton] at hd
    subst hd
    exact ⟨hok.1.1, h0⟩
  | cons e l ih =>
    intro c hok g p q hs h0 d hd
    simp only [chainS, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨k1, -⟩, kl⟩, krest⟩ := hok
    have hc0 := (cellOK_basic c k1).1
    have he := cell_w c k1 (hs.mono (by exact_mod_cast hc0)) h0
    obtain ⟨-, hbox⟩ := link_box kl he
    rcases List.mem_cons.1 hd with h | h
    · subst h; exact ⟨k1, h0⟩
    · exact ih e krest hs hbox d h

/-- Rational bounds of the three components on a checked cell entered at its ball. -/
theorem cell_bounds {T : ℚ} (c : Cell) (hok : cellOK T c = true) {g p q : ℝ → ℝ}
    (hs : SolC T 0 g p q) (h0 : InBox c g p q) (t : ℝ) (ht : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h)) :
    ((glo c - c.r1 : ℚ) : ℝ) ≤ g t ∧ g t ≤ ((ghi c + c.r1 : ℚ) : ℝ) ∧
    ((plo c - c.r2 : ℚ) : ℝ) ≤ p t ∧ p t ≤ ((phi c + c.r2 : ℚ) : ℝ) ∧
    ((qlo c - c.B : ℚ) : ℝ) ≤ q t ∧ q t ≤ ((qhi c + c.B : ℚ) : ℝ) := by
  have hc0 := (cellOK_basic c hok).1
  obtain ⟨b1, b2, b3⟩ := encl c hok (hs.mono (by exact_mod_cast hc0)) h0 t ht
  have hσ : t - c.t0 ∈ Icc (0 : ℝ) c.h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have lg := lower_q c.pg (h := c.h) hσ.1 hσ.2
  have ug := upper_q c.pg (h := c.h) hσ.1 hσ.2
  have lp := lower_q c.pp (h := c.h) hσ.1 hσ.2
  have up := upper_q c.pp (h := c.h) hσ.1 hσ.2
  have lq := lower_q c.pq (h := c.h) hσ.1 hσ.2
  have uq := upper_q c.pq (h := c.h) hσ.1 hσ.2
  simp only [glo, ghi, plo, phi, qlo, qhi]
  push_cast at lg ug lp up lq uq ⊢
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The components at a checked cell's start, from its Taylor polynomials' constant terms. -/
theorem cell_start {T : ℚ} (c : Cell) (hok : cellOK T c = true) {g p q : ℝ → ℝ}
    (hs : SolC T 0 g p q) (h0 : InBox c g p q) :
    ((c.pg.headD 0 - c.r1 : ℚ) : ℝ) ≤ g c.t0 ∧ g c.t0 ≤ ((c.pg.headD 0 + c.r1 : ℚ) : ℝ) ∧
    ((c.pp.headD 0 - c.r2 : ℚ) : ℝ) ≤ p c.t0 ∧ p c.t0 ≤ ((c.pp.headD 0 + c.r2 : ℚ) : ℝ) := by
  have hc0 := (cellOK_basic c hok).1
  have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c hok).2.2
  obtain ⟨b1, b2, -⟩ := encl c hok (hs.mono (by exact_mod_cast hc0)) h0 c.t0 ⟨le_rfl, by linarith⟩
  simp only [sub_self, evalQ_zero_head] at b1 b2
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2
  push_cast
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

open Checked.FSRev.RFlowCells in
/-- Rational bounds of the three components on a sub-interval [t₀ + a, t₀ + b] of a checked cell. -/
theorem sub_bounds {T : ℚ} (c : Cell) (hok : cellOK T c = true) {g p q : ℝ → ℝ}
    (hs : SolC T 0 g p q) (h0 : InBox c g p q) (a b : ℚ) (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ c.h)
    (t : ℝ) (ht : t ∈ Icc ((c.t0 : ℝ) + a) ((c.t0 : ℝ) + b)) :
    ((slo c.pg a (b - a) - c.r1 : ℚ) : ℝ) ≤ g t ∧ g t ≤ ((shi c.pg a (b - a) + c.r1 : ℚ) : ℝ) ∧
    ((slo c.pp a (b - a) - c.r2 : ℚ) : ℝ) ≤ p t ∧ p t ≤ ((shi c.pp a (b - a) + c.r2 : ℚ) : ℝ) ∧
    ((slo c.pq a (b - a) - c.B : ℚ) : ℝ) ≤ q t ∧ q t ≤ ((shi c.pq a (b - a) + c.B : ℚ) : ℝ) := by
  have hc0 := (cellOK_basic c hok).1
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ c.h := by exact_mod_cast hb
  have ht' : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨b1, b2, b3⟩ := encl c hok (hs.mono (by exact_mod_cast hc0)) h0 t ht'
  have e : t - c.t0 = (a : ℝ) + (t - c.t0 - a) := by ring
  rw [e, ← evalQ_qshift] at b1
  rw [e, ← evalQ_qshift] at b2
  rw [e, ← evalQ_qshift] at b3
  have hτ0 : (0 : ℝ) ≤ t - c.t0 - a := by linarith [ht.1]
  have hτ1 : t - c.t0 - a ≤ ((b - a : ℚ) : ℝ) := by push_cast; linarith [ht.2]
  have lg := lower_q (qshift c.pg a) hτ0 hτ1
  have ug := upper_q (qshift c.pg a) hτ0 hτ1
  have lp := lower_q (qshift c.pp a) hτ0 hτ1
  have up := upper_q (qshift c.pp a) hτ0 hτ1
  have lq := lower_q (qshift c.pq a) hτ0 hτ1
  have uq := upper_q (qshift c.pq a) hτ0 hτ1
  simp only [slo, shi]
  push_cast at lg ug lp up lq uq ⊢
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2; have a3 := abs_le.1 b3
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The clamped flow solves the clamped field on [0, T]. -/
theorem flow_sol (α T : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (flow α) (vN t (flow α t)) (Icc 0 T) t :=
  fun t ht => (flow_deriv α t ht.1).mono Icc_subset_Ici_self

end Checked.FSNeg.LFlowCells
