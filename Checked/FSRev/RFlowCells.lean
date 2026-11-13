import Checked.FSRev.RAssemble
import Checked.FSRev.RCell
import Checked.FalknerSkan.BoundedTools

/-! Falkner–Skan adverse pressure gradient, reversed-flow branch: the solution of `RAssemble.core_rev` together with its scaled wall value and the clamped flow it comes from (so that the certified cells of a tube enclose it), the enclosures that a chain of checked cells gives on each of its cells, positivity of the shear after any point where it is positive, and translates of a solution on the half-line. Used to classify the wall conditions of the attached-row window headlines (`Checked/Trust/NecessityY.lean`). Module `RFlowCells`, run 2026-11-13T2028Z. -/

namespace Checked.FSRev.RFlowCells
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSAtt.ABase Checked.FSAtt.AFlow
  Checked.FSAtt.AAssemble Checked.FSRev.RBase Checked.FalknerSkan.LimitCore Checked.FSRev.RAssemble
  Checked.Sim Checked.Sim.QPoly Checked.FSSep.SCellWC Checked.FSRev.RCell

/-- `RAssemble.core_rev` with the wall value `a` of the clamped flow exposed: the solution is the
rescaled clamped flow from (0, 0, a), lo < a < hi. -/
theorem core_rev_flow {K : ℝ} (hK5 : 5 ≤ K) {lo hi : ℝ} (hlh : lo < hi) (hO : ChainA K lo Over) (hS : ChainA K hi SlowR)
    (hT : TubeR K lo hi) :
    ∃ a : ℝ, lo < a ∧ a < hi ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => Real.sqrt K * (flowA K a (s / Real.sqrt K)).1)
        ((fun s => (flowA K a (s / Real.sqrt K)).2.1) η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (flowA K a (s / Real.sqrt K)).2.1)
        ((fun s => (flowA K a (s / Real.sqrt K)).2.2 / Real.sqrt K) η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (flowA K a (s / Real.sqrt K)).2.2 / Real.sqrt K)
        (-((fun s => Real.sqrt K * (flowA K a (s / Real.sqrt K)).1) η *
            (fun s => (flowA K a (s / Real.sqrt K)).2.2 / Real.sqrt K) η) -
          (-1 / K) * (1 - (fun s => (flowA K a (s / Real.sqrt K)).2.1) η ^ 2)) (Ici 0) η) ∧
      Tendsto (fun s => (flowA K a (s / Real.sqrt K)).2.1) atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 / 2 < (flowA K a (η / Real.sqrt K)).2.1 ∧ (flowA K a (η / Real.sqrt K)).2.1 < 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - (flowA K a (η / Real.sqrt K)).2.1) ≤ (flowA K a (η / Real.sqrt K)).2.2 / Real.sqrt K) := by
  have over_lo : Over (flowA K lo) := of_chain hO
  have slow_hi : SlowR (flowA K hi) := of_chain hS
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ Over (flowA K α)} with hSd
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, over_lo⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun α hα => hα.1.2⟩
  set a := sSup S with ha
  have hloa := le_csSup hbdd hloS
  obtain ⟨δ2, hδ2, hS2⟩ := slowR_open K hi slow_hi
  have ha_lt : a < hi := by
    have hub : ∀ α ∈ S, α ≤ hi - δ2 / 2 := by
      intro α hα
      by_contra hc
      push Not at hc
      exact slowR_not_over hK5 (hS2 α (by rw [abs_lt]; constructor <;> linarith [hα.1.2])) hα.2
    have := csSup_le hne hub
    linarith
  have hnO : ¬ Over (flowA K a) := by
    intro hOa
    obtain ⟨δ, hδ, hOa'⟩ := over_open K a hOa
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hOa' α' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hα'S
    linarith
  have hnS : ¬ SlowR (flowA K a) := by
    intro hSa
    obtain ⟨δ, hδ, hSa'⟩ := slowR_open K a hSa
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact slowR_not_over hK5 (hSa' α (by rw [abs_lt]; constructor <;> linarith)) hαS.2
  have hlo_lt : lo < a := by
    rcases eq_or_lt_of_le hloa with h | h
    · exact absurd (by rw [ha, ← h]; exact over_lo) hnO
    · exact h
  obtain ⟨tF, tP, tQ, hlim, hpb, hdec⟩ :=
    neither_classR hK5 hT ⟨hloa, ha_lt.le⟩ hnS hnO
  set F := fun t => (flowA K a t).1
  set P := fun t => (flowA K a t).2.1
  set Q := fun t => (flowA K a t).2.2
  have hF0 : F 0 = 0 := by simp [F, flowA_zero]
  have hP0 : P 0 = 0 := by simp [P, flowA_zero]
  have hQ0 : Q 0 = a := by simp [Q, flowA_zero]
  have hc : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  have hc2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
  have tQ' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt Q (-(K * F η * Q η) - (-1) * (1 - P η ^ 2)) (Ici 0) η :=
    fun η hη => (tQ η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hc tF tP tQ'
  have hm := Checked.FalknerSkan.FSScale.mapsTo_div hc
  refine ⟨a, hlo_lt, ha_lt, A, B, fun s hs => ?_, Checked.FalknerSkan.FSScale.scale_lim hc hlim,
    fun s hs => hpb _ (hm hs), fun M => ?_⟩
  · refine (C s hs).congr_deriv ?_
    field_simp
    rw [hc2]
  · have hd := (tendsto_id.atTop_div_const hc).eventually (hdec (M * Real.sqrt K))
    filter_upwards [hd] with s hs
    simp only [id] at hs
    rw [le_div_iff₀ hc]
    linarith


/-- Every cell of a checked chain entered at its first cell's ball: each cell is checked and the
solution enters its ball. -/
theorem chain_box {K T : ℚ} {side term : Cell → Bool} :
    ∀ (l : List Cell) (c : Cell), chainS K T side term (c :: l) = true →
    ∀ {g p q : ℝ → ℝ}, SolC (K : ℝ) T 0 g p q → InBox c g p q →
    ∀ d ∈ c :: l, cellOK K T d = true ∧ InBox d g p q := by
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
theorem cell_bounds {K T : ℚ} (c : Cell) (hok : cellOK K T c = true) {g p q : ℝ → ℝ}
    (hs : SolC (K : ℝ) T 0 g p q) (h0 : InBox c g p q) (t : ℝ) (ht : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h)) :
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
theorem cell_start {K T : ℚ} (c : Cell) (hok : cellOK K T c = true) {g p q : ℝ → ℝ}
    (hs : SolC (K : ℝ) T 0 g p q) (h0 : InBox c g p q) :
    ((c.pg.headD 0 - c.r1 : ℚ) : ℝ) ≤ g c.t0 ∧ g c.t0 ≤ ((c.pg.headD 0 + c.r1 : ℚ) : ℝ) ∧
    ((c.pp.headD 0 - c.r2 : ℚ) : ℝ) ≤ p c.t0 ∧ p c.t0 ≤ ((c.pp.headD 0 + c.r2 : ℚ) : ℝ) := by
  have hc0 := (cellOK_basic c hok).1
  have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c hok).2.2
  obtain ⟨b1, b2, -⟩ := encl c hok (hs.mono (by exact_mod_cast hc0)) h0 c.t0 ⟨le_rfl, by linarith⟩
  simp only [sub_self, evalQ_zero_head] at b1 b2
  have a1 := abs_le.1 b1; have a2 := abs_le.1 b2
  push_cast
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Adverse pressure gradient (β < 0) and −1 < p < 1: once the shear is positive it stays positive. -/
theorem pos_after {β : ℝ} (hβ : β < 0) {f p q : ℝ → ℝ}
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hb : ∀ η ∈ Ici (0 : ℝ), -1 < p η ∧ p η < 1) {s : ℝ} (hs : 0 ≤ s) (hqs : 0 < q s) :
    ∀ η, s ≤ η → 0 < q η := by
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun x => -q x)
      (-(-(f η * q η) - β * (1 - p η ^ 2))) (Ici 0) η := fun η hη => (hq η hη).neg
  have hz : ∀ η ∈ Ici (0 : ℝ), -q η = 0 → -(-(f η * q η) - β * (1 - p η ^ 2)) < 0 := by
    intro η hη h0
    have hq0 : q η = 0 := by linarith
    rw [hq0]
    have h1 := hb η hη
    have : 0 < 1 - p η ^ 2 := by nlinarith
    nlinarith
  have hnn : ∀ η, s ≤ η → 0 ≤ q η := by
    intro η hη
    have := Checked.FalknerSkan.BoundedTools.stays_nonpos hq' hz hs (by linarith) η hη
    linarith
  intro η hη
  rcases eq_or_lt_of_le hη with h | h
  · rw [← h]; exact hqs
  · by_contra hc
    have hq0 : q η = 0 := le_antisymm (not_lt.1 hc) (hnn η hη)
    have hη0 : (0 : ℝ) < η := lt_of_le_of_lt hs h
    have hd : HasDerivAt q (-(f η * q η) - β * (1 - p η ^ 2)) η :=
      (hq η hη0.le).hasDerivAt (Ici_mem_nhds hη0)
    have hmin : IsLocalMin q η := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      rw [hq0]; exact hnn x (le_of_lt hx)
    have h0 := hmin.hasDerivAt_eq_zero hd
    rw [hq0] at h0
    have h1 := hb η hη0.le
    have : 0 < 1 - p η ^ 2 := by nlinarith
    nlinarith

/-- A translate of a function with right derivatives on the half-line. -/
theorem shift_deriv {u u' : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt u (u' η) (Ici 0) η) :
    ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun x => u (x + s)) (u' (η + s)) (Ici 0) η := by
  intro η hη
  have hη' : η + s ∈ Ici (0 : ℝ) := add_nonneg hη hs
  have h1 := (h (η + s) hη').comp η ((hasDerivWithinAt_id η (Ici (0 : ℝ))).add_const s)
    (fun x hx => (add_nonneg (mem_Ici.1 hx) hs : (0 : ℝ) ≤ x + s))
  rw [mul_one] at h1
  exact h1

theorem shift_lim {p : ℝ → ℝ} (s : ℝ) (h : Tendsto p atTop (𝓝 1)) :
    Tendsto (fun x => p (x + s)) atTop (𝓝 1) :=
  h.comp (tendsto_atTop_add_const_right atTop s tendsto_id)

theorem shift_dec {p q : ℝ → ℝ} (s : ℝ) (h : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p (η + s)) ≤ q (η + s) := fun M =>
  (tendsto_atTop_add_const_right atTop s tendsto_id).eventually (h M)

/-- The clamped flow solves the clamped field on [0, T]. -/
theorem flow_sol (K α T : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (flowA K α) (vS K t (flowA K α t)) (Icc 0 T) t :=
  fun t ht => (flowA_deriv K α t ht.1).mono Icc_subset_Ici_self

/-- A zero of a continuous function between a negative and a positive value. -/
theorem cross {u : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn u (Icc a b)) (ha : u a < 0)
    (hb : 0 < u b) : ∃ s ∈ Icc a b, u s = 0 :=
  intermediate_value_Icc hab hc ⟨ha.le, hb.le⟩

end Checked.FSRev.RFlowCells
