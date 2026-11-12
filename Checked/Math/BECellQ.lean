import Checked.Math.GCellQ

/-! Bonnor–Ebert sphere, `BECellQ`: the validated cells of the isothermal solution with the sign of exp w minus half the square of w' as cell invariant (positive, negative or none), checked by kernel evaluation. Promoted from `Work/Math/BECellQ.lean`. -/

namespace Checked.Math.BECellQ
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.GCellQ

/-- E − φ²/2 as a polynomial in σ = t − t0, computed from the cell's Taylor polynomials. -/
def gpoly (c : Cell) : List ℚ := qsub c.pe (qsmul (1 / 2) (qmul c.pp c.pp))

theorem gpoly_eval (c : Cell) (σ : ℝ) :
    evalQ c.pe σ - evalQ c.pp σ ^ 2 / 2 = evalQ (gpoly c) σ := by
  simp only [gpoly, evalQ_qsub, evalQ_qsmul, evalQ_qmul]; push_cast; ring

/-- The invariant of a cell, as a proposition over ℚ. -/
def BInvProp (m : ℕ) (c : Cell) : Prop :=
  match m with
  | 1 => 0 < lo (gpoly c) c.h - c.B * (1 + c.PH)
  | 2 => hi (gpoly c) c.h + c.B * (1 + c.PH) < 0
  | _ => True

instance (m : ℕ) (c : Cell) : Decidable (BInvProp m c) := by
  unfold BInvProp
  split <;> infer_instance

/-- The invariant as a statement about the solution at time t. -/
def BInv (m : ℕ) (E φ : ℝ → ℝ) (t : ℝ) : Prop :=
  match m with
  | 1 => φ t ^ 2 / 2 < E t
  | 2 => E t < φ t ^ 2 / 2
  | _ => True

/-- Cell conditions and invariant, as a Boolean for evaluation by the kernel. -/
def bcellOK (T : ℚ) (m : ℕ) (c : Cell) : Bool := decide (CellProp T c) && decide (BInvProp m c)

theorem bcell_basic {T : ℚ} {m : ℕ} (c : Cell) (hok : bcellOK T m c = true) :
    0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  simp only [bcellOK, Bool.and_eq_true] at hok
  obtain ⟨k1, k2, k3, -⟩ : CellProp T c := of_decide_eq_true hok.1
  exact ⟨k1, k2, k3⟩

/-- The box bound |pp| ≤ PH of a cell. -/
theorem pp_box {T : ℚ} (c : Cell) (hok : decide (CellProp T c) = true) {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ c.h) : |evalQ c.pp σ| ≤ c.PH := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k12, k13, -⟩ : CellProp T c := of_decide_eq_true hok
  have r12 : ((-(c.PH - 1 / 100) : ℚ) : ℝ) ≤ ((lo c.pp c.h : ℚ) : ℝ) := by exact_mod_cast k12
  have r13 : ((hi c.pp c.h : ℚ) : ℝ) ≤ ((c.PH - 1 / 100 : ℚ) : ℝ) := by exact_mod_cast k13
  push_cast at r12 r13
  have a := lo_le c.pp h0 h1
  have b := le_hi c.pp h0 h1
  rw [abs_le]; constructor <;> linarith

/-- What one cell gives: the invariant on the cell, the enclosure on the whole cell, and the end
enclosure. -/
theorem bcell_facts {T : ℚ} {m : ℕ} (c : Cell) (hok : bcellOK T m c = true) {E φ : ℝ → ℝ}
    (hE : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t)
    (h0 : |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), BInv m E φ t) ∧
    |E (c.t0 + c.h) - ((qeval c.pe c.h : ℚ) : ℝ)| ≤ c.B ∧
    |φ (c.t0 + c.h) - ((qeval c.pp c.h : ℚ) : ℝ)| ≤ c.B := by
  have hok' := hok
  simp only [bcellOK, Bool.and_eq_true] at hok'
  have hc := cell_q c hok'.1 hE hφ h0 h0'
  obtain ⟨k1, -, k3⟩ := bcell_basic c hok
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
    have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
    obtain ⟨e1, e2⟩ := hc t ht
    have hB0 : (0 : ℝ) ≤ c.B := (abs_nonneg _).trans e1
    have hpb := pp_box c hok'.1 hσ0 hσ1
    have a1 := abs_le.1 e1
    have a2 := abs_le.1 e2
    have hpb' := abs_le.1 hpb
    -- |φ² − pp²| ≤ B (2 PH): |φ − pp| ≤ B and |φ + pp| ≤ 2|pp| + B ≤ 2 PH (B < 1/100 ≤ PH margin)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k12, k13, -, -, -, k17⟩ : CellProp T c :=
      of_decide_eq_true hok'.1
    have r17 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k17
    have r12 : ((-(c.PH - 1 / 100) : ℚ) : ℝ) ≤ ((lo c.pp c.h : ℚ) : ℝ) := by exact_mod_cast k12
    have r13 : ((hi c.pp c.h : ℚ) : ℝ) ≤ ((c.PH - 1 / 100 : ℚ) : ℝ) := by exact_mod_cast k13
    push_cast at r17 r12 r13
    have lp := lo_le c.pp hσ0 hσ1
    have hp := le_hi c.pp hσ0 hσ1
    set p := evalQ c.pp (t - c.t0) with hpdef
    set q := evalQ c.pe (t - c.t0) with hqdef
    have hsq : |φ t ^ 2 / 2 - p ^ 2 / 2| ≤ (c.B : ℝ) * (c.PH : ℝ) := by
      have e : φ t ^ 2 / 2 - p ^ 2 / 2 = ((φ t - p) * (φ t + p)) / 2 := by ring
      have h2 : |φ t + p| ≤ 2 * (c.PH : ℝ) := by
        rw [abs_le]; constructor <;> linarith
      have h3 : |(φ t - p) * (φ t + p)| ≤ (c.B : ℝ) * (2 * (c.PH : ℝ)) := by
        rw [abs_mul]; exact mul_le_mul e2 h2 (abs_nonneg _) hB0
      rw [e, abs_div, abs_two]
      linarith
    have hsq' := abs_le.1 hsq
    have hg := gpoly_eval c (t - c.t0)
    have kv : BInvProp m c := of_decide_eq_true hok'.2
    rcases m with _ | _ | _ | n
    · trivial
    · have rv : ((0 : ℚ) : ℝ) < ((lo (gpoly c) c.h - c.B * (1 + c.PH) : ℚ) : ℝ) := by
        exact_mod_cast kv
      push_cast at rv
      have hl := lo_le (gpoly c) hσ0 hσ1
      show φ t ^ 2 / 2 < E t
      nlinarith
    · have rv : ((hi (gpoly c) c.h + c.B * (1 + c.PH) : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by
        exact_mod_cast kv
      push_cast at rv
      have hl := le_hi (gpoly c) hσ0 hσ1
      show E t < φ t ^ 2 / 2
      nlinarith
    · trivial
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    rwa [add_sub_cancel_left, ← qeval_cast] at e
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).2
    rwa [add_sub_cancel_left, ← qeval_cast] at e

/-- A chain of cells inside [0, T] with invariant `m`, whose last cell satisfies `term`. -/
def bchainTo (T : ℚ) (m : ℕ) (term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => bcellOK T m c && term c
  | c :: d :: l => bcellOK T m c && linkOK c d && bchainTo T m term (d :: l)

theorem bchain_gen {T : ℚ} {m : ℕ} {term : Cell → Bool} {E φ : ℝ → ℝ} :
    ∀ (l : List Cell) (c : Cell), bchainTo T m term (c :: l) = true →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t) →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t) →
    |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    ∃ e : Cell, term e = true ∧ (c.t0 : ℝ) ≤ e.t0 + e.h ∧
    (∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), BInv m E φ t) ∧
    |E (e.t0 + e.h) - ((qeval e.pe e.h : ℚ) : ℝ)| ≤ e.B ∧
    |φ (e.t0 + e.h) - ((qeval e.pp e.h : ℚ) : ℝ)| ≤ e.B := by
  intro l
  induction l with
  | nil =>
    intro c hok hE hφ h0 h0'
    simp only [bchainTo, Bool.and_eq_true] at hok
    obtain ⟨k1, kt⟩ := hok
    obtain ⟨-, k2, k3⟩ := bcell_basic c k1
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    push_cast at k2'
    have hf := bcell_facts c k1 (E := E) (φ := φ)
      (fun t ht => hE t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hφ t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    exact ⟨c, kt, by linarith, hf⟩
  | cons d l ih =>
    intro c hok hE hφ h0 h0'
    simp only [bchainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    obtain ⟨-, k2, k3⟩ := bcell_basic c k1
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    push_cast at k2'
    have hf := bcell_facts c k1 (E := E) (φ := φ)
      (fun t ht => hE t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hφ t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    rw [he] at hf
    have kE' : |((qeval c.pe c.h : ℚ) : ℝ) - ((d.pe.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kE
    have kφ' : |((qeval c.pp c.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kφ
    obtain ⟨e, het, hce, hinv, hb1, hb2⟩ := ih d krest
      (fun t ht => hE t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hφ t ⟨by linarith [ht.1], ht.2⟩)
      (abs_link hf.2.1 kE') (abs_link hf.2.2 kφ')
    exact ⟨e, het, by linarith, icc_glue hf.1 hinv, hb1, hb2⟩

/-- A segment of a chain: the invariant on it, and the solution enters the input box of `d`. -/
theorem bseg_q {T : ℚ} {m : ℕ} {E φ : ℝ → ℝ} (d : Cell) (l : List Cell) (c : Cell)
    (hok : bchainTo T m (fun e => linkOK e d) (c :: l) = true)
    (hE : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t)
    (h0 : |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (c.t0 : ℝ) ≤ d.t0 ∧ (∀ t ∈ Icc (c.t0 : ℝ) d.t0, BInv m E φ t) ∧
    |E d.t0 - ((d.pe.headD 0 : ℚ) : ℝ)| ≤ d.δ ∧ |φ d.t0 - ((d.pp.headD 0 : ℚ) : ℝ)| ≤ d.δ := by
  obtain ⟨e, het, hce, hinv, hb1, hb2⟩ := bchain_gen l c hok hE hφ h0 h0'
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hce hinv hb1 hb2
  have kE' : |((qeval e.pe e.h : ℚ) : ℝ) - ((d.pe.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kE
  have kφ' : |((qeval e.pp e.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kφ
  exact ⟨hce, hinv, abs_link hb1 kE', abs_link hb2 kφ'⟩

/-- The last segment of a chain: ends at `te`, invariant up to there. -/
theorem bend_q {T te fE fφ r : ℚ} {m : ℕ} {E φ : ℝ → ℝ} (l : List Cell) (c : Cell)
    (hok : bchainTo T m (endOK te fE fφ r) (c :: l) = true)
    (hE : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt E (E t * φ t) (Icc 0 (T : ℝ)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 (T : ℝ)) t)
    (h0 : |E c.t0 - ((c.pe.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (∀ t ∈ Icc (c.t0 : ℝ) te, BInv m E φ t) := by
  obtain ⟨e, het, -, hinv, -, -⟩ := bchain_gen l c hok hE hφ h0 h0'
  obtain ⟨ke, -, -⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (te : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hinv
  exact hinv

end Checked.Math.BECellQ
