import Checked.Math.BEHCell

/-! Gelfand problem, `GLamCell`: chains of the validated homology cells of `Checked.Math.BEHCell` with new
invariants for the turning points of the branch parameter λ = u v: the sign of v − 2 (λ decreases where
v exceeds two, increases where v is below two), the sign of u − 1 (v increases where u exceeds one), and a
band for u on every cell of the chain. The cell check `CellProp`, the links and the end condition are those of
`Checked.Math.BEHCell`; only the invariant is new. -/

namespace Work.Math.GLamCell
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.BEHCell
open Checked.Math.GCellQ (lo hi lo_le le_hi abs_link icc_glue)

/-- Invariant data: a kind (1: v > 2, 2: v < 2, 3: u > 1, 4: u < 1, otherwise none) and a band for u. -/
structure VI where
  k : ℕ
  ua : ℚ
  ub : ℚ

/-- The kind part of the invariant, checked on a cell's polynomials over ℚ. -/
def kProp (k : ℕ) (c : Cell) : Prop :=
  match k with
  | 1 => 2 + c.B < lo c.pv c.h
  | 2 => hi c.pv c.h + c.B < 2
  | 3 => 1 + c.B < lo c.pu c.h
  | 4 => hi c.pu c.h + c.B < 1
  | _ => True

instance (k : ℕ) (c : Cell) : Decidable (kProp k c) := by
  unfold kProp; split <;> infer_instance

/-- The invariant checked on a cell. -/
def VProp (m : VI) (c : Cell) : Prop :=
  kProp m.k c ∧ m.ua + c.B ≤ lo c.pu c.h ∧ hi c.pu c.h + c.B ≤ m.ub

instance (m : VI) (c : Cell) : Decidable (VProp m c) := by
  unfold VProp; infer_instance

/-- The kind part of the invariant for the solution at radius t. -/
def kInv (k : ℕ) (u v : ℝ → ℝ) (t : ℝ) : Prop :=
  match k with
  | 1 => 2 < v t
  | 2 => v t < 2
  | 3 => 1 < u t
  | 4 => u t < 1
  | _ => True

/-- The invariant for the solution at radius t. -/
def VInv (m : VI) (u v : ℝ → ℝ) (t : ℝ) : Prop :=
  kInv m.k u v t ∧ (m.ua : ℝ) ≤ u t ∧ u t ≤ m.ub

/-- Cell conditions and invariant, as a Boolean for evaluation by the kernel. -/
def vcellOK (L T : ℚ) (m : VI) (c : Cell) : Bool := decide (CellProp L T c) && decide (VProp m c)

theorem vcell_basic {L T : ℚ} {m : VI} (c : Cell) (hok : vcellOK L T m c = true) :
    L ≤ c.t0 ∧ 0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  simp only [vcellOK, Bool.and_eq_true] at hok
  obtain ⟨k0, k1, k2, k3, -⟩ : CellProp L T c := of_decide_eq_true hok.1
  exact ⟨k0, k1, k2, k3⟩

/-- What one cell gives: the invariant on the cell and the end enclosure. -/
theorem vcell_facts {L T : ℚ} {m : VI} (c : Cell) (hok : vcellOK L T m c = true) {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), VInv m u v t) ∧
    |u (c.t0 + c.h) - ((qeval c.pu c.h : ℚ) : ℝ)| ≤ c.B ∧
    |v (c.t0 + c.h) - ((qeval c.pv c.h : ℚ) : ℝ)| ≤ c.B := by
  have hok' := hok
  simp only [vcellOK, Bool.and_eq_true] at hok'
  have hc := cell_q c hok'.1 hu hv h0 h0'
  obtain ⟨-, -, -, k3⟩ := vcell_basic c hok
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
    have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
    obtain ⟨e1, e2⟩ := hc t ht
    have a1 := abs_le.1 e1
    have a2 := abs_le.1 e2
    have lu := lo_le c.pu hσ0 hσ1
    have hu' := le_hi c.pu hσ0 hσ1
    have lv := lo_le c.pv hσ0 hσ1
    have hv' := le_hi c.pv hσ0 hσ1
    obtain ⟨kk, ka, kb⟩ : VProp m c := of_decide_eq_true hok'.2
    have ra : ((m.ua + c.B : ℚ) : ℝ) ≤ ((lo c.pu c.h : ℚ) : ℝ) := by exact_mod_cast ka
    have rb : ((hi c.pu c.h + c.B : ℚ) : ℝ) ≤ ((m.ub : ℚ) : ℝ) := by exact_mod_cast kb
    push_cast at ra rb
    refine ⟨?_, by linarith, by linarith⟩
    unfold kInv
    unfold kProp at kk
    split
    · rename_i h; rw [h] at kk
      have r : ((2 + c.B : ℚ) : ℝ) < ((lo c.pv c.h : ℚ) : ℝ) := by exact_mod_cast kk
      push_cast at r; linarith
    · rename_i h; rw [h] at kk
      have r : ((hi c.pv c.h + c.B : ℚ) : ℝ) < ((2 : ℚ) : ℝ) := by exact_mod_cast kk
      push_cast at r; linarith
    · rename_i h; rw [h] at kk
      have r : ((1 + c.B : ℚ) : ℝ) < ((lo c.pu c.h : ℚ) : ℝ) := by exact_mod_cast kk
      push_cast at r; linarith
    · rename_i h; rw [h] at kk
      have r : ((hi c.pu c.h + c.B : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by exact_mod_cast kk
      push_cast at r; linarith
    · trivial
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    rwa [add_sub_cancel_left, ← qeval_cast] at e
  · have e := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).2
    rwa [add_sub_cancel_left, ← qeval_cast] at e

/-- A chain of cells inside [L, T] with invariant `m`, whose last cell satisfies `term`. -/
def vchainTo (L T : ℚ) (m : VI) (term : Cell → Bool) : List Cell → Bool
  | [] => false
  | [c] => vcellOK L T m c && term c
  | c :: d :: l => vcellOK L T m c && Checked.Math.BEHCell.linkOK c d && vchainTo L T m term (d :: l)

theorem vchain_gen {L T : ℚ} {m : VI} {term : Cell → Bool} {u v : ℝ → ℝ} :
    ∀ (l : List Cell) (c : Cell), vchainTo L T m term (c :: l) = true →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t) →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t) →
    |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    ∃ e : Cell, term e = true ∧ (c.t0 : ℝ) ≤ e.t0 + e.h ∧
    (∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), VInv m u v t) ∧
    |u (e.t0 + e.h) - ((qeval e.pu e.h : ℚ) : ℝ)| ≤ e.B ∧
    |v (e.t0 + e.h) - ((qeval e.pv e.h : ℚ) : ℝ)| ≤ e.B := by
  intro l
  induction l with
  | nil =>
    intro c hok hu hv h0 h0'
    simp only [vchainTo, Bool.and_eq_true] at hok
    obtain ⟨k1, kt⟩ := hok
    obtain ⟨-, -, k2, k3⟩ := vcell_basic c k1
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    push_cast at k2'
    have hf := vcell_facts c k1 (u := u) (v := v)
      (fun t ht => hu t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hv t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    exact ⟨c, kt, by linarith, hf⟩
  | cons d l ih =>
    intro c hok hu hv h0 h0'
    simp only [vchainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    obtain ⟨-, -, k2, k3⟩ := vcell_basic c k1
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    push_cast at k2'
    have hf := vcell_facts c k1 (u := u) (v := v)
      (fun t ht => hu t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hv t ⟨ht.1, by linarith [ht.2]⟩) h0 h0'
    rw [he] at hf
    have kE' : |((qeval c.pu c.h : ℚ) : ℝ) - ((d.pu.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kE
    have kφ' : |((qeval c.pv c.h : ℚ) : ℝ) - ((d.pv.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kφ
    obtain ⟨e, het, hce, hinv, hb1, hb2⟩ := ih d krest
      (fun t ht => hu t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hv t ⟨by linarith [ht.1], ht.2⟩)
      (abs_link hf.2.1 kE') (abs_link hf.2.2 kφ')
    exact ⟨e, het, by linarith, icc_glue hf.1 hinv, hb1, hb2⟩

/-- A segment of a chain: the invariant up to the start of `d`, and the solution enters the input
box of `d`. -/
theorem vseg_q {L T : ℚ} {m : VI} {u v : ℝ → ℝ} (d : Cell) (l : List Cell) (c : Cell)
    (hok : vchainTo L T m (fun e => Checked.Math.BEHCell.linkOK e d) (c :: l) = true)
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (c.t0 : ℝ) ≤ d.t0 ∧ (∀ t ∈ Icc (c.t0 : ℝ) d.t0, VInv m u v t) ∧
    |u d.t0 - ((d.pu.headD 0 : ℚ) : ℝ)| ≤ d.δ ∧ |v d.t0 - ((d.pv.headD 0 : ℚ) : ℝ)| ≤ d.δ := by
  obtain ⟨e, het, hce, hinv, hb1, hb2⟩ := vchain_gen l c hok hu hv h0 h0'
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hce hinv hb1 hb2
  have kE' : |((qeval e.pu e.h : ℚ) : ℝ) - ((d.pu.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kE
  have kφ' : |((qeval e.pv e.h : ℚ) : ℝ) - ((d.pv.headD 0 : ℚ) : ℝ)| + e.B ≤ d.δ := by
    exact_mod_cast kφ
  exact ⟨hce, hinv, abs_link hb1 kE', abs_link hb2 kφ'⟩

/-- The last segment of a chain: the invariant up to `te`, and the solution is within `r` of
(fu, fv) at `te`. -/
theorem vend_q {L T te fu fv r : ℚ} {m : VI} {u v : ℝ → ℝ} (l : List Cell) (c : Cell)
    (hok : vchainTo L T m (endOK te fu fv r) (c :: l) = true)
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : |u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    (∀ t ∈ Icc (c.t0 : ℝ) te, VInv m u v t) ∧ |u te - fu| ≤ r ∧ |v te - fv| ≤ r := by
  obtain ⟨e, het, -, hinv, hb1, hb2⟩ := vchain_gen l c hok hu hv h0 h0'
  obtain ⟨ke, kE, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (te : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hinv hb1 hb2
  have kE' : |((qeval e.pu e.h : ℚ) : ℝ) - fu| + e.B ≤ r := by exact_mod_cast kE
  have kφ' : |((qeval e.pv e.h : ℚ) : ℝ) - fv| + e.B ≤ r := by exact_mod_cast kφ
  exact ⟨hinv, abs_link hb1 kE', abs_link hb2 kφ'⟩

end Work.Math.GLamCell
