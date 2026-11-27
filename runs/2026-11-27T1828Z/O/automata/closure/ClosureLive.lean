import Mathlib
import Readings.automata
import ComparatorChallenges.OneWayLiveness
import Closure.Common

/-! # Target O, family O66: closures of the paper 2 readings against `main_theorem`

Module `Closure.Live`. The frozen statement is OpenAI's `OAI.OneWayLiveness.main_theorem`
(challenge `OneWayLiveness`), taken with `type_of%` and never retyped; every closure has the form
`frozen → reading`.

Model translation (paper 2). OpenAI's machines have states `Fin n`, configurations
(head position in `Fin (|w| + 2)`, state), moves `Move`, a deterministic machine has an
`Option`-valued transition, a nondeterministic one a set-valued transition, and both carry
the side conditions that no transition on the left endmarker moves left and none on the right
endmarker moves right; `FiniteRun positive` is reachability with (`false`) or without (`true`)
the empty run. Reader A's model (the hub of `Closure.Common`) is translated into OpenAI's
nondeterministic machine along a bijection of the states with `Fin n` (`toN`), dropping the
transitions that cross an endmarker (they can never fire), and OpenAI's machine back into reader
A's model (`fromN`, with `toN (fromN N) = N`). A deterministic reader automaton becomes OpenAI's
deterministic machine `toD` (choose the unique allowed successor), with the same steps as `toN`.
Acceptance agrees under both conventions (`accepts_iff`).

Alphabets: each reader's relations are in bijection with OpenAI's `BRel (Fin h)`, carrying the
reader's liveness language onto OpenAI's `OWL h` (products in path order on both sides).

Closed here (frozen implies reading), for each reader: the theorem (the `h + 3`-state automaton
without left moves, and the lower bounds for deterministic automata with `s + 2` under each
convention and `s + 1` under the convention counting an accepting initial configuration), and the
corollary (no bound `C n^c` for determinization), from the frozen bound with `h = 62 k + 2`.
-/

namespace TargetO.Automata.Live

open Relation TargetO.Automata
open OAI.OneWayLiveness (Symbol Move scanned NMachine DMachine FiniteRun OWL Alphabet)

noncomputable section

variable {α Sg Q : Type} {n : ℕ}

/-! ## OpenAI's machines and reader A's model -/

def mvDir : Move → ReaderA.Dir
  | .left => .left
  | .stay => .stay
  | .right => .right

def dirMv : ReaderA.Dir → Move
  | .left => .left
  | .stay => .stay
  | .right => .right

@[simp] theorem mvDir_dirMv (d : ReaderA.Dir) : mvDir (dirMv d) = d := by cases d <;> rfl
@[simp] theorem dirMv_mvDir (m : Move) : dirMv (mvDir m) = m := by cases m <;> rfl

def symL (e : α ≃ Sg) : ReaderA.TapeSym α → Symbol Sg
  | .lend => .left
  | .rend => .right
  | .sym a => .letter (e a)

def unSymL (e : α ≃ Sg) : Symbol Sg → ReaderA.TapeSym α
  | .left => .lend
  | .right => .rend
  | .letter s => .sym (e.symm s)

@[simp] theorem symL_unSymL (e : α ≃ Sg) (x : Symbol Sg) : symL e (unSymL e x) = x := by
  cases x <;> simp [symL, unSymL]

/-- A move is allowed on a symbol unless it crosses that endmarker. -/
abbrev legal (x : Symbol Sg) (m : Move) : Prop :=
  ¬(x = .left ∧ m = .left) ∧ ¬(x = .right ∧ m = .right)

def toN (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) : NMachine Sg n where
  initial := σ M.init
  accepting := {i | σ.symm i ∈ M.acc}
  transition i x := {p | (σ.symm p.1, mvDir p.2) ∈ M.δ (σ.symm i) (unSymL e x) ∧ legal x p.2}
  left_boundary _ _ h := h.2.1 ⟨rfl, rfl⟩
  right_boundary _ _ h := h.2.2 ⟨rfl, rfl⟩

def fromN (e : α ≃ Sg) (N : NMachine Sg n) : ReaderA.TwoNFA α (Fin n) :=
  ⟨N.initial, N.accepting, fun q t => {p | (p.1, dirMv p.2) ∈ N.transition q (symL e t)}⟩

theorem legal_of (N : NMachine Sg n) {i : Fin n} {x : Symbol Sg} {q' : Fin n} {m : Move}
    (h : (q', m) ∈ N.transition i x) : legal x m := by
  refine ⟨?_, ?_⟩
  · rintro ⟨rfl, rfl⟩
    exact N.left_boundary i q' h
  · rintro ⟨rfl, rfl⟩
    exact N.right_boundary i q' h

theorem nm_ext {N1 N2 : NMachine Sg n} (h1 : N1.initial = N2.initial)
    (h2 : N1.accepting = N2.accepting) (h3 : N1.transition = N2.transition) : N1 = N2 := by
  cases N1
  cases N2
  cases h1
  cases h2
  cases h3
  rfl

theorem toN_fromN (e : α ≃ Sg) (N : NMachine Sg n) : toN e (Equiv.refl _) (fromN e N) = N := by
  refine nm_ext rfl rfl ?_
  funext q x
  ext ⟨q', m⟩
  simp only [toN, fromN, Equiv.refl_symm, Equiv.refl_apply, Set.mem_setOf_eq, dirMv_mvDir,
    symL_unSymL]
  exact ⟨And.left, fun h => ⟨h, legal_of N h⟩⟩

theorem scanned_eq (e : α ≃ Sg) (u : List α) (p : Fin ((u.map e).length + 2)) :
    unSymL e (scanned (u.map e) p) = ReaderA.TwoNFA.tapeAt u p.val := by
  obtain ⟨i, hi⟩ := p
  simp only [List.length_map] at hi
  cases i with
  | zero => simp [scanned, unSymL, ReaderA.TwoNFA.tapeAt]
  | succ k =>
    simp only [scanned, ReaderA.TwoNFA.tapeAt, List.length_map]
    by_cases hk : k < u.length
    · rw [dif_neg (by omega), dif_pos (by omega), dif_pos hk]
      simp [unSymL]
    · rw [dif_neg (by omega), dif_neg (by omega), dif_neg hk]
      rfl

theorem scanned_left (w : List Sg) (p : Fin (w.length + 2)) (h : scanned w p = .left) :
    p.val = 0 := by
  unfold scanned at h
  split_ifs at h with h0 hi
  exact h0

theorem scanned_right (w : List Sg) (p : Fin (w.length + 2)) (h : scanned w p = .right) :
    p.val = w.length + 1 := by
  have := p.isLt
  unfold scanned at h
  split_ifs at h with h0 hi
  omega

theorem step_iff (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) (u : List α)
    (c c' : OAI.OneWayLiveness.Configuration (u.map e) n) :
    (toN e σ M).Step (u.map e) c c' ↔ M.Step u (σ.symm c.2, c.1.val) (σ.symm c'.2, c'.1.val) := by
  have hc := c.1.isLt
  have hc' := c'.1.isLt
  simp only [List.length_map] at hc hc'
  rw [HubA.step_iff]
  constructor
  · rintro ⟨d, ⟨hd, -⟩, hrel⟩
    refine ⟨mvDir d, by rwa [scanned_eq] at hd, by omega, ?_⟩
    cases d <;> simp [mvDir, OAI.OneWayLiveness.Move.Rel] at hrel ⊢ <;> omega
  · rintro ⟨dd, hdd, hj, hm⟩
    have hmem : (σ.symm c'.2, mvDir (dirMv dd)) ∈ M.δ (σ.symm c.2) (unSymL e (scanned (u.map e) c.1)) := by
      rw [scanned_eq, mvDir_dirMv]
      exact hdd
    rcases hm with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · refine ⟨.left, And.intro hmem (And.intro (fun hx => ?_) (fun hx => by cases hx.2)), ?_⟩
      · have := scanned_left _ _ hx.1
        omega
      · simp only [OAI.OneWayLiveness.Move.Rel]
        omega
    · refine ⟨.stay, And.intro hmem (And.intro (fun hx => by cases hx.2) (fun hx => by cases hx.2)), ?_⟩
      simp only [OAI.OneWayLiveness.Move.Rel]
      omega
    · refine ⟨.right, And.intro hmem (And.intro (fun hx => by cases hx.2) (fun hx => ?_)), ?_⟩
      · have := scanned_right _ _ hx.1
        simp only [List.length_map] at this
        omega
      · simp only [OAI.OneWayLiveness.Move.Rel]
        omega

theorem accepts_iff (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) (u : List α) :
    (M.Accepts u ↔ (toN e σ M).Accepts false (u.map e)) ∧
    (M.AcceptsPos u ↔ (toN e σ M).Accepts true (u.map e)) := by
  let f : OAI.OneWayLiveness.Configuration (u.map e) n → Q × ℕ := fun c => (σ.symm c.2, c.1.val)
  have h1 : ∀ a a', (toN e σ M).Step (u.map e) a a' → M.Step u (f a) (f a') :=
    fun a a' h => (step_iff e σ M u a a').1 h
  have h2 : ∀ a b, M.Step u (f a) b → ∃ a', f a' = b ∧ (toN e σ M).Step (u.map e) a a' := by
    intro a b h
    have hb := HubA.step_bound M u _ _ h
    refine ⟨(⟨b.2, by simp only [List.length_map]; omega⟩, σ b.1), by simp [f], ?_⟩
    rw [step_iff]
    simpa using h
  have hf : f (⟨0, by omega⟩, σ M.init) = (M.init, 0) := by simp [f]
  constructor
  · simp only [ReaderA.TwoNFA.Accepts, OAI.OneWayLiveness.NMachine.Accepts,
      OAI.OneWayLiveness.FiniteRun, Bool.false_eq_true, if_false]
    constructor
    · rintro ⟨c, hc, hacc⟩
      obtain ⟨a, rfl, ha⟩ := (rtg_sim f h1 h2 _ _ c hf).1 hc
      exact ⟨a, ha, hacc⟩
    · rintro ⟨a, ha, hacc⟩
      exact ⟨f a, (rtg_sim f h1 h2 _ _ _ hf).2 ⟨a, rfl, ha⟩, hacc⟩
  · simp only [ReaderA.TwoNFA.AcceptsPos, OAI.OneWayLiveness.NMachine.Accepts,
      OAI.OneWayLiveness.FiniteRun, if_true]
    constructor
    · rintro ⟨c, hc, hacc⟩
      obtain ⟨a, rfl, ha⟩ := (tg_sim f h1 h2 _ _ c hf).1 hc
      exact ⟨a, ha, hacc⟩
    · rintro ⟨a, ha, hacc⟩
      exact ⟨f a, (tg_sim f h1 h2 _ _ _ hf).2 ⟨a, rfl, ha⟩, hacc⟩

theorem surj (e : α ≃ Sg) (w : List Sg) : ∃ u : List α, u.map e = w :=
  ⟨w.map e.symm, by simp [List.map_map]⟩

theorem recog_of (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) {L : Set (List α)}
    {L' : Set (List Sg)} (hL : ∀ u, u ∈ L ↔ u.map e ∈ L') :
    (M.lang = L → (toN e σ M).Recognizes false L') ∧
    (M.langPos = L → (toN e σ M).Recognizes true L') := by
  constructor
  · intro hM w
    obtain ⟨u, rfl⟩ := surj e w
    rw [← (accepts_iff e σ M u).1, ← hL, ← hM]
    rfl
  · intro hM w
    obtain ⟨u, rfl⟩ := surj e w
    rw [← (accepts_iff e σ M u).2, ← hL, ← hM]
    rfl

theorem lang_fromN (e : α ≃ Sg) (N : NMachine Sg n) {L : Set (List α)} {L' : Set (List Sg)}
    (hL : ∀ u, u ∈ L ↔ u.map e ∈ L') (hN : N.Recognizes false L') : (fromN e N).lang = L := by
  ext u
  show (fromN e N).Accepts u ↔ _
  rw [(accepts_iff e (Equiv.refl _) (fromN e N) u).1, toN_fromN, hN, hL]

theorem noLeft_fromN (e : α ≃ Sg) (N : NMachine Sg n) (h : N.NoLeft) : (fromN e N).NoLeft :=
  fun q a q' hq => h q (symL e a) q' hq

/-! ## Deterministic machines -/

open Classical in
def toD (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) : DMachine Sg n where
  initial := σ M.init
  accepting := {i | σ.symm i ∈ M.acc}
  transition i x := if h : ((toN e σ M).transition i x).Nonempty then some h.some else none
  left_boundary q q' h := by
    split_ifs at h with hne
    · have hm := hne.some_mem
      rw [Option.some_inj.1 h] at hm
      exact (toN e σ M).left_boundary q q' hm
  right_boundary q q' h := by
    split_ifs at h with hne
    · have hm := hne.some_mem
      rw [Option.some_inj.1 h] at hm
      exact (toN e σ M).right_boundary q q' hm

theorem toN_sub (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) (hdet : M.IsDet)
    (i : Fin n) (x : Symbol Sg) : ((toN e σ M).transition i x).Subsingleton := by
  rintro ⟨q1, m1⟩ ⟨h1, -⟩ ⟨q2, m2⟩ ⟨h2, -⟩
  have := hdet _ _ h1 h2
  simp only [Prod.mk.injEq] at this
  exact Prod.ext (σ.symm.injective this.1) (by simpa using congrArg dirMv this.2)

theorem toD_trans (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) (hdet : M.IsDet)
    (i : Fin n) (x : Symbol Sg) (p : Fin n × Move) :
    (toD e σ M).transition i x = some p ↔ p ∈ (toN e σ M).transition i x := by
  simp only [toD]
  split_ifs with hne
  · constructor
    · intro h
      rw [← Option.some_inj.1 h]
      exact hne.some_mem
    · intro hp
      exact congrArg some (toN_sub e σ M hdet i x hne.some_mem hp)
  · simp only [false_iff]
    exact fun hp => hne ⟨p, hp⟩

theorem toD_accepts (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) (hdet : M.IsDet)
    (positive : Bool) (w : List Sg) :
    (toD e σ M).Accepts positive w ↔ (toN e σ M).Accepts positive w := by
  have hs : (toD e σ M).Step w = (toN e σ M).Step w := by
    funext c c'
    apply propext
    exact exists_congr fun d => and_congr_left' (toD_trans e σ M hdet _ _ _)
  simp only [OAI.OneWayLiveness.DMachine.Accepts, OAI.OneWayLiveness.NMachine.Accepts, hs]
  rfl

theorem recogD (e : α ≃ Sg) (σ : Q ≃ Fin n) (M : ReaderA.TwoNFA α Q) (hdet : M.IsDet)
    {L : Set (List α)} {L' : Set (List Sg)} (hL : ∀ u, u ∈ L ↔ u.map e ∈ L') :
    (M.lang = L → (toD e σ M).Recognizes false L') ∧
    (M.langPos = L → (toD e σ M).Recognizes true L') := by
  constructor
  · intro hM w
    rw [toD_accepts e σ M hdet]
    exact (recog_of e σ M hL).1 hM w
  · intro hM w
    rw [toD_accepts e σ M hdet]
    exact (recog_of e σ M hL).2 hM w

/-! ## The alphabets -/

def toS (H : Type) : OAI.OneWayLiveness.BRel H ≃ SetRel H H where
  toFun b := {p | b.holds p.1 p.2}
  invFun S := ⟨fun a b => (a, b) ∈ S⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem toS_prod {H : Type} (w : List (OAI.OneWayLiveness.BRel H)) :
    toS H w.prod = rp (w.map (toS H)) := by
  induction w with
  | nil =>
    ext ⟨a, b⟩
    rfl
  | cons R w ih =>
    rw [List.prod_cons, List.map_cons, rp_cons, ← ih]
    ext ⟨a, c⟩
    rfl

theorem owl_iff (h : ℕ) (w : List (Alphabet h)) : w ∈ OWL h ↔ (rp (w.map (toS (Fin h)))).Nonempty := by
  rw [← toS_prod]
  exact ⟨fun ⟨a, b, hab⟩ => ⟨(a, b), hab⟩, fun ⟨p, hp⟩ => ⟨p.1, p.2, hp⟩⟩

theorem bridge {h : ℕ} (eX : α ≃ SetRel (Fin h) (Fin h)) {L : Set (List α)}
    (hL : ∀ u, u ∈ L ↔ (rp (u.map eX)).Nonempty) (u : List α) :
    u ∈ L ↔ u.map (eX.trans (toS (Fin h)).symm) ∈ OWL h := by
  rw [owl_iff, List.map_map, hL]
  have : (⇑(toS (Fin h)) ∘ ⇑(eX.trans (toS (Fin h)).symm)) = eX := by
    funext x
    simp
  rw [this]

abbrev eOA (h : ℕ) : ReaderA.BRel (ReaderA.Icc1 h) ≃ Alphabet h :=
  (relEquiv (iccEquiv h)).trans (toS (Fin h)).symm
abbrev eOB (h : ℕ) : ReaderB.Rel' (Fin h) ≃ Alphabet h := (eB (Fin h)).trans (toS (Fin h)).symm
abbrev eOC (h : ℕ) : Set (Fin h × Fin h) ≃ Alphabet h :=
  (Equiv.refl (SetRel (Fin h) (Fin h))).trans (toS (Fin h)).symm

theorem hLA (h : ℕ) (u : List (ReaderA.BRel (ReaderA.Icc1 h))) :
    u ∈ ReaderA.OWL h ↔ u.map (eOA h) ∈ OWL h :=
  bridge _ (memA_iff (iccEquiv h)) u

theorem hLB (h : ℕ) (u : List (ReaderB.Rel' (Fin h))) :
    u ∈ ReaderB.livenessLang (Fin h) ↔ u.map (eOB h) ∈ OWL h :=
  bridge _ memB_iff u

theorem hLC (h : ℕ) (u : List (Set (Fin h × Fin h))) :
    u ∈ ReaderC.relLive (Fin h) ↔ u.map (eOC h) ∈ OWL h :=
  bridge _ (fun u => by rw [memC_iff]; simp) u

/-! ## Arithmetic -/

theorem sq_bound {k s : ℕ} (h : 2 ^ (2 * k) ≤ 4 * (s + 1) ^ 2) : (2 : ℝ) ^ k ≤ 2 * (s + 1) := by
  have h' : (2 ^ k) ^ 2 ≤ (2 * (s + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm k 2, mul_pow]
    norm_num
    exact h
  have := (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h'
  exact_mod_cast this

theorem le_succ_bound {a s : ℕ} (h : a ≤ 4 * (s + 1) ^ 2) : a ≤ 4 * (s + 2) ^ 2 :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))

/-! ## Reader A -/

theorem A_p2_thm (hF : type_of% @OAI.OneWayLiveness.main_theorem) :
    type_of% @ReaderA.reading_paper2_theorem_1_1 := by
  intro h hh
  obtain ⟨⟨N, hNL, hNR⟩, hD⟩ := hF h hh
  have b1 : ∀ (Q : Type) [Fintype Q] (D : ReaderA.TwoNFA (ReaderA.BRel (ReaderA.Icc1 h)) Q),
      D.IsDet → D.lang = ReaderA.OWL h → 2 ^ ((h - 2) / 31) ≤ 4 * (Fintype.card Q + 1) ^ 2 := by
    intro Q _ D hdet hDL
    simpa using hD false _ (toD (eOA h) (Fintype.equivFin Q) D)
      ((recogD _ _ D hdet (hLA h)).1 hDL)
  refine ⟨⟨fromN (eOA h) N, noLeft_fromN _ N hNL, lang_fromN _ N (hLA h) (hNR false)⟩,
    fun Q _ D hdet hDL => le_succ_bound (b1 Q D hdet hDL), fun Q _ D hdet hDL => ?_, b1⟩
  simpa using hD true _ (toD (eOA h) (Fintype.equivFin Q) D) ((recogD _ _ D hdet (hLA h)).2 hDL)

theorem A_p2_cor (hF : type_of% @OAI.OneWayLiveness.main_theorem) :
    type_of% @ReaderA.reading_paper2_corollary := by
  rintro ⟨C, c, hC, hc, H⟩
  obtain ⟨k, hk, hbig⟩ := exists_big C c 62 5 (by norm_num)
  obtain ⟨⟨N, -, hNR⟩, hD⟩ := hF (62 * k + 2) (by omega)
  have hM := lang_fromN (eOA _) N (hLA _) (hNR false)
  obtain ⟨Q, _, D, hdet, hDM, hcard⟩ :=
    H _ inferInstance (62 * k + 5) (fromN (eOA (62 * k + 2)) N)
  have hb := hD false _ (toD (eOA _) (Fintype.equivFin Q) D)
    ((recogD _ _ D hdet (hLA _)).1 (hDM.trans hM))
  have hk2 : (62 * k + 2 - 2) / 31 = 2 * k := by omega
  simp only [hk2, Bool.false_eq_true, if_false] at hb
  have h2 := sq_bound hb
  rw [abs_of_pos hC] at hbig
  linarith

/-! ## Reader B -/

theorem langB (N : ReaderA.TwoNFA α Q) : (HubB.ofA N).Lang = N.lang := by
  rw [(HubB.lang_eq _).1, HubB.toA_ofA]

theorem B_p2_thm (hF : type_of% @OAI.OneWayLiveness.main_theorem) :
    type_of% @ReaderB.readingLiveness := by
  intro h hh
  obtain ⟨⟨N, hNL, hNR⟩, hD⟩ := hF h hh
  have b1 : ∀ (Q : Type) (_ : Fintype Q) (D : ReaderB.TwoWay (ReaderB.Rel' (Fin h)) Q),
      D.IsDet → D.Lang = ReaderB.livenessLang (Fin h) →
        2 ^ ((h - 2) / 31) ≤ 4 * (Fintype.card Q + 1) ^ 2 := by
    intro Q _ D hdet hDL
    rw [(HubB.lang_eq D).1] at hDL
    simpa using hD false _ (toD (eOB h) (Fintype.equivFin Q) (HubB.toA D))
      ((recogD _ _ _ ((HubB.isDet_iff D).1 hdet) (hLB h)).1 hDL)
  refine ⟨⟨Fin (h + 3), inferInstance, HubB.ofA (fromN (eOB h) N), by simp,
    (HubB.noLeft_iff _).2 (by rw [HubB.toA_ofA]; exact noLeft_fromN _ N hNL),
    by rw [langB]; exact lang_fromN _ N (hLB h) (hNR false)⟩, ?_, b1⟩
  rintro Q _ D hdet (hDL | hDL)
  · exact le_succ_bound (b1 Q _ D hdet hDL)
  · rw [(HubB.lang_eq D).2] at hDL
    simpa using hD true _ (toD (eOB h) (Fintype.equivFin Q) (HubB.toA D))
      ((recogD _ _ _ ((HubB.isDet_iff D).1 hdet) (hLB h)).2 hDL)

theorem B_p2_cor (hF : type_of% @OAI.OneWayLiveness.main_theorem) :
    type_of% @ReaderB.readingNoPolynomialSimulation := by
  rintro ⟨C, c, hC, hc, H⟩
  obtain ⟨k, hk, hbig⟩ := exists_big C c 62 5 (by norm_num)
  obtain ⟨⟨N, -, hNR⟩, hD⟩ := hF (62 * k + 2) (by omega)
  have hM : (HubB.ofA (fromN (eOB (62 * k + 2)) N)).Lang = ReaderB.livenessLang _ := by
    rw [langB]
    exact lang_fromN (eOB _) N (hLB _) (hNR false)
  obtain ⟨Q, _, D, hdet, hDM, hcard⟩ :=
    H _ inferInstance (Fin (62 * k + 5)) inferInstance (HubB.ofA (fromN (eOB (62 * k + 2)) N))
  have hDL := hDM.trans hM
  rw [(HubB.lang_eq D).1] at hDL
  have hb := hD false _ (toD (eOB _) (Fintype.equivFin Q) (HubB.toA D))
    ((recogD _ _ _ ((HubB.isDet_iff D).1 hdet) (hLB _)).1 hDL)
  have hk2 : (62 * k + 2 - 2) / 31 = 2 * k := by omega
  simp only [hk2, Bool.false_eq_true, if_false] at hb
  have h2 := sq_bound hb
  rw [abs_of_pos hC] at hbig
  simp only [Fintype.card_fin] at hcard
  linarith

/-! ## Reader C -/

theorem langC (N : ReaderA.TwoNFA α Q) : (HubC.ofA N).Lang = N.lang := by
  rw [HubC.lang_eq, HubC.toA_ofA]

theorem C_p2_thm (hF : type_of% @OAI.OneWayLiveness.main_theorem) :
    type_of% @ReaderC.reading_O66_p2_thm11 := by
  intro h hh
  obtain ⟨⟨N, hNL, hNR⟩, hD⟩ := hF h hh
  have b1 : ∀ (Q : Type) [Finite Q] (D : ReaderC.TWA Q (Set (Fin h × Fin h))),
      D.Det → D.Lang = ReaderC.relLive (Fin h) → 2 ^ ((h - 2) / 31) ≤ 4 * (Nat.card Q + 1) ^ 2 := by
    intro Q _ D hdet hDL
    have := Fintype.ofFinite Q
    rw [HubC.lang_eq D] at hDL
    rw [Nat.card_eq_fintype_card]
    simpa using hD false _ (toD (eOC h) (Fintype.equivFin Q) (HubC.toA D))
      ((recogD _ _ _ ((HubC.det_iff D).1 hdet) (hLC h)).1 hDL)
  refine ⟨⟨Fin (h + 3), HubC.ofA (fromN (eOC h) N), by simp,
    (HubC.noLeft_iff _).2 (by rw [HubC.toA_ofA]; exact noLeft_fromN _ N hNL),
    by rw [langC]; exact lang_fromN _ N (hLC h) (hNR false)⟩,
    fun Q _ D hdet hDL => le_succ_bound (b1 Q D hdet hDL), b1⟩

theorem C_p2_cor (hF : type_of% @OAI.OneWayLiveness.main_theorem) :
    type_of% @ReaderC.reading_O66_p2_cor := by
  rintro ⟨C, c, hC, hc, H⟩
  obtain ⟨k, hk, hbig⟩ := exists_big C c 62 5 (by norm_num)
  obtain ⟨⟨N, -, hNR⟩, hD⟩ := hF (62 * k + 2) (by omega)
  have hM : (HubC.ofA (fromN (eOC (62 * k + 2)) N)).Lang = ReaderC.relLive _ := by
    rw [langC]
    exact lang_fromN (eOC _) N (hLC _) (hNR false)
  obtain ⟨Q, D, hQ, hdet, hDM, hcard⟩ :=
    H _ (62 * k + 5) (Fin (62 * k + 5)) (HubC.ofA (fromN (eOC (62 * k + 2)) N)) (by simp)
  have := Fintype.ofFinite Q
  have hDL := hDM.trans hM
  rw [HubC.lang_eq D] at hDL
  have hb := hD false _ (toD (eOC _) (Fintype.equivFin Q) (HubC.toA D))
    ((recogD _ _ _ ((HubC.det_iff D).1 hdet) (hLC _)).1 hDL)
  have hk2 : (62 * k + 2 - 2) / 31 = 2 * k := by omega
  simp only [hk2, Bool.false_eq_true, if_false] at hb
  have h2 := sq_bound hb
  rw [abs_of_pos hC] at hbig
  rw [Nat.card_eq_fintype_card] at hcard
  linarith

end

end TargetO.Automata.Live

#print axioms TargetO.Automata.Live.A_p2_thm
#print axioms TargetO.Automata.Live.A_p2_cor
#print axioms TargetO.Automata.Live.B_p2_thm
#print axioms TargetO.Automata.Live.B_p2_cor
#print axioms TargetO.Automata.Live.C_p2_thm
#print axioms TargetO.Automata.Live.C_p2_cor
