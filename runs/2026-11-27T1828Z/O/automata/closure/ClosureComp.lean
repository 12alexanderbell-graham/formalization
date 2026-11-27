import Mathlib
import Readings.automata
import ComparatorChallenges.TwoWayComplementation
import Closure.Common

/-! # Target O, family O66: closures against `complementation_lower_bound_finite`

Module `Closure.Comp`. The frozen statement is OpenAI's
`OAI.TwoWayComplementation.complementation_lower_bound_finite` (challenge
`TwoWayComplementation`), taken with `type_of%` at universe zero and never retyped. This challenge
defines the same constant names as `TwoWayDeterminization`, so its closures live in their own
module, with their own copy of the translation between OpenAI's `TwoNFA` and reader A's model
(the same text as in `Closure.Det`, see there).

This frozen statement gives an `n`-state automaton whose complement needs the stated number of
states, but it does not say which language that automaton recognizes. Hence:

* frozen implies the no polynomial complementation consequence of readers A and B
  (`A_p1_thm_nopoly_c`, `B_p1_thm_nopoly_c`): only the existence of the hard automaton is used;
* each reader's theorem implies the frozen statement (`A_p1_thm_to_frozen`, `B_p1_thm_to_frozen`,
  `C_p1_thm_to_frozen`); the converse is not derivable from this statement alone, because the
  reading's conjunct that the automaton recognizes the liveness language has no counterpart here.
  That conjunct is supplied by `explicit_family_main` (module `Closure.Det`), from which every
  paper 1 reading is closed.

State relabelling (`relabel`): the readers B and C give their automaton on an arbitrary state type
with `n` elements, OpenAI's statement wants `Fin n`.
-/

namespace TargetO.Automata.Comp

open Relation TargetO.Automata
open OAI.TwoWayComplementation (TwoNFA tapeSymbol relStar)


variable {α Sg Q Q0 : Type}

/-! ## OpenAI's `TwoNFA` and reader A's model -/

def finDir (m : Fin 3) : ReaderA.Dir :=
  if m.val = 0 then .left else if m.val = 1 then .stay else .right

def dirFin : ReaderA.Dir → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

@[simp] theorem finDir_dirFin (d : ReaderA.Dir) : finDir (dirFin d) = d := by cases d <;> rfl
@[simp] theorem dirFin_finDir (m : Fin 3) : dirFin (finDir m) = m := by fin_cases m <;> rfl

def symO (e : α ≃ Sg) : ReaderA.TapeSym α → Fin 2 ⊕ Sg
  | .lend => .inl 0
  | .rend => .inl 1
  | .sym a => .inr (e a)

def unSym (e : α ≃ Sg) : Fin 2 ⊕ Sg → ReaderA.TapeSym α
  | .inl i => if i.val = 0 then .lend else .rend
  | .inr s => .sym (e.symm s)

@[simp] theorem symO_unSym (e : α ≃ Sg) (x : Fin 2 ⊕ Sg) : symO e (unSym e x) = x := by
  rcases x with i | s
  · fin_cases i <;> rfl
  · simp [symO, unSym]

def toO (e : α ≃ Sg) (M : ReaderA.TwoNFA α Q) : TwoNFA Sg Q where
  initial := M.init
  accepting := M.acc
  transition q x := {p | (p.1, finDir p.2) ∈ M.δ q (unSym e x)}

def ofO (e : α ≃ Sg) (B : TwoNFA Sg Q) : ReaderA.TwoNFA α Q :=
  ⟨B.initial, B.accepting, fun q t => {p | (p.1, dirFin p.2) ∈ B.transition q (symO e t)}⟩

theorem toO_ofO (e : α ≃ Sg) (B : TwoNFA Sg Q) : toO e (ofO e B) = B := by
  obtain ⟨i, a, δ⟩ := B
  simp only [toO, ofO, Set.mem_setOf_eq, dirFin_finDir, symO_unSym]
  rfl

theorem tapeSymbol_eq (e : α ≃ Sg) (u : List α) (p : Fin ((u.map e).length + 2)) :
    unSym e (tapeSymbol (u.map e) p) = ReaderA.TwoNFA.tapeAt u p.val := by
  obtain ⟨i, hi⟩ := p
  simp only [List.length_map] at hi
  cases i with
  | zero => simp [tapeSymbol, unSym, ReaderA.TwoNFA.tapeAt]
  | succ k =>
    simp only [tapeSymbol, ReaderA.TwoNFA.tapeAt, List.length_map]
    by_cases hk : k < u.length
    · rw [dif_neg (by omega), dif_neg (by omega), dif_pos hk]
      simp [unSym]
    · rw [dif_neg (by omega), dif_pos (by omega), dif_neg hk]
      simp [unSym]

theorem step_iff (e : α ≃ Sg) (M : ReaderA.TwoNFA α Q) (u : List α)
    (a a' : Q × Fin ((u.map e).length + 2)) :
    M.Step u (a.1, a.2.val) (a'.1, a'.2.val) ↔ (a, a') ∈ (toO e M).step (u.map e) := by
  have ha' := a'.2.isLt
  simp only [List.length_map] at ha'
  rw [HubA.step_iff]
  simp only [TwoNFA.step, toO, Set.mem_setOf_eq, tapeSymbol_eq]
  constructor
  · rintro ⟨d, hd, hj, hm⟩
    refine ⟨dirFin d, by simpa using hd, ?_⟩
    rcases hm with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [dirFin] <;> omega
  · rintro ⟨m, hm, heq⟩
    refine ⟨finDir m, hm, by omega, ?_⟩
    fin_cases m <;> simp [finDir] at heq ⊢ <;> omega

theorem lang_iff (e : α ≃ Sg) (M : ReaderA.TwoNFA α Q) (u : List α) :
    u ∈ M.lang ↔ u.map e ∈ (toO e M).language := by
  have hn : 0 < (u.map e).length + 2 := by omega
  have h := (sim_fin hn (fun a a' => (a, a') ∈ (toO e M).step (u.map e)) (M.Step u)
    (step_iff e M u) (fun a b h => by
      have := HubA.step_bound M u _ _ h
      simp only [List.length_map]
      omega) M.init (· ∈ M.acc)).1
  show M.Accepts u ↔ _
  refine h.trans ?_
  simp only [TwoNFA.language, relStar, Set.mem_setOf_eq]
  exact ⟨fun ⟨c, hr, hq⟩ => ⟨c, hq, hr⟩, fun ⟨c, hq, hr⟩ => ⟨c, hr, hq⟩⟩

theorem memO (e : α ≃ Sg) (B : TwoNFA Sg Q) (u : List α) :
    u ∈ (ofO e B).lang ↔ u.map e ∈ B.language := by
  rw [lang_iff e, toO_ofO]

theorem surj (e : α ≃ Sg) (w : List Sg) : ∃ u : List α, u.map e = w :=
  ⟨w.map e.symm, by simp [List.map_map]⟩

theorem lang_eq_of (e : α ≃ Sg) {L : Set (List α)} {L' : Set (List Sg)}
    (hL : ∀ u, u ∈ L ↔ u.map e ∈ L') (M : ReaderA.TwoNFA α Q) :
    M.lang = L → (toO e M).language = L' := by
  intro h
  ext w
  obtain ⟨u, rfl⟩ := surj e w
  rw [← lang_iff, h, hL]

theorem compl_transfer (e : α ≃ Sg) (A0 : TwoNFA Sg Q0) (B : ReaderA.TwoNFA α Q)
    (hB : B.lang = (ofO e A0).langᶜ) : (toO e B).language = A0.languageᶜ :=
  lang_eq_of e (fun u => by rw [Set.mem_compl_iff, Set.mem_compl_iff, memO]) B hB

/-! ## State relabelling in reader A's model -/

def relabel {Q' : Type} (σ : Q ≃ Q') (M : ReaderA.TwoNFA α Q) : ReaderA.TwoNFA α Q' :=
  ⟨σ M.init, {q | σ.symm q ∈ M.acc}, fun q t => {p | (σ.symm p.1, p.2) ∈ M.δ (σ.symm q) t}⟩

theorem relabel_lang {Q' : Type} (σ : Q ≃ Q') (M : ReaderA.TwoNFA α Q) :
    (relabel σ M).lang = M.lang := by
  ext w
  let f : Q' × ℕ → Q × ℕ := fun c => (σ.symm c.1, c.2)
  have hs : ∀ a a', (relabel σ M).Step w a a' ↔ M.Step w (f a) (f a') := by
    rintro ⟨q, i⟩ ⟨q', j⟩
    simp only [HubA.step_iff, relabel, Set.mem_setOf_eq, f]
  have h1 : ∀ a a', (relabel σ M).Step w a a' → M.Step w (f a) (f a') := fun a a' h => (hs a a').1 h
  have h2 : ∀ a b, M.Step w (f a) b → ∃ a', f a' = b ∧ (relabel σ M).Step w a a' := by
    intro a b h
    refine ⟨(σ b.1, b.2), by simp [f], (hs _ _).2 ?_⟩
    simpa [f] using h
  have hf : f (σ M.init, 0) = (M.init, 0) := by simp [f]
  show (relabel σ M).Accepts w ↔ M.Accepts w
  constructor
  · rintro ⟨c, hc, hacc⟩
    exact ⟨f c, (rtg_sim f h1 h2 _ _ _ hf).2 ⟨c, rfl, hc⟩, hacc⟩
  · rintro ⟨c, hc, hacc⟩
    obtain ⟨a, rfl, ha⟩ := (rtg_sim f h1 h2 _ _ c hf).1 hc
    exact ⟨a, ha, hacc⟩

/-! ## The alphabets -/

abbrev eA (m : ℕ) : ReaderA.BRel (ReaderA.Icc1 m) ≃ SetRel (Fin m) (Fin m) := relEquiv (iccEquiv m)
abbrev eC (m : ℕ) : Set (Fin m × Fin m) ≃ SetRel (Fin m) (Fin m) := Equiv.refl _

theorem langB (N : ReaderA.TwoNFA α Q) : (HubB.ofA N).Lang = N.lang := by
  rw [(HubB.lang_eq _).1, HubB.toA_ofA]

theorem langC (N : ReaderA.TwoNFA α Q) : (HubC.ofA N).Lang = N.lang := by
  rw [HubC.lang_eq, HubC.toA_ofA]

theorem div_eq (k : ℕ) : (127 * k + 4 - 4) / 127 = k := by omega

/-- The complement transfer in the other direction: a reader automaton built from OpenAI's
complement automaton recognizes the reader's complement. -/
theorem compl_back (e : α ≃ Sg) (A : ReaderA.TwoNFA α Q0) (B : TwoNFA Sg Q)
    (hB : B.language = (toO e A).languageᶜ) : (ofO e B).lang = A.langᶜ := by
  ext u
  rw [memO, hB, Set.mem_compl_iff, Set.mem_compl_iff, ← lang_iff]

/-! ## Frozen implies the no polynomial complementation consequences -/

theorem A_p1_thm_nopoly_c
    (hF : type_of% @OAI.TwoWayComplementation.complementation_lower_bound_finite.{0}) :
    type_of% @ReaderA.reading_paper1_theorem_1_1_no_poly := by
  rintro ⟨p, hp⟩
  obtain ⟨k, hk, hbig⟩ := exists_big_poly p 127 4 (by norm_num)
  obtain ⟨A0, hcomp⟩ := hF (127 * k + 4) (by omega)
  obtain ⟨Q, _, B, hB, hcard⟩ := hp _ inferInstance _ (ofO (eA _) A0)
  have h := hcomp Q (toO (eA _) B) (compl_transfer (eA _) A0 B hB)
  rw [div_eq] at h
  have : (Fintype.card Q : ℝ) ≤ ((p.eval (127 * k + 4) : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith [(pow_pos two_pos k : (0 : ℝ) < 2 ^ k)]

theorem B_p1_thm_nopoly_c
    (hF : type_of% @OAI.TwoWayComplementation.complementation_lower_bound_finite.{0}) :
    type_of% @ReaderB.readingNoPolyComplement := by
  rintro ⟨p, hp⟩
  obtain ⟨k, hk, hbig⟩ := exists_big_poly p 127 4 (by norm_num)
  obtain ⟨A0, hcomp⟩ := hF (127 * k + 4) (by omega)
  obtain ⟨Q, _, B, hB, hcard⟩ := hp _ inferInstance _ inferInstance (HubB.ofA (ofO (eB _) A0))
  have h := hcomp Q (toO (eB _) (HubB.toA B)) (compl_transfer (eB _) A0 _ (by
    rw [← (HubB.lang_eq B).1, hB, langB]
    rfl))
  rw [div_eq] at h
  simp only [Fintype.card_fin] at hcard
  have : (Fintype.card Q : ℝ) ≤ ((p.eval (127 * k + 4) : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith [(pow_pos two_pos k : (0 : ℝ) < 2 ^ k)]

/-! ## Each reading implies the frozen statement -/

theorem A_p1_thm_to_frozen : type_of% @ReaderA.reading_paper1_theorem_1_1 →
    type_of% @OAI.TwoWayComplementation.complementation_lower_bound_finite.{0} := by
  intro hR n hn
  obtain ⟨A, -, hA⟩ := hR n hn
  exact ⟨toO (eA (n - 2)) A, fun Q _ B hB => hA Q (ofO (eA _) B) (compl_back _ A B hB)⟩

theorem B_p1_thm_to_frozen : type_of% @ReaderB.readingComplementation →
    type_of% @OAI.TwoWayComplementation.complementation_lower_bound_finite.{0} := by
  intro hR n hn
  obtain ⟨Q, _, A, hcard, -, hA⟩ := hR n hn
  let σ := Fintype.equivFinOfCardEq hcard
  refine ⟨toO (eB _) (relabel σ (HubB.toA A)), fun Q' _ B hB => hA Q' _ (HubB.ofA (ofO (eB _) B)) ?_⟩
  rw [langB, compl_back _ _ B hB, relabel_lang, ← (HubB.lang_eq A).1]
  rfl

theorem C_p1_thm_to_frozen : type_of% @ReaderC.reading_O66_p1_thm11 →
    type_of% @OAI.TwoWayComplementation.complementation_lower_bound_finite.{0} := by
  intro hR n hn
  obtain ⟨Q, A, hcard, -, hA⟩ := hR n hn
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite Q
  let σ := Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card (α := Q)).symm.trans hcard)
  refine ⟨toO (eC _) (relabel σ (HubC.toA A)), fun Q' _ B hB => ?_⟩
  have := hA Q' inferInstance (HubC.ofA (ofO (eC _) B))
    (by rw [langC, compl_back _ _ B hB, relabel_lang, ← HubC.lang_eq A])
  rwa [Nat.card_eq_fintype_card] at this

end TargetO.Automata.Comp

#print axioms TargetO.Automata.Comp.A_p1_thm_nopoly_c
#print axioms TargetO.Automata.Comp.B_p1_thm_nopoly_c
#print axioms TargetO.Automata.Comp.A_p1_thm_to_frozen
#print axioms TargetO.Automata.Comp.B_p1_thm_to_frozen
#print axioms TargetO.Automata.Comp.C_p1_thm_to_frozen
