import Mathlib
import Readings.automata
import ComparatorChallenges.TwoWayDeterminization
import Closure.Common

/-! # Target O, family O66: closures of the paper 1 readings against `explicit_family_main`

Module `Closure.Det`. The frozen statement is OpenAI's
`OAI.TwoWayComplementation.explicit_family_main` (challenge `TwoWayDeterminization`), taken
with `type_of%` at universe zero and never retyped; every closure has the form
`frozen → reading`.

Model translation (paper 1). OpenAI's `TwoNFA` (endmarkers `Sum.inl 0`, `Sum.inl 1`, move codes
in `Fin 3`, head positions in `Fin (|w| + 2)`, acceptance by reaching an accepting state with the
empty run allowed) and reader A's `TwoNFA` (head positions in `ℕ`, moves past the endmarkers
unavailable) are translated both ways with the same state type, so state counts are equal:
`toO e M` and `ofO e B`, along a bijection `e` of the alphabets. A word `u` is accepted by `M`
iff `u.map e` is accepted by `toO e M` (`lang_iff`); determinism is preserved (`det_of`).
Readers B and C go through reader A's model (`Closure.Common`).

Alphabets: reader A's relations on `{1, …, n-2}` (a subtype of `ℕ`), reader B's
`Fin (n-2) → Fin (n-2) → Prop`, and reader C's `Set (Fin (n-2) × Fin (n-2))` are each in
bijection with OpenAI's `SetRel (Fin (n-2)) (Fin (n-2))`, and the bijection carries each reader's
liveness language onto OpenAI's `sourceLanguage`.

Closed here (frozen implies reading), for each reader: the theorem (the `n`-state automaton for
the liveness language whose complement needs the stated number of states), its no polynomial
complementation consequence, the determinization corollary (constants one half and `131`), and its
no polynomial determinization consequence (reader C has the corollary and its consequence in one
theorem).
-/

namespace TargetO.Automata.Det

open Relation TargetO.Automata
open OAI.TwoWayComplementation (TwoNFA tapeSymbol relStar sourceLanguage relationProduct)

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

theorem det_of (e : α ≃ Sg) (M : ReaderA.TwoNFA α Q) (h : M.IsDet) :
    (toO e M).Deterministic := by
  intro q x p1 hp1 p2 hp2
  have := h q (unSym e x) hp1 hp2
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.1 (by simpa using congrArg dirFin this.2)

/-! ## The alphabets -/

abbrev eA (m : ℕ) : ReaderA.BRel (ReaderA.Icc1 m) ≃ SetRel (Fin m) (Fin m) := relEquiv (iccEquiv m)
abbrev eC (m : ℕ) : Set (Fin m × Fin m) ≃ SetRel (Fin m) (Fin m) := Equiv.refl _

theorem hLA (m : ℕ) (u : List (ReaderA.BRel (ReaderA.Icc1 m))) :
    u ∈ ReaderA.LH (ReaderA.Icc1 m) ↔ u.map (eA m) ∈ sourceLanguage (Fin m) :=
  memA_iff (iccEquiv m) u

theorem hLB (m : ℕ) (u : List (ReaderB.Rel' (Fin m))) :
    u ∈ ReaderB.livenessLang (Fin m) ↔ u.map (eB (Fin m)) ∈ sourceLanguage (Fin m) :=
  memB_iff u

theorem hLC (m : ℕ) (u : List (Set (Fin m × Fin m))) :
    u ∈ ReaderC.relLive (Fin m) ↔ u.map (eC m) ∈ sourceLanguage (Fin m) := by
  have : u.map (eC m) = u := by simp
  rw [this]
  exact memC_iff u

theorem langB (N : ReaderA.TwoNFA α Q) : (HubB.ofA N).Lang = N.lang := by
  rw [(HubB.lang_eq _).1, HubB.toA_ofA]

theorem langC (N : ReaderA.TwoNFA α Q) : (HubC.ofA N).Lang = N.lang := by
  rw [HubC.lang_eq, HubC.toA_ofA]

/-- The arithmetic of the no polynomial bound consequences. -/
theorem div_eq (k : ℕ) : (127 * k + 4 - 4) / 127 = k := by omega

/-! ## Reader A -/

theorem A_p1_thm (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderA.reading_paper1_theorem_1_1 := by
  intro n hn
  obtain ⟨A0, hA0, hcomp, -⟩ := hF n hn
  refine ⟨ofO (eA (n - 2)) A0, ?_, fun Q _ B hB => hcomp Q (toO (eA _) B) (compl_transfer (eA _) A0 B hB)⟩
  ext u
  rw [memO, hA0]
  exact (hLA _ u).symm

theorem A_p1_thm_nopoly (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderA.reading_paper1_theorem_1_1_no_poly := by
  rintro ⟨p, hp⟩
  obtain ⟨k, hk, hbig⟩ := exists_big_poly p 127 4 (by norm_num)
  obtain ⟨A0, -, hcomp, -⟩ := hF (127 * k + 4) (by omega)
  obtain ⟨Q, _, B, hB, hcard⟩ := hp _ inferInstance _ (ofO (eA _) A0)
  have h := hcomp Q (toO (eA _) B) (compl_transfer (eA _) A0 B hB)
  rw [div_eq] at h
  have : (Fintype.card Q : ℝ) ≤ ((p.eval (127 * k + 4) : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith [(pow_pos two_pos k : (0 : ℝ) < 2 ^ k)]

theorem A_p1_cor (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderA.reading_paper1_corollary := by
  refine ⟨1 / 2, by norm_num, 131, by norm_num, fun n hn Q _ D hdet hD => ?_⟩
  obtain ⟨A0, hA0, -, hdet0⟩ := hF n (by omega)
  exact hdet0 hn Q (toO (eA (n - 2)) D) (det_of (eA _) D hdet)
    (by rw [hA0]; exact lang_eq_of (eA _) (hLA _) D hD)

theorem A_p1_cor_nopoly (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderA.reading_paper1_corollary_no_poly := by
  rintro ⟨p, hp⟩
  obtain ⟨k, hk, hbig⟩ := exists_big_poly p 127 4 (by norm_num)
  obtain ⟨A0, -, -, hdet0⟩ := hF (127 * k + 4) (by omega)
  obtain ⟨Q, _, D, hdet, hD, hcard⟩ := hp _ inferInstance _ (ofO (eA _) A0)
  have h := hdet0 (by omega) Q (toO (eA _) D) (det_of (eA _) D hdet) (lang_eq_of (eA _) (memO (eA _) A0) D hD)
  rw [div_eq] at h
  have : (Fintype.card Q : ℝ) ≤ ((p.eval (127 * k + 4) : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith [(pow_pos two_pos k : (0 : ℝ) < 2 ^ k)]

/-! ## Reader B -/

theorem B_p1_thm (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderB.readingComplementation := by
  intro n hn
  obtain ⟨A0, hA0, hcomp, -⟩ := hF n hn
  refine ⟨Fin n, inferInstance, HubB.ofA (ofO (eB _) A0), by simp, ?_, fun Q _ B hB => ?_⟩
  · ext u
    rw [langB, memO, hA0]
    exact (hLB _ u).symm
  · refine hcomp Q (toO (eB _) (HubB.toA B)) (compl_transfer (eB _) A0 _ ?_)
    rw [← (HubB.lang_eq B).1, hB, langB]
    rfl

theorem B_p1_thm_nopoly (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderB.readingNoPolyComplement := by
  rintro ⟨p, hp⟩
  obtain ⟨k, hk, hbig⟩ := exists_big_poly p 127 4 (by norm_num)
  obtain ⟨A0, -, hcomp, -⟩ := hF (127 * k + 4) (by omega)
  obtain ⟨Q, _, B, hB, hcard⟩ := hp _ inferInstance _ inferInstance (HubB.ofA (ofO (eB _) A0))
  have h := hcomp Q (toO (eB _) (HubB.toA B)) (compl_transfer (eB _) A0 _ (by
    rw [← (HubB.lang_eq B).1, hB, langB]
    rfl))
  rw [div_eq] at h
  simp only [Fintype.card_fin] at hcard
  have : (Fintype.card Q : ℝ) ≤ ((p.eval (127 * k + 4) : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith [(pow_pos two_pos k : (0 : ℝ) < 2 ^ k)]

theorem B_p1_cor (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderB.readingDeterminization := by
  refine ⟨1 / 2, by norm_num, 131, by norm_num, fun n hn => ?_⟩
  obtain ⟨A0, hA0, -, hdet0⟩ := hF n (by omega)
  refine ⟨Fin n, inferInstance, HubB.ofA (ofO (eB _) A0), by simp, ?_, fun Q _ D hdet hD => ?_⟩
  · ext u
    rw [langB, memO, hA0]
    exact (hLB _ u).symm
  · refine hdet0 hn Q (toO (eB _) (HubB.toA D)) (det_of (eB _) _ ((HubB.isDet_iff D).1 hdet))
      (lang_eq_of (eB _) (memO (eB _) A0) _ ?_)
    rw [← (HubB.lang_eq D).1, hD, langB]

theorem B_p1_cor_nopoly (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderB.readingNoPolyDeterminize := by
  rintro ⟨p, hp⟩
  obtain ⟨k, hk, hbig⟩ := exists_big_poly p 127 4 (by norm_num)
  obtain ⟨A0, -, -, hdet0⟩ := hF (127 * k + 4) (by omega)
  obtain ⟨Q, _, D, hdet, hD, hcard⟩ := hp _ inferInstance _ inferInstance (HubB.ofA (ofO (eB _) A0))
  have h := hdet0 (by omega) Q (toO (eB _) (HubB.toA D)) (det_of (eB _) _ ((HubB.isDet_iff D).1 hdet))
    (lang_eq_of (eB _) (memO (eB _) A0) _ (by rw [← (HubB.lang_eq D).1, hD, langB]))
  rw [div_eq] at h
  simp only [Fintype.card_fin] at hcard
  have : (Fintype.card Q : ℝ) ≤ ((p.eval (127 * k + 4) : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith [(pow_pos two_pos k : (0 : ℝ) < 2 ^ k)]

/-! ## Reader C -/

theorem C_p1_thm (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderC.reading_O66_p1_thm11 := by
  intro n hn
  obtain ⟨A0, hA0, hcomp, -⟩ := hF n hn
  refine ⟨Fin n, HubC.ofA (ofO (eC _) A0), by simp, ?_, fun Q hQ B hB => ?_⟩
  · ext u
    rw [langC, memO, hA0]
    exact (hLC _ u).symm
  · have := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card]
    refine hcomp Q (toO (eC _) (HubC.toA B)) (compl_transfer (eC _) A0 _ ?_)
    rw [← HubC.lang_eq B, hB, langC]

theorem C_p1_cor (hF : type_of% @OAI.TwoWayComplementation.explicit_family_main.{0, 0}) :
    type_of% @ReaderC.reading_O66_p1_cor := by
  refine ⟨⟨1 / 2, by norm_num, 131, by norm_num, fun n hn Q _ D hdet hD => ?_⟩, ?_⟩
  · have := Fintype.ofFinite Q
    obtain ⟨A0, hA0, -, hdet0⟩ := hF n (by omega)
    rw [Nat.card_eq_fintype_card]
    exact hdet0 hn Q (toO (eC (n - 2)) (HubC.toA D)) (det_of (eC _) _ ((HubC.det_iff D).1 hdet))
      (by rw [hA0]; exact lang_eq_of (eC _) (hLC _) _ (by rw [← HubC.lang_eq D, hD]))
  · rintro ⟨C, d, H⟩
    obtain ⟨k, hk, hbig⟩ := exists_big C d 127 4 (by norm_num)
    obtain ⟨A0, -, -, hdet0⟩ := hF (127 * k + 4) (by omega)
    obtain ⟨Q, D, hQ, hdet, hD, hcard⟩ := H _ (Fin (127 * k + 4)) (HubC.ofA (ofO (eC _) A0))
    have := Fintype.ofFinite Q
    have h := hdet0 (by omega) Q (toO (eC _) (HubC.toA D)) (det_of (eC _) _ ((HubC.det_iff D).1 hdet))
      (lang_eq_of (eC _) (memO (eC _) A0) _ (by rw [← HubC.lang_eq D, hD, langC]))
    rw [div_eq] at h
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    have h1 : C * ((127 * k + 4 : ℕ) : ℝ) ^ d ≤ |C| * ((127 * k + 4 : ℕ) : ℝ) ^ (d : ℝ) := by
      rw [Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    push_cast at hcard h1 hbig
    linarith [(pow_pos two_pos k : (0 : ℝ) < 2 ^ k)]

end TargetO.Automata.Det

#print axioms TargetO.Automata.Det.A_p1_thm
#print axioms TargetO.Automata.Det.A_p1_thm_nopoly
#print axioms TargetO.Automata.Det.A_p1_cor
#print axioms TargetO.Automata.Det.A_p1_cor_nopoly
#print axioms TargetO.Automata.Det.B_p1_thm
#print axioms TargetO.Automata.Det.B_p1_thm_nopoly
#print axioms TargetO.Automata.Det.B_p1_cor
#print axioms TargetO.Automata.Det.B_p1_cor_nopoly
#print axioms TargetO.Automata.Det.C_p1_thm
#print axioms TargetO.Automata.Det.C_p1_cor
