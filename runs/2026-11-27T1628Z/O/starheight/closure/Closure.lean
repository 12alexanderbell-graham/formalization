import Mathlib
import Readings.starheight
import ComparatorChallenges.GeneralizedStarHeight

/-! # Target O, family O59 (generalized star height at most three): closures (run 2026-11-27T1628Z).

Frozen statement `OAI.GeneralizedStarHeight.main` (taken by name, never retyped): over every finite alphabet
(`[Finite Alphabet]`, any universe), every `Language.IsRegular` language has an `Expression` of height `≤ 3`.

Each reader wrote its own expression type; the closure maps a frozen expression to the reader's one constructor by
constructor (`ofE`) and proves that the map preserves the language and the height, so the frozen expression for
`L` gives the reader's. Readers A and B take languages with Mathlib's `Language` operations (the frozen ones);
reader C writes them as sets of lists (`∅`, `{[]}`, `∪`, explicit concatenation and flattening, `univ \ ·`),
proved equal to Mathlib's `0, 1, +, *, ∗, ᶜ` (`Language.mul_def`, `Language.kstar_def`). Regularity: reader A uses
Mathlib's `Language.IsRegular`; B's DFA definition is the same proposition; C's explicit `foldl` automaton is a
Mathlib `DFA` with the same accepted language. -/

namespace TargetO.StarHeight

open OAI.GeneralizedStarHeight

universe u

/-! ## Reader A -/

def toA {α : Type*} : Expression α → ReaderA.GRE α
  | .zero => .zero
  | .one => .one
  | .letter a => .letter a
  | .union P Q => .union (toA P) (toA Q)
  | .concat P Q => .concat (toA P) (toA Q)
  | .compl P => .compl (toA P)
  | .star P => .star (toA P)

theorem toA_lang {α : Type*} (P : Expression α) : (toA P).denote = P.language := by
  induction P with
  | zero => rfl
  | one => rfl
  | letter a => rfl
  | union P Q hP hQ => simp only [toA, ReaderA.GRE.denote, Expression.language, hP, hQ]
  | concat P Q hP hQ => simp only [toA, ReaderA.GRE.denote, Expression.language, hP, hQ]
  | compl P hP => simp only [toA, ReaderA.GRE.denote, Expression.language, hP]
  | star P hP => simp only [toA, ReaderA.GRE.denote, Expression.language, hP]

theorem toA_ht {α : Type*} (P : Expression α) : (toA P).sht = P.height := by
  induction P with
  | zero => rfl
  | one => rfl
  | letter a => rfl
  | union P Q hP hQ => simp only [toA, ReaderA.GRE.sht, Expression.height, hP, hQ]
  | concat P Q hP hQ => simp only [toA, ReaderA.GRE.sht, Expression.height, hP, hQ]
  | compl P hP => simp only [toA, ReaderA.GRE.sht, Expression.height, hP]
  | star P hP => simp only [toA, ReaderA.GRE.sht, Expression.height, hP]

theorem closure_A (frozen : type_of% @main.{u}) : type_of% @ReaderA.reading_thm_1_1.{u} := by
  intro α _ L hL
  obtain ⟨P, hP, hh⟩ := frozen L hL
  exact ⟨toA P, by rw [toA_lang, hP], by rw [toA_ht]; exact hh⟩

/-! ## Reader B -/

def toB {α : Type} : Expression α → ReaderB.GRE α
  | .zero => .zero
  | .one => .one
  | .letter a => .letter a
  | .union P Q => .union (toB P) (toB Q)
  | .concat P Q => .concat (toB P) (toB Q)
  | .compl P => .compl (toB P)
  | .star P => .star (toB P)

theorem toB_lang {α : Type} (P : Expression α) : (toB P).sem = P.language := by
  induction P with
  | zero => rfl
  | one => rfl
  | letter a => rfl
  | union P Q hP hQ => simp only [toB, ReaderB.GRE.sem, Expression.language, hP, hQ]
  | concat P Q hP hQ => simp only [toB, ReaderB.GRE.sem, Expression.language, hP, hQ]
  | compl P hP => simp only [toB, ReaderB.GRE.sem, Expression.language, hP]
  | star P hP => simp only [toB, ReaderB.GRE.sem, Expression.language, hP]

theorem toB_ht {α : Type} (P : Expression α) : (toB P).sht = P.height := by
  induction P with
  | zero => rfl
  | one => rfl
  | letter a => rfl
  | union P Q hP hQ => simp only [toB, ReaderB.GRE.sht, Expression.height, hP, hQ]
  | concat P Q hP hQ => simp only [toB, ReaderB.GRE.sht, Expression.height, hP, hQ]
  | compl P hP => simp only [toB, ReaderB.GRE.sht, Expression.height, hP]
  | star P hP => simp only [toB, ReaderB.GRE.sht, Expression.height, hP]

theorem regB {α : Type} (L : Language α) (h : ReaderB.IsRegularLang L) : L.IsRegular := h

theorem closure_B (frozen : type_of% @main.{0}) : type_of% @ReaderB.readingThm1_1 := by
  intro α _ L hL
  obtain ⟨P, hP, hh⟩ := frozen L (regB L hL)
  exact ⟨toB P, by rw [toB_lang, hP], by rw [toB_ht]; exact hh⟩

/-! ## Reader C -/

def toC {α : Type} : Expression α → ReaderC.GRE α
  | .zero => .zero
  | .one => .one
  | .letter a => .letter a
  | .union P Q => .union (toC P) (toC Q)
  | .concat P Q => .concat (toC P) (toC Q)
  | .compl P => .compl (toC P)
  | .star P => .star (toC P)

theorem toC_lang {α : Type} (P : Expression α) : (toC P).lang = (P.language : Set (List α)) := by
  induction P with
  | zero => rfl
  | one => rfl
  | letter a => rfl
  | union P Q hP hQ =>
    simp only [toC, ReaderC.GRE.lang, Expression.language, hP, hQ, Language.add_def]
  | concat P Q hP hQ =>
    simp only [toC, ReaderC.GRE.lang, Expression.language, hP, hQ, Language.mul_def]
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_image2]
    constructor
    · rintro ⟨u, v, rfl, hu, hv⟩; exact ⟨u, hu, v, hv, rfl⟩
    · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, v, rfl, hu, hv⟩
  | compl P hP =>
    simp only [toC, ReaderC.GRE.lang]
    rw [hP]
    ext w
    exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  | star P hP =>
    simp only [toC, ReaderC.GRE.lang, Expression.language, hP, Language.kstar_def]
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, rfl, hl⟩
    · rintro ⟨l, rfl, hl⟩; exact ⟨l, hl, rfl⟩

theorem toC_ht {α : Type} (P : Expression α) : (toC P).ht = P.height := by
  induction P with
  | zero => rfl
  | one => rfl
  | letter a => rfl
  | union P Q hP hQ => simp only [toC, ReaderC.GRE.ht, Expression.height, hP, hQ]
  | concat P Q hP hQ => simp only [toC, ReaderC.GRE.ht, Expression.height, hP, hQ]
  | compl P hP => simp only [toC, ReaderC.GRE.ht, Expression.height, hP]
  | star P hP => simp only [toC, ReaderC.GRE.ht, Expression.height, hP]

theorem regC {α : Type} (L : Set (List α)) (h : ReaderC.IsRegularLang L) : Language.IsRegular (L : Language α) := by
  obtain ⟨Q, _, δ, q0, F, rfl⟩ := h
  exact ⟨Q, inferInstance, ⟨δ, q0, F⟩, rfl⟩

theorem closure_C (frozen : type_of% @main.{0}) : type_of% @ReaderC.reading_starheight_le_three := by
  intro α _ L hL
  obtain ⟨P, hP, hh⟩ := frozen (L : Language α) (regC L hL)
  exact ⟨toC P, by rw [toC_lang, hP], by rw [toC_ht]; exact hh⟩

theorem reading_A_closed : type_of% @ReaderA.reading_thm_1_1.{u} := closure_A @main.{u}
theorem reading_B_closed : type_of% @ReaderB.readingThm1_1 := closure_B @main.{0}
theorem reading_C_closed : type_of% @ReaderC.reading_starheight_le_three := closure_C @main.{0}

end TargetO.StarHeight

#print axioms TargetO.StarHeight.closure_A
#print axioms TargetO.StarHeight.closure_B
#print axioms TargetO.StarHeight.closure_C
