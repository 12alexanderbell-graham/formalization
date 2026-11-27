import Mathlib
import Readings.automata

/-! # Target O, family O66 (two-way automata): challenge-free machinery for the closures

Module `Closure.Common`; it imports no challenge, so it can be shared by the closures of the two
challenges that define the same constant names.

* `rtg_sim`, `tg_sim`, `sim_fin`: a step relation on configurations with a `Fin` head position
  simulates a step relation on configurations with a natural head position, for reachability with
  and without the empty run.
* The three readers' automaton models are translated into reader A's model (`ReaderA.TwoNFA`),
  which is the hub: `toA`/`ofA` for reader B and `toAC`/`ofAC` for reader C, with languages under
  both acceptance conventions, determinism and the absence of left moves preserved, and the round
  trip `toA (ofA N) = N`.
* The three readers' liveness languages are written as nonemptiness of the path order product
  `rp` of the word, mapped into `SetRel (Fin m) (Fin m)` (reader A's points `{1, …, m}` are
  relabelled by `iccEquiv`).
* `exists_big`: an exponential beats any power, in the form needed by the no polynomial bound
  corollaries.
-/

namespace TargetO.Automata

open Relation

/-! ## Simulation of reachability -/

theorem rtg_sim {α β : Type*} {S : α → α → Prop} {T : β → β → Prop} (f : α → β)
    (h1 : ∀ a a', S a a' → T (f a) (f a'))
    (h2 : ∀ a b, T (f a) b → ∃ a', f a' = b ∧ S a a') (a0 : α) (b0 b : β) (hf : f a0 = b0) :
    ReflTransGen T b0 b ↔ ∃ a, f a = b ∧ ReflTransGen S a0 a := by
  subst hf
  constructor
  · intro h
    induction h with
    | refl => exact ⟨a0, rfl, .refl⟩
    | tail _ hbc ih =>
      obtain ⟨a, rfl, ha⟩ := ih
      obtain ⟨a', rfl, h'⟩ := h2 _ _ hbc
      exact ⟨a', rfl, ha.tail h'⟩
  · rintro ⟨a, rfl, h⟩
    exact h.lift f h1

theorem tg_sim {α β : Type*} {S : α → α → Prop} {T : β → β → Prop} (f : α → β)
    (h1 : ∀ a a', S a a' → T (f a) (f a'))
    (h2 : ∀ a b, T (f a) b → ∃ a', f a' = b ∧ S a a') (a0 : α) (b0 b : β) (hf : f a0 = b0) :
    TransGen T b0 b ↔ ∃ a, f a = b ∧ TransGen S a0 a := by
  subst hf
  constructor
  · intro h
    induction h with
    | single hbc =>
      obtain ⟨a', rfl, h'⟩ := h2 _ _ hbc
      exact ⟨a', rfl, .single h'⟩
    | tail _ hbc ih =>
      obtain ⟨a, rfl, ha⟩ := ih
      obtain ⟨a', rfl, h'⟩ := h2 _ _ hbc
      exact ⟨a', rfl, ha.tail h'⟩
  · rintro ⟨a, rfl, h⟩
    exact h.lift f h1

/-- Acceptance (some reachable configuration has an accepting state) is the same for a step
relation on `Q × ℕ` and one on `Q × Fin n` that agrees with it and whose steps stay below `n`. -/
theorem sim_fin {Q : Type*} {n : ℕ} (hn : 0 < n) (S : Q × Fin n → Q × Fin n → Prop)
    (T : Q × ℕ → Q × ℕ → Prop)
    (hiff : ∀ a a' : Q × Fin n, T (a.1, a.2.val) (a'.1, a'.2.val) ↔ S a a')
    (hbd : ∀ (a : Q × Fin n) b, T (a.1, a.2.val) b → b.2 < n) (q0 : Q) (P : Q → Prop) :
    ((∃ c, ReflTransGen T (q0, 0) c ∧ P c.1) ↔
      ∃ a, ReflTransGen S (q0, ⟨0, hn⟩) a ∧ P a.1) ∧
    ((∃ c, TransGen T (q0, 0) c ∧ P c.1) ↔
      ∃ a, TransGen S (q0, ⟨0, hn⟩) a ∧ P a.1) := by
  have h1 : ∀ a a', S a a' → T (a.1, a.2.val) (a'.1, a'.2.val) := fun a a' h => (hiff a a').2 h
  have h2 : ∀ (a : Q × Fin n) b, T (a.1, a.2.val) b →
      ∃ a' : Q × Fin n, (a'.1, a'.2.val) = b ∧ S a a' :=
    fun a b h => ⟨(b.1, ⟨b.2, hbd a b h⟩), rfl, (hiff _ _).1 h⟩
  have hr := fun b => rtg_sim (S := S) (T := T) (fun a => (a.1, a.2.val)) h1 h2
    (q0, ⟨0, hn⟩) (q0, 0) b rfl
  have ht := fun b => tg_sim (S := S) (T := T) (fun a => (a.1, a.2.val)) h1 h2
    (q0, ⟨0, hn⟩) (q0, 0) b rfl
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨c, hc, hP⟩
    obtain ⟨a, rfl, ha⟩ := (hr c).1 hc
    exact ⟨a, ha, hP⟩
  · rintro ⟨a, ha, hP⟩
    exact ⟨_, (hr _).2 ⟨a, rfl, ha⟩, hP⟩
  · rintro ⟨c, hc, hP⟩
    obtain ⟨a, rfl, ha⟩ := (ht c).1 hc
    exact ⟨a, ha, hP⟩
  · rintro ⟨a, ha, hP⟩
    exact ⟨_, (ht _).2 ⟨a, rfl, ha⟩, hP⟩

/-! ## Reader A's model, the hub -/

namespace HubA

variable {α Q : Type}

theorem step_iff (M : ReaderA.TwoNFA α Q) (w : List α) (q q' : Q) (i j : ℕ) :
    M.Step w (q, i) (q', j) ↔ ∃ d, (q', d) ∈ M.δ q (ReaderA.TwoNFA.tapeAt w i) ∧
      j ≤ w.length + 1 ∧
      ((d = .left ∧ j + 1 = i) ∨ (d = .stay ∧ j = i) ∨ (d = .right ∧ j = i + 1)) := by
  simp only [ReaderA.TwoNFA.Step]
  constructor
  · rintro ⟨d, hd, hj, hm⟩
    refine ⟨d, hd, hj, ?_⟩
    cases d <;> simp_all
  · rintro ⟨d, hd, hj, hm⟩
    refine ⟨d, hd, hj, ?_⟩
    rcases hm with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact h

theorem step_bound (M : ReaderA.TwoNFA α Q) (w : List α) (c d : Q × ℕ) (h : M.Step w c d) :
    d.2 < w.length + 2 := by
  obtain ⟨q, i⟩ := c
  obtain ⟨q', j⟩ := d
  obtain ⟨_, _, hj, _⟩ := (step_iff M w q q' i j).1 h
  simp only
  omega

/-- Reader A's acceptance, both conventions, on configurations with a `Fin` head position. -/
def FS (M : ReaderA.TwoNFA α Q) (w : List α) (a a' : Q × Fin (w.length + 2)) : Prop :=
  M.Step w (a.1, a.2.val) (a'.1, a'.2.val)

theorem accepts_iff (M : ReaderA.TwoNFA α Q) (w : List α) :
    (M.Accepts w ↔ ∃ a, ReflTransGen (FS M w) (M.init, ⟨0, by omega⟩) a ∧ a.1 ∈ M.acc) ∧
    (M.AcceptsPos w ↔ ∃ a, TransGen (FS M w) (M.init, ⟨0, by omega⟩) a ∧ a.1 ∈ M.acc) :=
  sim_fin (by omega) (FS M w) (M.Step w) (fun _ _ => Iff.rfl)
    (fun a b h => step_bound M w _ _ h) M.init (· ∈ M.acc)

end HubA

/-! ## Reader B's model into reader A's -/

namespace HubB

variable {α Q : Type}

def dAB : ReaderA.Dir → ReaderB.Dir
  | .left => .L
  | .stay => .S
  | .right => .R

def dBA : ReaderB.Dir → ReaderA.Dir
  | .L => .left
  | .S => .stay
  | .R => .right

def sAB : ReaderA.TapeSym α → ReaderB.Sym α
  | .lend => .lm
  | .rend => .rm
  | .sym a => .ch a

def sBA : ReaderB.Sym α → ReaderA.TapeSym α
  | .lm => .lend
  | .rm => .rend
  | .ch a => .sym a

@[simp] theorem dAB_dBA (d : ReaderB.Dir) : dAB (dBA d) = d := by cases d <;> rfl
@[simp] theorem dBA_dAB (d : ReaderA.Dir) : dBA (dAB d) = d := by cases d <;> rfl
@[simp] theorem sAB_sBA (t : ReaderB.Sym α) : sAB (sBA t) = t := by cases t <;> rfl
@[simp] theorem sBA_sAB (t : ReaderA.TapeSym α) : sBA (sAB t) = t := by cases t <;> rfl

def toA (M : ReaderB.TwoWay α Q) : ReaderA.TwoNFA α Q :=
  ⟨M.init, M.acc, fun q t => {p | (p.1, dAB p.2) ∈ M.trans q (sAB t)}⟩

def ofA (N : ReaderA.TwoNFA α Q) : ReaderB.TwoWay α Q :=
  ⟨N.init, N.acc, fun q t => {p | (p.1, dBA p.2) ∈ N.δ q (sBA t)}⟩

theorem toA_ofA (N : ReaderA.TwoNFA α Q) : toA (ofA N) = N := by
  obtain ⟨i, a, δ⟩ := N
  simp only [toA, ofA, Set.mem_setOf_eq, dBA_dAB, sBA_sAB]
  rfl

theorem symAt_eq (w : List α) (i : ℕ) :
    ReaderB.symAt w i = sAB (ReaderA.TwoNFA.tapeAt w i) := by
  cases i with
  | zero => rfl
  | succ k =>
    simp only [ReaderB.symAt, ReaderA.TwoNFA.tapeAt]
    split_ifs <;> rfl

theorem step_iff (M : ReaderB.TwoWay α Q) (w : List α) (a a' : Q × Fin (w.length + 2)) :
    M.Step w (a.1, a.2.val) (a'.1, a'.2.val) ↔ HubA.FS (toA M) w a a' := by
  have ha := a.2.isLt
  have ha' := a'.2.isLt
  simp only [HubA.FS, HubA.step_iff, ReaderB.TwoWay.Step, toA, Set.mem_setOf_eq, symAt_eq]
  constructor
  · rintro ⟨-, hj, d, hd, hm⟩
    refine ⟨dBA d, by simpa using hd, hj, ?_⟩
    rcases hm with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [dBA] <;> omega
  · rintro ⟨d, hd, hj, hm⟩
    refine ⟨by omega, hj, dAB d, hd, ?_⟩
    rcases hm with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [dAB] <;> omega

theorem step_bound (M : ReaderB.TwoWay α Q) (w : List α) (c d : Q × ℕ) (h : M.Step w c d) :
    d.2 < w.length + 2 := by
  obtain ⟨-, h, -⟩ := h
  omega

theorem lang_eq (M : ReaderB.TwoWay α Q) : M.Lang = (toA M).lang ∧ M.LangPos = (toA M).langPos := by
  constructor <;> ext w
  · have h := (sim_fin (by omega) (HubA.FS (toA M) w) (M.Step w) (step_iff M w)
      (fun a b h => step_bound M w _ _ h) M.init (· ∈ M.acc)).1
    show _ ↔ (toA M).Accepts w
    rw [(HubA.accepts_iff (toA M) w).1]
    refine Iff.trans ?_ h
    simp only [ReaderB.TwoWay.Lang, Set.mem_setOf_eq]
    exact ⟨fun ⟨q, hq, i, hr⟩ => ⟨(q, i), hr, hq⟩, fun ⟨c, hr, hq⟩ => ⟨c.1, hq, c.2, hr⟩⟩
  · have h := (sim_fin (by omega) (HubA.FS (toA M) w) (M.Step w) (step_iff M w)
      (fun a b h => step_bound M w _ _ h) M.init (· ∈ M.acc)).2
    show _ ↔ (toA M).AcceptsPos w
    rw [(HubA.accepts_iff (toA M) w).2]
    refine Iff.trans ?_ h
    simp only [ReaderB.TwoWay.LangPos, Set.mem_setOf_eq]
    exact ⟨fun ⟨q, hq, i, hr⟩ => ⟨(q, i), hr, hq⟩, fun ⟨c, hr, hq⟩ => ⟨c.1, hq, c.2, hr⟩⟩

theorem isDet_iff (M : ReaderB.TwoWay α Q) : M.IsDet ↔ (toA M).IsDet := by
  constructor
  · intro h q t x hx y hy
    have := h q (sAB t) hx hy
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 (by simpa using congrArg dBA this.2)
  · intro h q t x hx y hy
    have := h q (sBA t) (x := (x.1, dBA x.2)) (by simpa [toA] using hx)
      (y := (y.1, dBA y.2)) (by simpa [toA] using hy)
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 (by simpa using congrArg dAB this.2)

theorem noLeft_iff (M : ReaderB.TwoWay α Q) : M.NoLeft ↔ (toA M).NoLeft := by
  constructor
  · intro h q t q' hq
    exact h q (sAB t) _ hq rfl
  · intro h q t x hx hL
    apply h q (sBA t) x.1
    show (x.1, dAB .left) ∈ M.trans q (sAB (sBA t))
    rw [sAB_sBA, show dAB ReaderA.Dir.left = x.2 from hL.symm]
    exact hx

end HubB

/-! ## Reader C's model into reader A's -/

namespace HubC

variable {α Q : Type}

def dAC : ReaderA.Dir → ReaderC.Move
  | .left => .left
  | .stay => .stay
  | .right => .right

def dCA : ReaderC.Move → ReaderA.Dir
  | .left => .left
  | .stay => .stay
  | .right => .right

def sAC : ReaderA.TapeSym α → ReaderC.Sym α
  | .lend => .lend
  | .rend => .rend
  | .sym a => .sym a

def sCA : ReaderC.Sym α → ReaderA.TapeSym α
  | .lend => .lend
  | .rend => .rend
  | .sym a => .sym a

@[simp] theorem dAC_dCA (d : ReaderC.Move) : dAC (dCA d) = d := by cases d <;> rfl
@[simp] theorem dCA_dAC (d : ReaderA.Dir) : dCA (dAC d) = d := by cases d <;> rfl
@[simp] theorem sAC_sCA (t : ReaderC.Sym α) : sAC (sCA t) = t := by cases t <;> rfl
@[simp] theorem sCA_sAC (t : ReaderA.TapeSym α) : sCA (sAC t) = t := by cases t <;> rfl

def toA (M : ReaderC.TWA Q α) : ReaderA.TwoNFA α Q :=
  ⟨M.init, M.accept, fun q t => {p | (p.1, dAC p.2) ∈ M.δ q (sAC t)}⟩

def ofA (N : ReaderA.TwoNFA α Q) : ReaderC.TWA Q α :=
  ⟨N.init, N.acc, fun q t => {p | (p.1, dCA p.2) ∈ N.δ q (sCA t)}⟩

theorem toA_ofA (N : ReaderA.TwoNFA α Q) : toA (ofA N) = N := by
  obtain ⟨i, a, δ⟩ := N
  simp only [toA, ofA, Set.mem_setOf_eq, dCA_dAC, sCA_sAC]
  rfl

theorem tapeAt_eq (w : List α) (i : ℕ) :
    ReaderC.tapeAt w i = sAC (ReaderA.TwoNFA.tapeAt w i) := by
  cases i with
  | zero => rfl
  | succ k =>
    simp only [ReaderC.tapeAt, ReaderA.TwoNFA.tapeAt]
    split_ifs with h
    · simp [List.getElem?_eq_getElem h, sAC]
    · rw [List.getElem?_eq_none (by omega)]
      rfl

theorem step_iff (M : ReaderC.TWA Q α) (w : List α) (a a' : Q × Fin (w.length + 2)) :
    M.Step w (a.1, a.2.val) (a'.1, a'.2.val) ↔ HubA.FS (toA M) w a a' := by
  have ha := a.2.isLt
  have ha' := a'.2.isLt
  simp only [HubA.FS, HubA.step_iff, ReaderC.TWA.Step, toA, Set.mem_setOf_eq, tapeAt_eq]
  constructor
  · rintro ⟨d, hd, hm⟩
    refine ⟨dCA d, by simpa using hd, by omega, ?_⟩
    rcases hm with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [dCA] <;> omega
  · rintro ⟨d, hd, hj, hm⟩
    refine ⟨dAC d, hd, ?_⟩
    rcases hm with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp [dAC] <;> omega

theorem lang_eq (M : ReaderC.TWA Q α) : M.Lang = (toA M).lang := by
  ext w
  have h := (sim_fin (by omega) (HubA.FS (toA M) w) (M.Step w) (step_iff M w)
    (fun a b h => by
      have := a.2.isLt
      obtain ⟨d, -, hm⟩ := h
      omega) M.init (· ∈ M.accept)).1
  show _ ↔ (toA M).Accepts w
  rw [(HubA.accepts_iff (toA M) w).1]
  refine Iff.trans ?_ h
  simp only [ReaderC.TWA.Lang, ReaderC.TWA.Accepts, Set.mem_setOf_eq]
  exact ⟨fun ⟨q, hq, i, hr⟩ => ⟨(q, i), hr, hq⟩, fun ⟨c, hr, hq⟩ => ⟨c.1, hq, c.2, hr⟩⟩

theorem det_iff (M : ReaderC.TWA Q α) : M.Det ↔ (toA M).IsDet := by
  constructor
  · intro h q t x hx y hy
    have := h q (sAC t) hx hy
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 (by simpa using congrArg dCA this.2)
  · intro h q t x hx y hy
    have := h q (sCA t) (x := (x.1, dCA x.2)) (by simpa [toA] using hx)
      (y := (y.1, dCA y.2)) (by simpa [toA] using hy)
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 (by simpa using congrArg dAC this.2)

theorem noLeft_iff (M : ReaderC.TWA Q α) : M.NoLeft ↔ (toA M).NoLeft := by
  constructor
  · intro h q t q' hq
    exact h q (sAC t) q' _ hq rfl
  · intro h q t q' m hm hL
    subst hL
    apply h q (sCA t) q'
    show (q', dAC .left) ∈ M.δ q (sAC (sCA t))
    rw [sAC_sCA]
    exact hm

end HubC

/-! ## Relation products -/

/-- The path order product of a word of relations, empty product the identity. -/
def rp {H : Type*} (w : List (SetRel H H)) : SetRel H H := w.foldr SetRel.comp SetRel.id

theorem rp_cons {H : Type*} (R : SetRel H H) (w : List (SetRel H H)) :
    rp (R :: w) = R.comp (rp w) := rfl

theorem foldl_comp {H : Type*} (A : SetRel H H) (w : List (SetRel H H)) :
    w.foldl SetRel.comp A = A.comp (rp w) := by
  induction w generalizing A with
  | nil => simp [rp]
  | cons R w ih => rw [List.foldl_cons, ih, rp_cons, SetRel.comp_assoc]

/-- Reader A's points `{1, …, m}` relabelled as `Fin m`. -/
def iccEquiv (m : ℕ) : ReaderA.Icc1 m ≃ Fin m where
  toFun x := ⟨x.1 - 1, by have := Finset.mem_Icc.1 x.2; omega⟩
  invFun i := ⟨i.1 + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  left_inv x := Subtype.ext (by have := Finset.mem_Icc.1 x.2; simp only; omega)
  right_inv i := Fin.ext (by simp)

/-- Relations transported along a bijection of the points. -/
def relEquiv {H K : Type*} (σ : H ≃ K) : Set (H × H) ≃ SetRel K K where
  toFun R := {p | (σ.symm p.1, σ.symm p.2) ∈ R}
  invFun S := {p | (σ p.1, σ p.2) ∈ S}
  left_inv R := by ext ⟨a, b⟩; simp
  right_inv S := by ext ⟨a, b⟩; simp

theorem relEquiv_nonempty {H K : Type*} (σ : H ≃ K) (R : Set (H × H)) :
    (relEquiv σ R).Nonempty ↔ R.Nonempty :=
  ⟨fun ⟨_, hp⟩ => ⟨_, hp⟩, fun ⟨p, hp⟩ => ⟨(σ p.1, σ p.2), by simpa [relEquiv] using hp⟩⟩

theorem relEquiv_wordProd {H K : Type} (σ : H ≃ K) (w : List (ReaderA.BRel H)) :
    relEquiv σ (ReaderA.wordProd w) = rp (w.map (relEquiv σ)) := by
  induction w with
  | nil =>
    ext ⟨a, b⟩
    simp [ReaderA.wordProd, ReaderA.relId, relEquiv, rp]
  | cons R w ih =>
    rw [ReaderA.wordProd, List.map_cons, rp_cons, ← ih]
    ext ⟨a, c⟩
    simp only [relEquiv, ReaderA.relMul, Equiv.coe_fn_mk, Set.mem_setOf_eq, SetRel.mem_comp]
    constructor
    · rintro ⟨q, h1, h2⟩
      exact ⟨σ q, by simpa using h1, by simpa using h2⟩
    · rintro ⟨b, h1, h2⟩
      exact ⟨σ.symm b, h1, h2⟩

theorem memA_iff {H K : Type} (σ : H ≃ K) (w : List (ReaderA.BRel H)) :
    w ∈ ReaderA.LH H ↔ (rp (w.map (relEquiv σ))).Nonempty := by
  rw [← relEquiv_wordProd, relEquiv_nonempty, Set.nonempty_iff_ne_empty]
  rfl

/-- Reader B's relations `H → H → Prop` as sets of pairs. -/
def eB (H : Type) : ReaderB.Rel' H ≃ SetRel H H where
  toFun R := {p | R p.1 p.2}
  invFun S a b := (a, b) ∈ S
  left_inv _ := rfl
  right_inv _ := rfl

theorem eB_foldl {H : Type} (A : ReaderB.Rel' H) (w : List (ReaderB.Rel' H)) :
    eB H (w.foldl (fun A R => Relation.Comp A R) A) = (w.map (eB H)).foldl SetRel.comp (eB H A) := by
  induction w generalizing A with
  | nil => rfl
  | cons R w ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons]
    congr 1

theorem memB_iff {H : Type} (w : List (ReaderB.Rel' H)) :
    w ∈ ReaderB.livenessLang H ↔ (rp (w.map (eB H))).Nonempty := by
  have : eB H (ReaderB.relProd w) = rp (w.map (eB H)) := by
    rw [ReaderB.relProd, eB_foldl, foldl_comp]
    have : eB H Eq = SetRel.id := rfl
    rw [this, SetRel.id_comp]
  rw [← this]
  exact ⟨fun ⟨a, b, h⟩ => ⟨(a, b), h⟩, fun ⟨p, h⟩ => ⟨p.1, p.2, h⟩⟩

theorem memC_iff {H : Type} (w : List (Set (H × H))) :
    w ∈ ReaderC.relLive H ↔ (rp w).Nonempty := by
  have h1 : (ReaderC.relComp : Set (H × H) → Set (H × H) → Set (H × H)) = SetRel.comp := by
    funext A B
    ext ⟨a, c⟩
    rfl
  have h2 : ReaderC.relId H = SetRel.id := by
    ext ⟨a, b⟩
    rfl
  have : ReaderC.relProd w = rp w := by
    rw [ReaderC.relProd, h1, h2, foldl_comp, SetRel.id_comp]
  show ReaderC.relProd w ≠ ∅ ↔ _
  rw [this, Set.nonempty_iff_ne_empty]

/-! ## Exponentials beat powers -/

theorem eventually_small (C : ℝ) (m : ℕ) : ∃ K : ℕ, ∀ k ≥ K, C * (k : ℝ) ^ m + 1 < 2 ^ k / 8 := by
  have h1 := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) m (r := 2) (by norm_num)
  have hε : (0 : ℝ) < 1 / (16 * (|C| + 1)) := by positivity
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (h1.def hε)
  refine ⟨max K 5, fun k hk => ?_⟩
  have hb := hK k (le_of_max_le_left hk)
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ m),
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ k)] at hb
  have h32 : (32 : ℝ) ≤ 2 ^ k := by
    have : (2 : ℝ) ^ 5 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (le_of_max_le_right hk)
    norm_num at this
    linarith
  have hC : C * (k : ℝ) ^ m ≤ |C| * (k : ℝ) ^ m :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have h3 : |C| * (k : ℝ) ^ m ≤ |C| * (1 / (16 * (|C| + 1)) * 2 ^ k) :=
    mul_le_mul_of_nonneg_left hb (abs_nonneg C)
  have h4 : |C| * (1 / (16 * (|C| + 1)) * 2 ^ k) = (|C| / (|C| + 1)) * (2 ^ k / 16) := by
    field_simp
  have h5 : |C| / (|C| + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have h6 : (|C| / (|C| + 1)) * (2 ^ k / 16) ≤ 2 ^ k / 16 :=
    mul_le_of_le_one_left (by positivity) h5
  linarith

/-- For every real `C, c`, and `a ≥ 1`, some `k ≥ 1` has `|C| (a k + b)^c + 1 < 2^k / 8`. -/
theorem exists_big (C c : ℝ) (a b : ℕ) (ha : 1 ≤ a) :
    ∃ k : ℕ, 1 ≤ k ∧ |C| * (((a * k + b : ℕ) : ℝ) ^ c) + 1 < 2 ^ k / 8 := by
  set m := ⌈c⌉₊
  obtain ⟨K, hK⟩ := eventually_small (|C| * ((a + b : ℕ) : ℝ) ^ m) m
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  set k := max K 1
  have hk : 1 ≤ k := le_max_right _ _
  have hn1 : (1 : ℝ) ≤ ((a * k + b : ℕ) : ℝ) := by
    have : 1 ≤ a * k + b := le_trans (Nat.one_le_iff_ne_zero.2 (by positivity)) (Nat.le_add_right _ _)
    exact_mod_cast this
  have h1 : ((a * k + b : ℕ) : ℝ) ^ c ≤ ((a * k + b : ℕ) : ℝ) ^ m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil c)
  have h2 : ((a * k + b : ℕ) : ℝ) ^ m ≤ ((a + b : ℕ) : ℝ) ^ m * (k : ℝ) ^ m := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : a * k + b ≤ (a + b) * k := by nlinarith
    exact_mod_cast this
  have := hK k (le_max_left _ _)
  have h3 : |C| * ((a * k + b : ℕ) : ℝ) ^ c ≤ |C| * ((a + b : ℕ) : ℝ) ^ m * (k : ℝ) ^ m := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C)
  linarith

theorem poly_le (p : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) : p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn (by simpa [Nat.lt_succ_iff] using hi))

/-- A polynomial with natural coefficients is eventually below the exponential, along `a k + b`. -/
theorem exists_big_poly (p : Polynomial ℕ) (a b : ℕ) (ha : 1 ≤ a) :
    ∃ k : ℕ, 1 ≤ k ∧ ((p.eval (a * k + b) : ℕ) : ℝ) + 1 < 2 ^ k / 8 := by
  obtain ⟨k, hk, h⟩ := exists_big ((p.eval 1 : ℕ) : ℝ) (p.natDegree : ℝ) a b ha
  rw [abs_of_nonneg (Nat.cast_nonneg _), Real.rpow_natCast] at h
  refine ⟨k, hk, lt_of_le_of_lt ?_ h⟩
  have h1 : 1 ≤ a * k + b := le_trans (Nat.one_le_iff_ne_zero.2 (by positivity)) (Nat.le_add_right _ _)
  have h2 := poly_le p h1
  have h3 : ((p.eval (a * k + b) : ℕ) : ℝ) ≤ ((p.eval 1 * (a * k + b) ^ p.natDegree : ℕ) : ℝ) := by
    exact_mod_cast h2
  rw [Nat.cast_mul, Nat.cast_pow] at h3
  linarith

end TargetO.Automata
