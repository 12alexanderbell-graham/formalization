import Mathlib
import Readings.turing
import ComparatorChallenges.DegreeRigidity

/-! # Target O, family O53 (rigidity of the Turing degrees): closures (run 2026-11-27T1628Z).

Frozen statement `OAI.TuringRigidity.ManuscriptMain.rigidity : MainTheorem`, used only through `MainTheorem`
(never retyped): every order automorphism of `Degree = Antisymmetrization (ℕ → Bool) Reduces` is the identity.

The three readers built degrees of *sets* `Set ℕ` (characteristic functions into `ℕ →. ℕ`, Mathlib's
`TuringReducible`); the frozen statement builds degrees of oracles `ℕ → Bool` with the same 0/1 characteristic
function and the same `TuringReducible`. The link: `Set ℕ ≃ (ℕ → Bool)` (`n ↦ decide (n ∈ A)`) carries each
reader's reducibility to `Reduces` exactly, hence each reader's degree poset is order-isomorphic to the frozen
`Degree`, and rigidity transfers along any order isomorphism (`transfer`). Each reader's statement asks for a
bijection that preserves and reflects the order, which is what an order automorphism is. -/

namespace TargetO.Turing

open OAI.TuringRigidity

/-- Rigidity transfers along an order-isomorphism onto the frozen degrees. -/
theorem transfer {X : Type*} (R : X → X → Prop) (f : X ≃ Degree) (hf : ∀ a b, R a b ↔ f a ≤ f b)
    (frozen : MainTheorem) :
    ∀ π : X → X, Function.Bijective π → (∀ a b, R a b ↔ R (π a) (π b)) → ∀ a, π a = a := by
  intro π hπ hord a
  let e : X ≃ X := Equiv.ofBijective π hπ
  let ρ : Degree ≃ Degree := (f.symm.trans e).trans f
  have hρ : ∀ x y : Degree, ρ x ≤ ρ y ↔ x ≤ y := by
    intro x y
    simp only [ρ, Equiv.trans_apply, e, Equiv.ofBijective_apply]
    rw [← hf, ← hord, hf]
    simp
  have := frozen ⟨ρ, fun {x y} => hρ x y⟩ (f a)
  have h2 : f (π a) = f a := by simpa [ρ, e] using this
  exact f.injective h2

/-- Sets of naturals and the frozen oracles. -/
noncomputable def toOracle : Set ℕ ≃ Oracle := by
  classical
  exact {
  toFun := fun A n => decide (n ∈ A)
  invFun := fun g => {n | g n = true}
  left_inv := fun A => by ext n; simp
  right_inv := fun g => by funext n; simp }

section Cl
open Classical

/-- The frozen characteristic function of `toOracle A` is each reader's characteristic function of `A`. -/
theorem oracleFunction_toOracle (A : Set ℕ) (n : ℕ) :
    oracleFunction (toOracle A) n = Part.some (if n ∈ A then 1 else 0) := by
  classical
  simp [oracleFunction, toOracle]

theorem chiA_eq (A : Set ℕ) : ReaderA.chi A = oracleFunction (toOracle A) := by
  classical
  funext n; rw [oracleFunction_toOracle]; simp [ReaderA.chi]

theorem chiB_eq (A : Set ℕ) : ReaderB.charFn A = oracleFunction (toOracle A) := by
  classical
  funext n; rw [oracleFunction_toOracle]; simp [ReaderB.charFn]

theorem chiC_eq (A : Set ℕ) : ReaderC.chi A = oracleFunction (toOracle A) := by
  classical
  funext n; rw [oracleFunction_toOracle]; simp [ReaderC.chi]

end Cl

/-- The frozen degree of an oracle. -/
def dg (g : Oracle) : Degree := toAntisymmetrization Reduces g

/-- On representatives, the frozen order is `Reduces`. -/
theorem deg_le_iff (g h : Oracle) :
    dg g ≤ dg h ↔ Reduces g h := Iff.rfl

/-- The frozen `Degree` as a quotient of oracles by mutual reducibility. -/
theorem deg_eq_iff (g h : Oracle) :
    dg g = dg h ↔
      Reduces g h ∧ Reduces h g := by
  constructor
  · intro e
    exact ⟨(deg_le_iff g h).1 (le_of_eq e), (deg_le_iff h g).1 (le_of_eq e.symm)⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm ((deg_le_iff g h).2 h1) ((deg_le_iff h g).2 h2)

theorem deg_surj (d : Degree) : ∃ g, dg g = d := by
  induction d using Quotient.inductionOn' with
  | h g => exact ⟨g, rfl⟩

/-- A quotient of `Set ℕ` by mutual `R`-reducibility, with `R` carried by `toOracle` to `Reduces`, is
order-isomorphic to the frozen degrees. Built from a surjection `q` with `q A = q B ↔ R A B ∧ R B A`. -/
noncomputable def quotEquiv {X : Type*} (q : Set ℕ → X) (hq : Function.Surjective q) (R : Set ℕ → Set ℕ → Prop)
    (hR : ∀ A B, R A B ↔ Reduces (toOracle A) (toOracle B)) (hqe : ∀ A B, q A = q B ↔ R A B ∧ R B A) :
    X ≃ Degree :=
  Equiv.ofBijective (fun x => dg (toOracle (Function.surjInv hq x))) (by
    constructor
    · intro x y hxy
      rw [deg_eq_iff, ← hR, ← hR, ← hqe] at hxy
      simpa [Function.surjInv_eq hq] using hxy
    · intro d
      obtain ⟨g, rfl⟩ := deg_surj d
      refine ⟨q (toOracle.symm g), ?_⟩
      have hg : g = toOracle (toOracle.symm g) := (toOracle.apply_symm_apply g).symm
      show dg _ = dg _
      conv_rhs => rw [hg]
      rw [deg_eq_iff, ← hR, ← hR, ← hqe, Function.surjInv_eq hq])

theorem quotEquiv_apply {X : Type*} (q : Set ℕ → X) (hq : Function.Surjective q) (R : Set ℕ → Set ℕ → Prop)
    (hR : ∀ A B, R A B ↔ Reduces (toOracle A) (toOracle B)) (hqe : ∀ A B, q A = q B ↔ R A B ∧ R B A)
    (A : Set ℕ) : quotEquiv q hq R hR hqe (q A) = dg (toOracle A) := by
  show dg _ = dg _
  rw [deg_eq_iff, ← hR, ← hR, ← hqe, Function.surjInv_eq hq]

/-! ## Reader A -/

theorem hRA (A B : Set ℕ) : ReaderA.LeT A B ↔ Reduces (toOracle A) (toOracle B) := by
  simp only [ReaderA.LeT, Reduces, chiA_eq]

/-- Reader A's degree of a set. -/
def qA (A : Set ℕ) : ReaderA.DT := Quotient.mk ReaderA.turingSetoid A

theorem qA_surj : Function.Surjective qA := Quotient.mk_surjective

theorem qA_eq (A B : Set ℕ) : qA A = qA B ↔ ReaderA.LeT A B ∧ ReaderA.LeT B A :=
  Quotient.eq (r := ReaderA.turingSetoid)

theorem qA_le (A B : Set ℕ) : ReaderA.DT.le (qA A) (qA B) ↔ ReaderA.LeT A B := Iff.rfl

theorem closure_A (frozen : MainTheorem) :
    ∀ π : ReaderA.DT → ReaderA.DT, Function.Bijective π →
      (∀ a b : ReaderA.DT, ReaderA.DT.le a b ↔ ReaderA.DT.le (π a) (π b)) →
      ∀ a : ReaderA.DT, π a = a := by
  refine transfer _ (quotEquiv qA qA_surj _ hRA qA_eq) ?_ frozen
  intro a b
  obtain ⟨A, rfl⟩ := qA_surj a
  obtain ⟨B, rfl⟩ := qA_surj b
  rw [quotEquiv_apply qA qA_surj _ hRA qA_eq, quotEquiv_apply qA qA_surj _ hRA qA_eq, deg_le_iff, ← hRA,
    qA_le]

theorem reading_A_closed : type_of% @ReaderA.reading_rigidity :=
  closure_A OAI.TuringRigidity.ManuscriptMain.rigidity

/-! ## Reader B -/

theorem hRB (A B : Set ℕ) : ReaderB.leT A B ↔ Reduces (toOracle A) (toOracle B) := by
  simp only [ReaderB.leT, Reduces, chiB_eq]

/-- Reader B's degree of a set. -/
def qB (A : Set ℕ) : ReaderB.Degrees := toAntisymmetrization (α := ReaderB.IntSet) (· ≤ ·) A

theorem qB_surj : Function.Surjective qB := fun d => by
  induction d using Antisymmetrization.ind with
  | _ g => exact ⟨g, rfl⟩

theorem qB_eq (A B : Set ℕ) : qB A = qB B ↔ ReaderB.leT A B ∧ ReaderB.leT B A := by
  exact (toAntisymmetrization_eq (α := ReaderB.IntSet) (· ≤ ·) A B).trans Iff.rfl

theorem qB_le (A B : Set ℕ) : qB A ≤ qB B ↔ ReaderB.leT A B := by
  exact toAntisymmetrization_le_toAntisymmetrization_iff (α := ReaderB.IntSet) (a := A) (b := B)

theorem closure_B (frozen : MainTheorem) (π : ReaderB.Degrees → ReaderB.Degrees) (hπ : Function.Bijective π)
    (hord : ∀ a b : ReaderB.Degrees, a ≤ b ↔ π a ≤ π b) : ∀ a : ReaderB.Degrees, π a = a := by
  refine transfer (fun a b : ReaderB.Degrees => a ≤ b) (quotEquiv qB qB_surj _ hRB qB_eq) ?_ frozen π hπ hord
  intro a b
  obtain ⟨A, rfl⟩ := qB_surj a
  obtain ⟨B, rfl⟩ := qB_surj b
  rw [quotEquiv_apply qB qB_surj _ hRB qB_eq, quotEquiv_apply qB qB_surj _ hRB qB_eq, deg_le_iff, ← hRB,
    qB_le]

theorem reading_B_closed : type_of% @ReaderB.readingRigidity :=
  closure_B OAI.TuringRigidity.ManuscriptMain.rigidity

/-! ## Reader C (existential order on the quotient) -/

theorem hRC (A B : Set ℕ) : ReaderC.leT A B ↔ Reduces (toOracle A) (toOracle B) := by
  simp only [ReaderC.leT, Reduces, chiC_eq]

theorem qC_surj : Function.Surjective ReaderC.deg := Quotient.mk_surjective

theorem qC_eq (A B : Set ℕ) : ReaderC.deg A = ReaderC.deg B ↔ ReaderC.leT A B ∧ ReaderC.leT B A :=
  Quotient.eq (r := ReaderC.tSetoid)

/-- Reader C's existential order agrees with the representatives' reducibility. -/
theorem leDeg_iff (A B : Set ℕ) : ReaderC.leDeg (ReaderC.deg A) (ReaderC.deg B) ↔ ReaderC.leT A B := by
  constructor
  · rintro ⟨A', B', hA, hB, h⟩
    have hA' := (qC_eq A A').1 hA
    have hB' := (qC_eq B B').1 hB
    exact ReaderC.leT_trans hA'.1 (ReaderC.leT_trans h hB'.2)
  · intro h; exact ⟨A, B, rfl, rfl, h⟩

theorem closure_C (frozen : MainTheorem) :
    ∀ π : ReaderC.DT → ReaderC.DT, Function.Bijective π →
      (∀ a b : ReaderC.DT, ReaderC.leDeg a b ↔ ReaderC.leDeg (π a) (π b)) →
      ∀ a : ReaderC.DT, π a = a := by
  refine transfer _ (quotEquiv _ qC_surj _ hRC qC_eq) ?_ frozen
  intro a b
  obtain ⟨A, rfl⟩ := qC_surj a
  obtain ⟨B, rfl⟩ := qC_surj b
  rw [quotEquiv_apply _ qC_surj _ hRC qC_eq, quotEquiv_apply _ qC_surj _ hRC qC_eq, deg_le_iff, ← hRC,
    leDeg_iff]

theorem reading_C_closed : type_of% @ReaderC.reading_turing_rigidity :=
  closure_C OAI.TuringRigidity.ManuscriptMain.rigidity

/-- No reader's degree is lost or merged by the link: `toOracle` is a bijection of `Set ℕ` onto the oracles. -/
theorem toOracle_bij : Function.Bijective toOracle := toOracle.bijective

end TargetO.Turing

#print axioms TargetO.Turing.closure_A
#print axioms TargetO.Turing.closure_B
#print axioms TargetO.Turing.closure_C
#print axioms TargetO.Turing.reading_A_closed
#print axioms TargetO.Turing.reading_B_closed
#print axioms TargetO.Turing.reading_C_closed
