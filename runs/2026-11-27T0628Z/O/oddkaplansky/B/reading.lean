import Mathlib

namespace ReaderB

/-- m = C(1200,600). -/
def m : ℕ := Nat.choose 1200 600

/-- p = min {h > 1 : h ∣ (m!)^2 + 1}. (Source uses h ∈ ℤ; positive divisors are naturals.)
If the set were empty, sInf would be the junk value 0; the theorem's `p.Prime` rules that out. -/
noncomputable def p : ℕ := sInf {h : ℕ | 1 < h ∧ h ∣ (Nat.factorial m) ^ 2 + 1}

/-- Theorem 1.1. "Specified" is read as existence. Torsion: an element g ≠ 1 of finite order. -/
theorem readingKaplansky :
    p.Prime ∧ p ≠ 2 ∧
    ∃ (K : Type) (_ : Field K), Nat.card K = p ^ 4 ∧
    ∃ (G : Type) (_ : Group G), Group.FG G ∧ (∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) ∧
      ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1 := sorry

/-
Ambiguities / choices:
- "specified": formalized as existence (K, G, a, b are not pinned down).
- Field K of order p^4: `Nat.card K = p^4` (a finite field has positive card; infinite gives 0 ≠ p^4).
- Torsion: some nontrivial element of finite order (`g ≠ 1 ∧ IsOfFinOrder g`).
- Finitely generated: `Group.FG G`. Universe Type.
- "finite sums a,b": automatic in `MonoidAlgebra K G` (finitely supported).
- p: sInf of a set of naturals (junk 0 if empty, excluded by `p.Prime`). "odd prime" = Prime ∧ ≠ 2.
- m, p not evaluated.
-/

end ReaderB
