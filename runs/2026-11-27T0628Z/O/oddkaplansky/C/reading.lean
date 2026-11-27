import Mathlib

namespace ReaderC

/-- The source's `m = binom(1200, 600)`. Not evaluated; only used as a term. -/
def readingM : ℕ := Nat.choose 1200 600

/-- The source's `p = min {h ∈ ℤ : h > 1, h ∣ (m!)^2 + 1}`, written over ℕ with `sInf`. -/
noncomputable def readingP : ℕ := sInf {h : ℕ | 1 < h ∧ h ∣ (readingM.factorial) ^ 2 + 1}

/-- The source's claim "p is an odd prime". -/
theorem reading_p_odd_prime : Nat.Prime readingP ∧ Odd readingP := by
  sorry

/-- Theorem 1.1 of oddkaplansky. -/
theorem reading_main :
    ∃ (K : Type) (_ : Field K) (G : Type) (_ : Group G),
      Nat.card K = readingP ^ 4 ∧
      Group.FG G ∧
      (∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) ∧
      ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1 := by
  sorry

end ReaderC

/-
Ambiguities and choices (comment block):
* m and p: `m` is `Nat.choose 1200 600` and `p` is `sInf` of the set {h : ℕ | 1 < h ∧ h ∣ (m!)^2 + 1}.
  The source minimises over h in ℤ with h > 1. Since (m!)^2 + 1 > 0, the divisors that are > 1 are
  positive naturals, so the set is the same and the min is over ℕ.
  `sInf` is used instead of `Nat.find`, because `Nat.find` needs an existence proof the source does
  not supply. If the set were empty, `sInf` would give 0, which is not prime, so
  `reading_p_odd_prime` would be false rather than silently true.
  Nothing is evaluated.
* "specified": the source calls K, G, a, b "specified". That is informal and not captured in Lean.
  I read each as existence of a witness. The construction is not formalised.
* "a field K of order p^4": `Nat.card K = readingP ^ 4`. This also forces K to be finite,
  since a card of 0 would not equal p^4 (p is nonzero).
* "a finitely generated group G containing torsion": `Group.FG G`, plus a non-identity element of
  finite order (`IsOfFinOrder g`, with `g ≠ 1`). "Containing torsion" is read as containing a
  nontrivial torsion element, because the identity is trivially torsion and would make the clause empty.
* `K[G]` is `MonoidAlgebra K G`, whose elements are finitely supported functions G →₀ K. This matches
  "finite sums c_g g". Its multiplication is the source's group-law convolution, and `1` is the group identity.
* The theorem is in `reading_main`, with `p` odd prime in `reading_p_odd_prime`.
  The `(_ : Field K)` and `(_ : Group G)` binders are local instances.
-/
