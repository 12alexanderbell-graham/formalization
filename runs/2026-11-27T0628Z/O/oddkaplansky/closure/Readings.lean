import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

namespace ReaderA

/-- `m = binom(1200, 600)`, kept symbolic (never evaluated). -/
def m : ℕ := Nat.choose 1200 600

/-- For every `k`, some `h > 1` divides `(k!)^2 + 1` (namely that number itself), so the
minimum exists. Stated for general `k` so that nothing about the huge `m` is ever reduced. -/
theorem exists_divisor_gt_one (k : ℕ) : ∃ h : ℕ, 1 < h ∧ h ∣ (Nat.factorial k) ^ 2 + 1 :=
  ⟨(Nat.factorial k) ^ 2 + 1,
    Nat.lt_add_of_pos_left (pow_pos (Nat.factorial_pos k) 2), dvd_refl _⟩

/-- `min {h : h > 1, h ∣ (k!)^2 + 1}` (via `Nat.find`; no junk value). -/
def leastDivisor (k : ℕ) : ℕ := Nat.find (exists_divisor_gt_one k)

/-- `p = min {h ∈ ℤ : h > 1, h ∣ (m!)^2 + 1}`. Any integer `h > 1` is a natural number,
and divisibility of naturals agrees in `ℕ` and `ℤ`, so we take the minimum over `ℕ`. -/
def p : ℕ := leastDivisor m

/-- The integer version of the defining set of `p`, stated literally over `ℤ`. -/
def pSetInt : Set ℤ := {h : ℤ | 1 < h ∧ h ∣ ((Nat.factorial m : ℤ) ^ 2 + 1)}

/-- A group "contains torsion": it has a non-identity element of finite order. -/
def HasTorsion (G : Type) [Group G] : Prop := ∃ g : G, g ≠ 1 ∧ IsOfFinOrder g

/-- Theorem 1.1. `p` is an odd prime, and there are a field `K` of order `p^4`,
a finitely generated group `G` containing torsion, and `a, b ∈ K[G]` with `ab = 1`, `ba ≠ 1`.
The integer-set characterisation of `p` is included as a conjunct so that the reading of
`p` as a minimum over `ℤ` is part of what is asserted. -/
theorem reading_main :
    IsLeast pSetInt (p : ℤ) ∧
    Nat.Prime p ∧ Odd p ∧
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = p ^ 4 ∧
    ∃ (G : Type) (_ : Group G), Group.FG G ∧ HasTorsion G ∧
    ∃ a b : MonoidAlgebra K G, a * b = 1 ∧ b * a ≠ 1 := sorry

end ReaderA

/-
Ambiguities and choices (reader A):

1. "Specified" field / group / finite sums: read as plain existence (∃). The word
   presumably means the paper writes them down explicitly; explicitness is not a
   mathematical property expressible in the statement, so it is dropped. The existential
   statement is what any explicit construction proves.
2. `p = min{h ∈ ℤ : h > 1, h ∣ (m!)^2+1}`: defined with `Nat.find` over ℕ (the integers
   `> 1` are exactly the naturals `> 1`), with a proved existence witness, so no junk value.
   The literal ℤ formulation `IsLeast pSetInt (p : ℤ)` is included as a conjunct of the
   theorem (true by construction, but it ties the reading to the source's ℤ definition).
   `m` and `p` are never evaluated. (A first version with `N := (m!)^2+1` as a closed
   definition and a closed existence proof made Lean try to reduce the huge numeral and
   run out of memory; the existence lemma and `leastDivisor` are therefore stated for a
   general `k` and instantiated at `m`. Same mathematical content.)
3. "Odd prime": `Nat.Prime p ∧ Odd p`.
4. "Field K of order p^4": a finite field (`Fintype K`) with `Fintype.card K = p ^ 4`;
   universe level fixed to `Type`.
5. "Finitely generated group containing torsion": `Group.FG G` and existence of an element
   `g ≠ 1` of finite order (`IsOfFinOrder 1` holds trivially, hence `g ≠ 1`).
6. `K[G]`: Mathlib's `MonoidAlgebra K G` (finitely supported functions `G → K` with
   convolution product), which is exactly "finite sums Σ c_g g multiplied by the group law
   and bilinearity". "Finite sums" is automatic.
7. `ab = 1` and `ba ≠ 1` use the unit `1 = single 1 1` of the group algebra.
8. The definitions of directly/stably finite in the text are background, not part of
   Theorem 1.1; not formalized.
-/

-- ===== reader B =====

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

-- ===== reader C =====

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
