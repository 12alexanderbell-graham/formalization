import Mathlib

namespace ReaderC

noncomputable section

/-- Word length of `g` with respect to a finite set `S` of group elements: the least length of a
word in `S ∪ S⁻¹` representing `g`. This is meaningful when `S` generates `G` (see
`IsWordHyperbolic`, where generation is part of the definition, so no `sInf ∅ = 0` junk is used). -/
def wordLen {G : Type} [Group G] (S : Finset G) (g : G) : ℕ :=
  sInf {n | ∃ l : List G, l.length = n ∧ (∀ x ∈ l, x ∈ S ∨ x⁻¹ ∈ S) ∧ l.prod = g}

/-- Word metric on the Cayley graph of `G` with respect to `S`. -/
def dW {G : Type} [Group G] (S : Finset G) (p q : G) : ℕ :=
  wordLen S (p⁻¹ * q)

/-- `a : ℕ → G` restricted to `[0, n]` is a geodesic from `x` to `y` in the Cayley graph: its
endpoints are `x` and `y`, and `d(a i, a j) = |i - j|` for `i, j ≤ n`. -/
def IsGeodesic {G : Type} [Group G] (S : Finset G) (x y : G) (n : ℕ) (a : ℕ → G) : Prop :=
  a 0 = x ∧ a n = y ∧
    ∀ i ≤ n, ∀ j ≤ n, ((dW S (a i) (a j) : ℕ) : ℤ) = |(i : ℤ) - (j : ℤ)|

/-- The vertex `p` lies within `δ` of some vertex of the side `b` on `[0, m]`. -/
def Near {G : Type} [Group G] (S : Finset G) (p : G) (b : ℕ → G) (m δ : ℕ) : Prop :=
  ∃ j ≤ m, dW S p (b j) ≤ δ

/-- `G` is word-hyperbolic: there is a finite generating set `S` and a constant `δ` such that for every
geodesic triangle (sides `a : x → y`, `b : y → z`, `c : z → x`) every vertex of each side lies within
`δ` of a vertex of one of the other two sides. -/
def IsWordHyperbolic (G : Type) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧
    ∃ δ : ℕ, ∀ (x y z : G) (n₁ n₂ n₃ : ℕ) (a b c : ℕ → G),
      IsGeodesic S x y n₁ a → IsGeodesic S y z n₂ b → IsGeodesic S z x n₃ c →
      (∀ i ≤ n₁, Near S (a i) b n₂ δ ∨ Near S (a i) c n₃ δ) ∧
      (∀ j ≤ n₂, Near S (b j) a n₁ δ ∨ Near S (b j) c n₃ δ) ∧
      (∀ k ≤ n₃, Near S (c k) a n₁ δ ∨ Near S (c k) b n₂ δ)

/-- `G` is torsion-free: no nontrivial element has finite order. -/
def IsTorsionFree (G : Type) [Group G] : Prop :=
  ∀ g : G, ∀ n : ℕ, 0 < n → g ^ n = 1 → g = 1

/-- `G` is residually finite: every nonidentity element has nonidentity image under some
homomorphism to a finite group. -/
def IsResFinite (G : Type) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (φ : G →* Q), φ g ≠ 1

/-- `G` is linear over the commutative field `K`: there is an injective homomorphism into
`GL_n(K)` for some finite `n ≥ 1`. -/
def IsLinearOver (K : Type) [Field K] (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) K, Function.Injective ρ

/-- Theorem 1.1 together with the corollary's last sentence, for one and the same group `G`:
there is a torsion-free word-hyperbolic group that is not residually finite, and it is not linear over
any commutative field. -/
theorem reading_hyperbolic :
    ∃ (G : Type) (_ : Group G),
      (IsTorsionFree G ∧ IsWordHyperbolic G ∧ ¬ IsResFinite G) ∧
      (∀ (K : Type) (_ : Field K), ¬ IsLinearOver K G) := sorry

end

end ReaderC

/-
Comment block (blind reading C, family O52, source
`hyperbolic/sources/abstract_and_introduction_lines48-74.tex` only).

Modelling choices and ambiguities, all my decisions:

* Groups are `G : Type` with a `Group G` instance. Torsion-free is defined directly: `g^n = 1` with
  `n > 0` forces `g = 1`. Mathlib's own name for this notion is not used, so the statement is literal.
* Finitely generated: part of `IsWordHyperbolic`. There is a `Finset S` with `closure S = ⊤`. Word
  hyperbolicity is defined relative to such an `S`, and the statement says "for some finite generating
  set", the standard definition, which is independent of the choice up to a change of constant.
* Word length `wordLen S g` is the least length of a word in `S ∪ S⁻¹` representing `g`. This is an
  `sInf` over a nonempty set, since `S` generates and the set is nonempty for every `g` in `G`. So no
  junk `0` arises from the `sInf ∅` convention.
* Word metric `dW S p q = |p⁻¹ q|_S`. A geodesic segment of length `n` is a map `a : ℕ → G` on `[0,n]`
  with `a 0 = x`, `a n = y` and `d(a i, a j) = |i - j|`. Values outside `[0,n]` are never used, so
  their junk values are irrelevant. Lengths are compared in `ℤ` via a cast, which avoids ℕ subtraction.
* Geodesic triangles and thinness: I use the vertex version of Gromov's thin-triangle condition. Each
  vertex of each side lies within `δ` of a vertex of one of the other two sides. This is equivalent to
  the usual point-version up to a change of constant `δ` (a standard fact). It is a choice of mine, since
  the source only says "uniformly thin geodesic triangles". The phrase "every point of one side is within
  that distance of the other two sides" is read as "within `δ` of the union of the other two sides",
  with the sides' vertices used as the points.
* "Thin" is stated for all three sides, with the conjunction over the three sides and both alternatives
  in each disjunction, giving the symmetric reading "within the other two sides".
* `IsResFinite G` is: each `g ≠ 1` has an image `φ g ≠ 1` under a hom `φ : G →* Q` to a finite group
  `Q : Type`. This is the source's definition. Equivalently the finite residual is trivial. I did not
  define the finite residual `R_f(G)` separately, since the source's first definition suffices.
* Non residual finiteness is `¬ IsResFinite G`. The statement is ` ¬ ∀ g ≠ 1, ∃ finite-quotient image`,
  exactly as in the source.
* `IsLinearOver K G`: there is `n ≥ 1` and an injective homomorphism `G →* GL_n(K)`, where
  `Matrix.GeneralLinearGroup (Fin n) K` is Mathlib's `GL_n(K)`. `K` is a `Field`, hence a commutative
  field. "Commutative field" is read as a `Field` in Lean. Quantification over all fields `K : Type` is
  the "any commutative field" reading.
* Theorem 1.1 and the corollary's last sentence are stated for the same group, conjoined inside one
  `∃ G`. The corollary's stronger content (the finite residual lies in every kernel) is not included,
  because the brief asks only for the last sentence. That sentence is "`G` is not linear over any
  commutative field".
* The file has `import Mathlib` only and is wrapped in `namespace ReaderC`. The one theorem is `sorry`.
-/
