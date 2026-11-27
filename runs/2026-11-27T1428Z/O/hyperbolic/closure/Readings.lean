import Mathlib

/-! # Target O, family hyperbolic: the three blind readings of run 2026-11-27T1428Z (brief 44efa61), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Reader A, family O52 (hyperbolic): Theorem 1.1 and the last sentence of Corollary 1.2 of
"A torsion-free hyperbolic group that is neither residually finite nor linear", read from
paper.tex lines 48-74 only.
-/

namespace ReaderA

/-- Torsion-free: no nonidentity element has finite order. -/
def IsTorsionFree (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1

/-- Residually finite: each nonidentity element has a nonidentity image under a homomorphism
to some finite group. -/
def IsResiduallyFinite (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ (F : Type) (_ : Group F) (_ : Finite F) (φ : G →* F), φ g ≠ 1

/-- The (undirected) Cayley graph of `G` with respect to `S`: `g ~ h` iff `g ≠ h` and
`h = g s` or `g = h s` for some `s ∈ S`. -/
def cayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G where
  Adj g h := g ≠ h ∧ (g⁻¹ * h ∈ S ∨ h⁻¹ * g ∈ S)
  symm := ⟨fun _ _ ⟨hne, hs⟩ => ⟨hne.symm, hs.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- `γ 0, γ 1, …, γ n` is a geodesic of the graph `Γ`: consecutive vertices are adjacent, and
no walk between the endpoints is shorter than `n`. -/
def IsGeodesic {V : Type*} (Γ : SimpleGraph V) (γ : ℕ → V) (n : ℕ) : Prop :=
  (∀ i < n, Γ.Adj (γ i) (γ (i + 1))) ∧ ∀ w : Γ.Walk (γ 0) (γ n), n ≤ w.length

/-- `u` is within graph distance `δ` of `v` (there is a walk of length at most `δ`). -/
def WithinDist {V : Type*} (Γ : SimpleGraph V) (u v : V) (δ : ℕ) : Prop :=
  ∃ w : Γ.Walk u v, w.length ≤ δ

/-- Uniformly thin geodesic triangles: there is a constant `δ` such that for every geodesic
triangle (sides `γ₁ : x → y`, `γ₂ : y → z`, `γ₃ : z → x`), every point of one side is within
`δ` of the union of the other two sides. Quantifying over all triangles and all cyclic labellings
covers every side. -/
def HasUniformlyThinTriangles {V : Type*} (Γ : SimpleGraph V) : Prop :=
  ∃ δ : ℕ, ∀ (γ₁ γ₂ γ₃ : ℕ → V) (n₁ n₂ n₃ : ℕ),
    IsGeodesic Γ γ₁ n₁ → IsGeodesic Γ γ₂ n₂ → IsGeodesic Γ γ₃ n₃ →
    γ₁ n₁ = γ₂ 0 → γ₂ n₂ = γ₃ 0 → γ₃ n₃ = γ₁ 0 →
    ∀ i ≤ n₁, ∃ j : ℕ,
      (j ≤ n₂ ∧ WithinDist Γ (γ₁ i) (γ₂ j) δ) ∨ (j ≤ n₃ ∧ WithinDist Γ (γ₁ i) (γ₃ j) δ)

/-- Word-hyperbolic: `G` is finitely generated, and the Cayley graph with respect to some finite
generating set has uniformly thin geodesic triangles. -/
def IsWordHyperbolic (G : Type*) [Group G] : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.closure S = ⊤ ∧ HasUniformlyThinTriangles (cayleyGraph S)

/-- Linear over the (commutative) field `K`: an injective homomorphism into `GL_n(K)` for some
finite `n ≥ 1`. -/
def IsLinearOver (G : Type*) [Group G] (K : Type*) [Field K] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) K, Function.Injective ρ

/-- Theorem 1.1. There exists a torsion-free word-hyperbolic group that is not residually
finite. -/
theorem readingHyperbolicMain :
    ∃ (G : Type) (_ : Group G),
      IsTorsionFree G ∧ IsWordHyperbolic G ∧ ¬ IsResiduallyFinite G := sorry

/-- Theorem 1.1 conjoined with the last sentence of Corollary 1.2 for the same group: there is a
torsion-free word-hyperbolic group that is not residually finite and is not linear over any
commutative field. -/
theorem readingHyperbolicNotLinear.{u} :
    ∃ (G : Type) (_ : Group G),
      IsTorsionFree G ∧ IsWordHyperbolic G ∧ ¬ IsResiduallyFinite G ∧
        ∀ (K : Type u) [Field K], ¬ IsLinearOver G K := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Residual finiteness: literally the source's first definition (each `g ≠ 1` survives in some
   finite quotient). Finite targets are taken in `Type`; every finite group is isomorphic to one
   in `Type` (e.g. on `Fin m`), so no generality is lost. The equivalent "finite residual is
   trivial" formulation is not used.

2. Torsion-free: written by hand as "no nontrivial element has a positive power equal to 1"
   (equivalent to Mathlib's `Monoid.IsTorsionFree`).

3. Word-hyperbolic. Mathlib has no hyperbolic groups, so I wrote the source's definition:
   "a finitely generated group is word-hyperbolic if a Cayley graph has uniformly thin geodesic
   triangles". Choices:
   - "A Cayley graph": with respect to SOME finite generating set `S` (`S.Finite`,
     `Subgroup.closure S = ⊤`); finite generation is thus built in. Edges `g — g s` for
     `s ∈ S ∪ S⁻¹` (identity loops dropped).
   - Points of a side are its VERTICES and distance is graph distance between vertices, rather
     than points of the metric graph with edges of length 1. Every point of an edge is within 1/2
     of a vertex, so the two notions of thinness agree up to changing the constant by at most 1:
     the property "there is a constant" is unaffected.
   - Geodesics are discrete: `γ : ℕ → G` on `0..n` with adjacent consecutive vertices and no
     shorter walk between endpoints (so every subsegment is also geodesic); values of `γ` beyond
     `n` are irrelevant.
   - Distances are expressed as "there is a walk of length ≤ δ" and "every walk has length ≥ n",
     avoiding `SimpleGraph.dist` (junk `0` between disconnected vertices) and `edist` (`⊤` in
     ℕ∞). The graph is connected anyway, since `S` generates.
   - "Within that distance of the other two sides" = within `δ` of some point of the union of the
     other two sides. Requiring it for side 1 of every triangle under every cyclic labelling
     covers all sides. `δ : ℕ` suffices (round up a real constant). `δ` is chosen before the
     triangle: uniform.

4. Linear over a commutative field K: Mathlib's `Field` is commutative. `GL_n(K)` is
   `Matrix.GeneralLinearGroup (Fin n) K`, with `n ≥ 1` as in the source. "Not linear over any
   commutative field" quantifies over all fields in an arbitrary universe `u` (the theorem is
   universe-polymorphic in `u`).

5. "The same group": the second theorem conjoins all properties of Theorem 1.1 with
   non-linearity under a single existential, as the brief asks. The stronger corollary statement
   `R_f(G) ⊆ ker ρ` is NOT formalized; only its last sentence.

6. No junk values: no ℕ subtraction (the geodesic condition uses `n ≤ w.length`), no division,
   no sSup/sInf, no ℕ∞.
-/


namespace ReaderB

universe u

/-- `G` is residually finite: every nonidentity element has a nonidentity image under a
homomorphism to some finite group. -/
def ResFinite (G : Type) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ (H : Type) (_ : Group H) (_ : Finite H) (φ : G →* H), φ g ≠ 1

section Hyperbolic
variable {G : Type} [Group G]

/-- `p` is a path of length `n` in the Cayley graph of `G` for generating set `S`
(vertices only): consecutive vertices differ by right multiplication by a generator or its
inverse. -/
def IsPath (S : Set G) (n : ℕ) (p : ℕ → G) : Prop :=
  ∀ i, i < n → (p i)⁻¹ * p (i + 1) ∈ S ∨ ((p i)⁻¹ * p (i + 1))⁻¹ ∈ S

/-- `p` (of length `n`) is a geodesic: no path between its endpoints is shorter. -/
def IsGeodesic (S : Set G) (n : ℕ) (p : ℕ → G) : Prop :=
  IsPath S n p ∧ ∀ (m : ℕ) (q : ℕ → G), IsPath S m q → q 0 = p 0 → q m = p n → n ≤ m

/-- The distance from `u` to `v` is at most `δ`. -/
def DistLE (S : Set G) (δ : ℕ) (u v : G) : Prop :=
  ∃ (m : ℕ) (q : ℕ → G), m ≤ δ ∧ IsPath S m q ∧ q 0 = u ∧ q m = v

/-- Geodesic triangles are `δ`-thin: for geodesic sides `a : x → y` (length `la`),
`b : y → z` (length `lb`), `c : z → x` (length `lc`), every point of `a` is within `δ`
of a point of `b` and within `δ` of a point of `c`. (All three sides are covered by
quantifying over all triangles.) -/
def ThinTriangles (S : Set G) (δ : ℕ) : Prop :=
  ∀ (la lb lc : ℕ) (a b c : ℕ → G),
    IsGeodesic S la a → IsGeodesic S lb b → IsGeodesic S lc c →
    a la = b 0 → b lb = c 0 → c lc = a 0 →
    ∀ i, i ≤ la →
      (∃ j, j ≤ lb ∧ DistLE S δ (a i) (b j)) ∧ (∃ j, j ≤ lc ∧ DistLE S δ (a i) (c j))

/-- A finitely generated group is word-hyperbolic if some Cayley graph (w.r.t. a finite
generating set) has uniformly thin geodesic triangles. -/
def WordHyperbolic (G : Type) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ ∃ δ : ℕ, ThinTriangles (S : Set G) δ

end Hyperbolic

/-- Torsion-free: no nonidentity element has finite order. -/
def TorsionFree (G : Type) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g

/-- Theorem 1.1. -/
theorem reading_hyperbolic_main :
    ∃ (G : Type) (_ : Group G), TorsionFree G ∧ WordHyperbolic G ∧ ¬ ResFinite G :=
  sorry

/-- Corollary 1.2 (last sentence), for the same group as Theorem 1.1: not linear over any
commutative field (no injective homomorphism into `GL_n(K)`, any `n ≥ 1`). -/
theorem reading_hyperbolic_nonlinear :
    ∃ (G : Type) (_ : Group G), (TorsionFree G ∧ WordHyperbolic G ∧ ¬ ResFinite G) ∧
      ∀ (K : Type u) (_ : Field K) (n : ℕ), 1 ≤ n →
        ¬ ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) K, Function.Injective ρ :=
  sorry

/-! ## Comments: ambiguities and choices

* Residual finiteness: written literally (each `g ≠ 1` survives in some finite quotient
  `H`), `H : Type` (same universe as `G`, harmless since finite images can be taken in
  `Type`). Own definition, not Mathlib's `Group.ResiduallyFinite`.
* Word-hyperbolic: "some Cayley graph is δ-thin". Existential over finite generating sets
  `S` (equivalent to "all" by a standard theorem). Cayley graph is modelled by its
  vertex set `G`, with edges `g — g s`, `s ∈ S ∪ S⁻¹`; paths/geodesics are sequences
  `ℕ → G` of length `n` (values beyond `n` are ignored). Geodesic = no shorter path with
  the same endpoints (this avoids `sInf` of word length). "Point of a side" is restricted
  to vertices, and "within the distance" is the graph distance between vertices; this is
  equivalent to the continuous formulation up to changing the constant by 1/2. The constant
  `δ` is a natural number, so no real-valued junk. Thinness is stated for one side
  against the other two; quantifying over all triangles with all labellings covers each
  side. Degenerate triangles are included (they are allowed in the definition).
* Group universe: `G : Type`. Finite generation is part of `WordHyperbolic`.
* Torsion-free: own definition (no nonidentity element has finite order, `IsOfFinOrder`); Mathlib's `IsMulTorsionFree` is a different notion.
* Linearity: `ρ : G →* GL (Fin n) K` injective, `n ≥ 1` (stated explicitly, though `n=0`
  would only make `GL` trivial), `K` any field (commutative) in an arbitrary universe `u`
  (the theorem is universe polymorphic). Corollary's quantifier "the group constructed in
  Theorem 1.1" is rendered by existentially quantifying one `G` carrying all properties of
  Theorem 1.1 together with non-linearity.
-/

end ReaderB


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
