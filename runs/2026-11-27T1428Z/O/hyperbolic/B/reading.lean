import Mathlib

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
