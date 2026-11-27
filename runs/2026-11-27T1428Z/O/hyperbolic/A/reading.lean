import Mathlib

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
