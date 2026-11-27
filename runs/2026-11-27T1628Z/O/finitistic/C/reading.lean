import Mathlib

/-
Blind reading C, target O, family O58 "An algebra of infinite little finitistic dimension".
Source read: abstract and 01-introduction.tex lines 1-112 only.
-/

namespace ReaderC

/-- A finite free resolution of length n of the left A-module M: an exact sequence
0 → P_n → ⋯ → P_0 → M → 0 with P_i = ⊕_{ι i} A free, d i : P_{i+1} → P_i, and e : P_0 → M
surjective, with ker e = im d_0, ker d_i = im d_{i+1}, and P_i = 0 for i > n. -/
def freeResLength (A : Type) [Ring A] (M : Type) [AddCommGroup M] [Module A M] (n : ℕ) : Prop :=
  ∃ (ι : ℕ → Type) (d : ∀ i, (ι (i + 1) →₀ A) →ₗ[A] (ι i →₀ A))
    (e : (ι 0 →₀ A) →ₗ[A] M),
    Function.Surjective e ∧
    LinearMap.ker e = LinearMap.range (d 0) ∧
    (∀ i, LinearMap.ker (d i) = LinearMap.range (d (i + 1))) ∧
    (∀ i, n < i → ∀ x : ι i →₀ A, x = 0)

/-- Projective dimension pd_A M ∈ ℕ∞: the infimum of the lengths n of finite resolutions.
If no finite resolution exists the infimum over the empty set is ⊤ = ∞, which is the
text's "pd = ∞". -/
noncomputable def pdFree (A : Type) [Ring A] (M : Type) [AddCommGroup M] [Module A M] : ℕ∞ :=
  ⨅ (n : ℕ) (_ : freeResLength A M n), (n : ℕ∞)

/-- Little finitistic dimension findim A: the supremum of pd_A N over finitely generated left
A-modules N with pd_A N < ∞. The set is nonempty (A itself, pd 0), so the supremum is
genuine; an unbounded set has supremum ⊤ in ℕ∞, which is the text's ∞. -/
noncomputable def findim (A : Type) [Ring A] : ℕ∞ :=
  sSup {x : ℕ∞ | ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N),
    Module.Finite A N ∧ pdFree A N < ⊤ ∧ x = pdFree A N}

/-- Big finitistic dimension Findim A: as findim, over all left A-modules N with pd_A N < ∞. -/
noncomputable def Findim (A : Type) [Ring A] : ℕ∞ :=
  sSup {x : ℕ∞ | ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N),
    pdFree A N < ⊤ ∧ x = pdFree A N}

/-- Theorem 1.1. There is a finite-dimensional unital complex algebra A such that for every
integer m ≥ 1 there is a finite-dimensional left A-module N_m with 2m - 2 ≤ pd_A N_m < ∞
(written 2m ≤ pd_A N_m + 2 to avoid ℕ subtraction). In particular findim A = ∞. -/
theorem reading_O58_thm1 :
    ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A), FiniteDimensional ℂ A ∧
      (∀ m : ℕ, 1 ≤ m →
        ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module ℂ N)
          (_ : IsScalarTower ℂ A N),
          FiniteDimensional ℂ N ∧
          (2 * (m : ℕ∞)) ≤ pdFree A N + 2 ∧ pdFree A N < ⊤) ∧
      findim A = ⊤ := by
  sorry

/-- Corollary 1.2. There is a finite-dimensional unital complex algebra Λ with
findim Λ = Findim Λ = ∞ and findim Λ^op = Findim Λ^op = 0 (all left modules, Λ^op-left modules
being right Λ-modules). The two injective-generation sentences are NOT formalized; see the
comment block. -/
theorem reading_O58_cor2 :
    ∃ (Λ : Type) (_ : Ring Λ) (_ : Algebra ℂ Λ), FiniteDimensional ℂ Λ ∧
      findim Λ = ⊤ ∧ Findim Λ = ⊤ ∧
      findim Λᵐᵒᵖ = 0 ∧ Findim Λᵐᵒᵖ = 0 := by
  sorry

end ReaderC

/-
## Comment block: ambiguities and choices (reader C, O58)

1. Projective dimension. The text's pd uses projective resolutions. I define it with free
   resolutions indexed by ι : ℕ → Type, i.e. modules P_i = ⊕_{ι i} A. For a finite resolution,
   pd is the least length, which equals the projective-resolution notion by the standard
   Eilenberg-swindle replacement of projectives by free modules. I did not prove this equivalence;
   it is a choice of definition, flagged here. Projective dimension is ⊤ if no finite
   resolution exists.

2. Universes and types. Modules are taken in Type; ι i and A are Type. Finitely generated means
   Module.Finite A N; finite-dimensional means FiniteDimensional ℂ (ℂ acting through
   IsScalarTower ℂ A N).

3. ℕ∞ and ⊤. The brief asks to avoid ⊤ in ℕ∞-valued quantities. Here ⊤ is not a junk value:
   (a) pd_A N = ⊤ as an infimum over the empty set means "no finite resolution" (the text's ∞);
   (b) findim and Findim are suprema over nonempty sets in the complete lattice ℕ∞, so the
   supremum is ⊤ exactly when the set is unbounded (the text's "fin.dim = ∞"). The comparisons
   "pd < ⊤" express "pd < ∞". The quantity 2m - 2 is written 2m ≤ pd + 2 in ℕ∞, which
   coincides with 2m - 2 ≤ pd for m ≥ 1 and finite pd. No ℕ subtraction appears.

4. Theorem 1.1 quantifiers. "There is a finite-dimensional unital complex algebra A such that for
   every m ≥ 1 there is N_m" is read with A fixed before m (the existential over A is outside the
   ∀ m). N_m is finite-dimensional as a complex vector space, with ℂ acting through A.

5. Big versus little. findim uses only finitely generated N; Findim uses all N with finite pd.
   Both are over left modules. Little ≤ big, so the Findim claim in Cor 1.2 is consistent.

6. Corollary 1.2. Λ is finite-dimensional unital over ℂ. The opposite algebra is Λᵐᵒᵖ with its
   Ring instance; findim Λᵐᵒᵖ and Findim Λᵐᵒᵖ use left Λᵐᵒᵖ-modules, i.e. right Λ-modules, as
   the text says ("All four dimensions here use left modules" for Λ^op). The four values are
   ⊤, ⊤, 0, 0.

7. NOT FORMALIZED: the two injective-generation sentences of Corollary 1.2 (injective left
   Λ-modules do not generate the unbounded derived category of all left Λ-modules; injective
   right Λ-modules generate the unbounded derived category of all right Λ-modules). Reason:
   generation requires the unbounded derived category of all modules, the smallest triangulated
   subcategory closed under arbitrary coproducts, and its closure properties; I did not find a
   usable Mathlib counterpart for the unbounded derived category of all modules and did not
   define one from the text. I did not attempt a partial definition.

8. Not formalized as separate claims: Rickard's theorem and the Cummings/Huisgen-Zimmermann/Igusa-Todorov
   background; the companion characteristic-two algebra; the prose "extreme left-right asymmetry" beyond
   the displayed equalities in Cor 1.2 (which are formalized).

9. Avoided: ℕ subtraction; sSup/sInf of sets I did not check nonempty (both findim sets contain
   pd of A or of any projective-type module, handled as above: findim's set contains pd A for A itself
   as a f.g. free module with pd 0 — the Findim set is nonempty for the same reason); tsum/tprod;
   Nat.nth.

Status: the file is written; compile status is reported in the handback.
-/
