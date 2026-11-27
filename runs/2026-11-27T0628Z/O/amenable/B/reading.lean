import Mathlib

open Classical

/-- Amenable as in the source (Følner condition): for every finite K and ε > 0 there is a nonempty
finite D with |gD Δ D| < ε |D| for all g ∈ K. Left translation gD = {g * x | x ∈ D}. -/
def IsAmenableFolner (G : Type) [Group G] : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ D : Finset G, D.Nonempty ∧
      ∀ g ∈ K, ((symmDiff (D.image (fun x => g * x)) D).card : ℝ) < ε * (D.card : ℝ)

/-- Finitely presented: G ≅ F(S) / ⟪⟪R⟫⟫ for finite S and finite R ⊆ F(S). -/
def IsFinitelyPresentedGroup (G : Type) [Group G] : Prop :=
  ∃ (S : Type) (_ : Fintype S) (R : Finset (FreeGroup S)),
    Nonempty (G ≃* (FreeGroup S ⧸ Subgroup.normalClosure (R : Set (FreeGroup S))))

theorem reading :
    ∃ (G : Type) (_ : Group G),
      Infinite G ∧ IsFinitelyPresentedGroup G ∧ IsSimpleGroup G ∧ IsAmenableFolner G := sorry

/-
Ambiguities and choices.
* Amenability: defined by the Følner condition given in the source, not Mathlib's notion; D ranges
  over `Finset G`, K over `Finset G`, ε real > 0, strict inequality, symmetric difference
  `symmDiff` of finsets, gD as image under left multiplication (only left is stated in source).
  With K empty it is trivially satisfied by D nonempty; no junk issue.
* Simple: Mathlib `IsSimpleGroup` (nontrivial, only normal subgroups ⊥ and ⊤). The source's wording
  "only trivial and G" would allow the trivial group, but infiniteness excludes it anyway.
* Finitely presented: finite generating type S (Fintype), finite set of relators R in the free group
  (the "relator words"), iso (MulEquiv) with the quotient by the normal closure. Source says
  "finite sets of generators S and relator words R": R taken as a subset of F(S).
* "Discrete group": no topology; plain `Group`.
* Infinite: `Infinite G`. Universe fixed at Type (0); G is countable anyway as f.p.
-/
