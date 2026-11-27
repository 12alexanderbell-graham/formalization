import Mathlib

/-! # Target O, family kadisonkastler: the three blind readings of run 2026-11-27T1428Z (brief 35bb25e), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Blind reading A of O55, "Strong Kadison–Kastler stability", Theorem 1.1.
-/

namespace ReaderA

universe u

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `M₁`, the closed operator-norm unit ball of a von Neumann algebra `M ⊆ B(H)`. -/
def unitBall (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ ‖x‖ ≤ 1}

/-- The Kadison–Kastler distance, eq. (kk-definition):
`d(M,N) = max { sup_{x∈M₁} inf_{y∈N₁} ‖x−y‖ , sup_{y∈N₁} inf_{x∈M₁} ‖x−y‖ }`.
All index sets are nonempty (`0 ∈ M₁, N₁`) and all values lie in `[0, 1]`
(`inf_y ‖x − y‖ ≤ ‖x − 0‖ ≤ 1`), so the real `⨆`/`⨅` are genuine sups/infs. -/
noncomputable def kkDist (M N : VonNeumannAlgebra H) : ℝ :=
  max (⨆ x : unitBall M, ⨅ y : unitBall N, ‖(x : H →L[ℂ] H) - y‖)
      (⨆ y : unitBall N, ⨅ x : unitBall M, ‖(x : H →L[ℂ] H) - y‖)

/-- Sanity check that the index sets are nonempty: `0 ∈ M₁`. -/
theorem zero_mem_unitBall (M : VonNeumannAlgebra H) : (0 : H →L[ℂ] H) ∈ unitBall M :=
  ⟨zero_mem M, by simp⟩

end

/-- Theorem 1.1 (Strong Kadison–Kastler stability). For every `ε > 0` there is `δ > 0` such
that for every complex Hilbert space `H` and all von Neumann algebras `M, N ⊆ B(H)`
(unital with identity `I_H`) with `d(M,N) < δ`, there is a unitary `u ∈ B(H)` with
`u M u* = N` and `‖u − I_H‖ < ε`. -/
theorem reading_strong_kadison_kastler :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M N : VonNeumannAlgebra H), kkDist M N < δ →
        ∃ u ∈ unitary (H →L[ℂ] H),
          (fun x => u * x * star u) '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H)) ∧
          ‖u - 1‖ < ε := sorry

end ReaderA

/-!
Ambiguities and choices.

1. "Von Neumann algebra M ⊆ B(H), unital with identity I_H": Mathlib's concrete
   `VonNeumannAlgebra H` (a ⋆-subalgebra of `H →L[ℂ] H` equal to its double commutant). It
   extends `StarSubalgebra`, so it automatically contains `1 = I_H`; this matches "unital with
   identity I_H" (no non-unital/degenerate algebras allowed).
2. "Complex Hilbert space": `NormedAddCommGroup H`, `InnerProductSpace ℂ H`, `CompleteSpace H`.
   The text stresses uniformity over all Hilbert spaces of all cardinalities: `δ` is chosen
   before `H` (quantifier order ∀ε ∃δ ∀H ∀M N), and the statement is universe-polymorphic in
   `u` (for each universe, `δ` works for every Hilbert space in that universe). The zero
   Hilbert space is included; the claim is trivial there.
3. Kadison–Kastler distance: written literally with `⨆`/`⨅` over the subtypes `M₁`, `N₁` in
   ℝ. Junk-value check: Real `⨆`/`⨅` are junk (`0`) only for empty or unbounded families; here
   every family is nonempty (`0 ∈ M₁`, see `zero_mem_unitBall`) and bounded (inner infima lie
   in `[0, ‖x‖] ⊆ [0,1]`, bounded below by 0), so the values are the true sup/inf. The second
   term keeps the text's `‖x − y‖` with `x ∈ M₁` inside, `y ∈ N₁` outside.
4. "u M u* = N" read as equality of sets `{u x u* | x ∈ M} = N`. "Unitary u ∈ B(H)":
   `u ∈ unitary (H →L[ℂ] H)` (`u* u = u u* = 1`), with `star` the Hilbert adjoint.
   `‖u − I_H‖` is the operator norm, `I_H = 1 = id`.
5. "δ = δ(ε)": only existence of `δ` depending on `ε` is asserted (no monotonicity or explicit
   formula). Strict inequalities `d(M,N) < δ`, `‖u − I‖ < ε` as in the text.
6. No ℕ subtraction, division, or extended-valued quantities are used.
-/


namespace ReaderB

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closed operator-norm unit ball of a von Neumann algebra, as a subtype. -/
def unitBall (M : VonNeumannAlgebra H) : Type u := {x : H →L[ℂ] H // x ∈ M ∧ ‖x‖ ≤ 1}

instance (M : VonNeumannAlgebra H) : Nonempty (unitBall M) :=
  ⟨⟨0, zero_mem M, by simp⟩⟩

/-- Kadison–Kastler distance, literally the formula of the text:
max { sup_{x∈M₁} inf_{y∈N₁} ‖x−y‖ , sup_{y∈N₁} inf_{x∈M₁} ‖x−y‖ }.
All index types are nonempty (0 lies in both balls) and all values lie in [0,2], so the real
`⨆`/`⨅` are the genuine sup/inf, not junk values. -/
noncomputable def kkDist (M N : VonNeumannAlgebra H) : ℝ :=
  max (⨆ x : unitBall M, ⨅ y : unitBall N, ‖x.1 - y.1‖)
      (⨆ y : unitBall N, ⨅ x : unitBall M, ‖x.1 - y.1‖)

/-- Theorem 1.1 (for Hilbert spaces in universe `u`): δ depends only on ε. -/
theorem readingKadisonKastler (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M N : VonNeumannAlgebra H), kkDist M N < δ →
        ∃ u : unitary (H →L[ℂ] H),
          (fun x : H →L[ℂ] H => (u : H →L[ℂ] H) * x * star (u : H →L[ℂ] H)) '' (M : Set (H →L[ℂ] H))
            = (N : Set (H →L[ℂ] H)) ∧
          ‖(u : H →L[ℂ] H) - 1‖ < ε := sorry

end ReaderB

/-
Ambiguities and choices.
* "Unital von Neumann algebra with identity I_H": Mathlib's `VonNeumannAlgebra H` is a
  star-subalgebra of `H →L[ℂ] H` equal to its double commutant, so it contains 1 = I_H
  (unital is built in).
* "Every complex Hilbert space": a complete complex inner product space `H`. Lean cannot quantify
  over all universes in one statement, so H ranges over `Type u` for an arbitrary fixed universe u
  (the theorem is universe-polymorphic), with δ chosen before H. A δ uniform across universes
  would follow from universe-independence of the claim but is not literally expressible.
* Distance: sup/inf over closed unit balls written with `⨆`/`⨅` over subtypes in ℝ. These are
  nonempty (0 ∈ ball) and bounded (norms of differences ≤ 2, ≥ 0), so no junk value; no ⊤/ENNReal.
  `d(M,N) < δ` is the strict inequality of the text (not the weaker "each x has a close y").
* Conjugation: u M u* = N as equality of sets of operators, image of M under x ↦ u x u*, with
  u in `unitary (H →L[ℂ] H)` (u*u = uu* = 1). ‖u − I_H‖ < ε is operator norm.
* Both M and N must act on the same H, as in the text. Real ε, δ; no subtraction in ℕ.
-/


namespace ReaderC

/-- Commutant of a set `S` of bounded operators on `H`. -/
def commSet (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {T | ∀ x ∈ S, x * T = T * x}

/-- A von Neumann algebra on `H`: a `*`-subalgebra `M ⊆ B(H)` equal to its double commutant. -/
def IsVNA (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  commSet H (commSet H (M : Set (H →L[ℂ] H))) = (M : Set (H →L[ℂ] H))

/-- The closed operator-norm unit ball `M_1 = {x ∈ M : ‖x‖ ≤ 1}`. -/
def unitBall (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ ‖x‖ ≤ 1}

/-- Kadison–Kastler distance
`d(M,N) = max { sup_{x∈M_1} inf_{y∈N_1} ‖x-y‖ , sup_{y∈N_1} inf_{x∈M_1} ‖x-y‖ }`.
The inner infima are over nonempty sets (`0` lies in both balls) bounded below by `0`, and the
outer suprema are over nonempty sets bounded above by `2`, so `sSup`/`sInf` give the genuine
values and no junk value is produced. -/
noncomputable def kkDist (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M N : StarSubalgebra ℂ (H →L[ℂ] H)) : ℝ :=
  max
    (sSup ((fun x : H →L[ℂ] H => sInf ((fun y : H →L[ℂ] H => ‖x - y‖) '' unitBall H N))
      '' unitBall H M))
    (sSup ((fun y : H →L[ℂ] H => sInf ((fun x : H →L[ℂ] H => ‖x - y‖) '' unitBall H M))
      '' unitBall H N))

/-- Theorem 1.1 (strong Kadison–Kastler stability): for every `ε > 0` there is `δ(ε) > 0` such
that for every complex Hilbert space `H` and unital von Neumann algebras `M, N ⊆ B(H)` with
`d(M,N) < δ`, there is a unitary `u ∈ B(H)` with `u M u* = N` and `‖u - I_H‖ < ε`.
Quantifier order follows the text: `δ` depends on `ε` only. -/
theorem reading_strong_kk :
    ∀ eps : ℝ, 0 < eps →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (M N : StarSubalgebra ℂ (H →L[ℂ] H)),
          IsVNA H M → IsVNA H N →
          (1 : H →L[ℂ] H) ∈ M → (1 : H →L[ℂ] H) ∈ N →
          kkDist H M N < δ →
          ∃ u ∈ unitary (H →L[ℂ] H),
            (fun x : H →L[ℂ] H => u * x * star u) '' (M : Set (H →L[ℂ] H)) =
              (N : Set (H →L[ℂ] H)) ∧
            ‖u - (1 : H →L[ℂ] H)‖ < eps := by
  sorry

end ReaderC

/-!
## Comment block: ambiguities and choices (reader C, family O55 / Kadison–Kastler)

1. "Von Neumann algebra". Concrete: a `StarSubalgebra ℂ (B(H))` equal to its double commutant
   (`IsVNA`). Abstract W*-algebras and preduals are not covered, and the bicommutant theorem is
   not used. "Unital" is stated literally as `1 ∈ M` and `1 ∈ N`. In Mathlib a subalgebra
   contains `1` anyway, so this hypothesis is redundant but harmless.
2. Unit balls. `M_1 = {x ∈ M : ‖x‖ ≤ 1}`, with `‖·‖` the operator norm of `B(H)`.
3. The distance. I wrote the text's formula with `sSup` and `sInf` over images of unit balls.
   The sets are nonempty (`0` is in each ball), the inner infima are bounded below by `0`,
   and `‖x - y‖ ≤ 2` on the balls, so the outer suprema are bounded above by `2`. No junk
   value occurs. `kkDist` is the `max` of the two one-sided quantities.
4. Strict inequalities. `d(M,N) < δ` and `‖u - I‖ < ε` are strict, as in the text.
5. Unitary. `u ∈ unitary (B(H))`, which is `u * star u = 1 ∧ star u * u = 1` in Mathlib.
   `u M u*` is the image set `{u x u* : x ∈ M}`, and `uMu* = N` is set equality with `N`.
   `I_H` is `(1 : B(H))`.
6. Quantifier order. The text says `δ = δ(ε)`, uniform over all algebras, representations and
   Hilbert spaces. I wrote `∀ ε > 0, ∃ δ > 0, ∀ H M N, ...`, so `δ` is chosen before `H`, `M`, `N`.
7. Universe. The text says "any complex Hilbert space". I quantified over `H : Type`, a single
   universe, so Hilbert spaces in larger universes are not covered. This is a formalization
   restriction, not a choice the text makes.
8. Hilbert space instances. `H` carries `NormedAddCommGroup`, `InnerProductSpace ℂ` and
   `CompleteSpace`, i.e. a complex Hilbert space (completeness needed for adjoints in `B(H)`).
9. Junk values. No ℕ subtraction, division by zero, `⊤`, or `sSup`/`sInf` of empty or unbounded
   sets: the sets above are nonempty and bounded, as in item 3.
10. Mathlib names used: `StarSubalgebra`, `unitary`, `star`, `sSup`, `sInf`, the operator norm on
   `H →L[ℂ] H`. No Mathlib theorem bodies were used.
-/
