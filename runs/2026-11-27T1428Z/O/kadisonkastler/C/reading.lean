import Mathlib

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
