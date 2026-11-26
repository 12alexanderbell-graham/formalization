# Red team BB report (2 attempts, both ACCEPTED; stopped early)

Common mechanism: the closure is `∀ c, P c ↔ H[c]` where the reader helper `SecondReading.P c` has a first disjunct
that is *true by arithmetic at the headline's literals*, and a second disjunct that is the headline restated
(reordered so the "contains the headline" check does not fire). The first disjunct is `c ≥ A`, with `A` spelled as
`(0.000000001:ℝ) * ((3321992119:ℕ):ℝ)` (resp. `10^-10 * ↑12325876568`). The numeral scan (`realNumVal?`,
`numeralValues`) does not evaluate `Nat.cast`, so the value 3.321992119 is never seen as "kept", while at the literals
the disjunct is `c0 ≥ c0`. The equivalence holds for all c because `c ≥ A` implies `H[c]` by monotonicity from the
program's own headline (Gelfand: larger bound; Hiemenz: wider interval around the certified window). The bite holds
(Gelfand: radial witness lam=3.3 vs c=3; Hiemenz: a=b=0). Axioms: standard only.
The reader's own proofs (`ContDiffOn`, `Module.Finite` instance proofs abstracted as `rn._proof_n`) would make an
inline reading mismatch the theorem's statement, so `rn := P c0` is a thin def over the helper `P`; the rule unfolds
reader definitions on both sides, so this is accepted.

## Attempt 1: `redteamBB/a1_body.lean` (Gelfand)
Reading: `rn = (3.321992119 ≥ 1e-9 * ↑3321992119) ∨ (no solution has λ > 3.321992119)`.
Harness: `RESULT a1: ACCEPTED []`.
Why it is not the headline: the first disjunct is `c0 ≥ c0`, true by arithmetic, so `rn` is a tautology and says nothing
about Gelfand's problem (it is "equivalent to True", and merely logically equivalent to the headline because the
headline is a proved theorem). Any threshold at or above the certified literal gives the same trivial reading.
(First tries were REJECTED only because inlined readings contain abstracted `_proof_n` constants that differ from the
theorem's own proof terms; a spurious rejection of honest inline readings that mention `ContDiffOn`, a side finding.)

## Attempt 2: `redteamBB/a2_body.lean` (Hiemenz, two literals)
Reading: `rn = (1.2325876568 ≤ 1e-10*↑12325876568 ∧ 1e-10*↑12325876569 ≤ 1.2325876569) ∨ (a solution has wall value in the window, restated)`.
Harness: `RESULT a2: ACCEPTED []`.
Why it is not the headline: the first disjunct is `a0 ≤ a0 ∧ b0 ≤ b0`, true by arithmetic, so the reading is a tautology
and asserts no existence of any boundary-value solution.

## Gaps in the rule
1. `Nat.cast` of a natural literal (and other non-listed numeral forms) is invisible to `realNumVal?`, so the value of
   a literal can be re-spelled and kept in the reading ("keeps a numeral" check bypassed).
2. `∀ c, X c ↔ H[c]` only forces X to be equivalent to H, not to be non-trivial at c0: a disjunct `c ≥ A` that implies
   `H[c]` by monotonicity from the program's own theorem is provable for all c and trivial at the literals.
3. Reader helper defs are unfolded without being checked, so a `def P` hides any content.
