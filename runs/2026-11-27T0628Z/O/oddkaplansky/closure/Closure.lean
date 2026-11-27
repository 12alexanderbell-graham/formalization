import Mathlib
import Readings.OddKaplansky
import ComparatorChallenges.OddKaplansky

/-! # Target O, family O35 (Kaplansky's direct finiteness conjecture in odd characteristic): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped: `MainClaim` — with m = C(1200, 600)
and p = `Nat.minFac ((m!)² + 1)` (both `@[irreducible]`, never evaluated), p is an odd prime and there are a finite
field K of characteristic p with p⁴ elements, a finitely generated group G with a nontrivial torsion element, and
a, b ∈ K[G] with ab = 1, ba ≠ 1 (and more). Each reader's p — `Nat.find` (A), `sInf` (B, C) of the divisors > 1 of
(m!)² + 1, and A's least-integer form — is proved equal to `minFac` for every n ≥ 2, without evaluating anything.
Closed (frozen ⇒ reading): every reader. -/

namespace TargetO.OddKaplansky

theorem sInf_eq (n : ℕ) (hn : 2 ≤ n) : sInf {h : ℕ | 1 < h ∧ h ∣ n} = Nat.minFac n := by
  have hmin : Nat.minFac n ∈ {h : ℕ | 1 < h ∧ h ∣ n} :=
    ⟨(Nat.minFac_prime (by omega)).one_lt, Nat.minFac_dvd n⟩
  apply le_antisymm (Nat.sInf_le hmin)
  refine le_csInf ⟨_, hmin⟩ fun h hh => Nat.minFac_le_of_dvd hh.1 hh.2

theorem find_eq (k : ℕ) : ReaderA.leastDivisor k = Nat.minFac ((Nat.factorial k) ^ 2 + 1) := by
  have h2 : 2 ≤ (Nat.factorial k) ^ 2 + 1 := by
    have := pow_pos (Nat.factorial_pos k) 2; omega
  unfold ReaderA.leastDivisor
  apply le_antisymm
  · exact Nat.find_min' _ ⟨(Nat.minFac_prime (by omega)).one_lt, Nat.minFac_dvd _⟩
  · have hs := Nat.find_spec (ReaderA.exists_divisor_gt_one k)
    exact Nat.minFac_le_of_dvd hs.1 hs.2

theorem n_ge (k : ℕ) : 2 ≤ (Nat.factorial k) ^ 2 + 1 := by
  have := pow_pos (Nat.factorial_pos k) 2; omega

theorem frozen_p : OAI.OddKaplansky.sourcePrime =
    Nat.minFac ((Nat.factorial OAI.OddKaplansky.sourceM) ^ 2 + 1) := by
  rw [OAI.OddKaplansky.sourcePrime]

/- `unseal` lets `rfl` see through the frozen `@[irreducible]` m: both sides are the same term
`Nat.choose 1200 600`, so nothing is evaluated (the equation lemma of `sourceM` itself cannot be generated
without hitting the recursion limit). -/
unseal OAI.OddKaplansky.sourceM in
theorem mA : ReaderA.m = OAI.OddKaplansky.sourceM := rfl
unseal OAI.OddKaplansky.sourceM in
theorem mB : ReaderB.m = OAI.OddKaplansky.sourceM := rfl
unseal OAI.OddKaplansky.sourceM in
theorem mC : ReaderC.readingM = OAI.OddKaplansky.sourceM := rfl

theorem pA : ReaderA.p = OAI.OddKaplansky.sourcePrime := by
  show ReaderA.leastDivisor ReaderA.m = _
  rw [frozen_p, ← mA]; exact find_eq _
theorem pB : ReaderB.p = OAI.OddKaplansky.sourcePrime := by
  show sInf {h : ℕ | 1 < h ∧ h ∣ (Nat.factorial ReaderB.m) ^ 2 + 1} = _
  rw [frozen_p, ← mB]; exact sInf_eq _ (n_ge _)
theorem pC : ReaderC.readingP = OAI.OddKaplansky.sourcePrime := by
  show sInf {h : ℕ | 1 < h ∧ h ∣ (Nat.factorial ReaderC.readingM) ^ 2 + 1} = _
  rw [frozen_p, ← mC]; exact sInf_eq _ (n_ge _)

theorem A_thm : (type_of% @OAI.OddKaplansky.main_theorem) → (type_of% @ReaderA.reading_main) := by
  rintro ⟨hp, hodd, K, iF, iK, -, hcard, G, iG, hfg, htor, a, b, hab, hba, -⟩
  rw [pA]
  refine ⟨⟨⟨by exact_mod_cast hp.one_lt, ?_⟩, ?_⟩, hp, hodd, K, iF, iK, hcard, G, iG, hfg, htor, a, b, hab, hba⟩
  · show (OAI.OddKaplansky.sourcePrime : ℤ) ∣ ((Nat.factorial ReaderA.m : ℕ) : ℤ) ^ 2 + 1
    rw [frozen_p, ← mA]
    exact_mod_cast Nat.minFac_dvd _
  · rintro h ⟨h1, hd⟩
    have hpos : 0 ≤ h := by omega
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    have hd' : n ∣ (Nat.factorial ReaderA.m) ^ 2 + 1 := by exact_mod_cast hd
    rw [frozen_p, ← mA]
    exact_mod_cast Nat.minFac_le_of_dvd (by omega) hd'

theorem B_thm : (type_of% @OAI.OddKaplansky.main_theorem) → (type_of% @ReaderB.readingKaplansky) := by
  rintro ⟨hp, hodd, K, iF, iK, -, hcard, G, iG, hfg, htor, a, b, hab, hba, -⟩
  rw [pB]
  refine ⟨hp, ?_, K, iF, by rw [Nat.card_eq_fintype_card]; exact hcard, G, iG, hfg, htor, a, b, hab, hba⟩
  rintro h2; rw [h2] at hodd; exact absurd hodd (by decide)

theorem C_odd : (type_of% @OAI.OddKaplansky.main_theorem) → (type_of% @ReaderC.reading_p_odd_prime) := by
  rintro ⟨hp, hodd, -⟩
  rw [pC]; exact ⟨hp, hodd⟩

theorem C_thm : (type_of% @OAI.OddKaplansky.main_theorem) → (type_of% @ReaderC.reading_main) := by
  rintro ⟨-, -, K, iF, iK, -, hcard, G, iG, hfg, htor, a, b, hab, hba, -⟩
  rw [pC]
  exact ⟨K, iF, G, iG, by rw [Nat.card_eq_fintype_card]; exact hcard, hfg, htor, a, b, hab, hba⟩

end TargetO.OddKaplansky

#print axioms TargetO.OddKaplansky.A_thm
#print axioms TargetO.OddKaplansky.B_thm
#print axioms TargetO.OddKaplansky.C_odd
#print axioms TargetO.OddKaplansky.C_thm
