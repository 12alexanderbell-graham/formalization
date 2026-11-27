import Mathlib
import Readings.PiExp
import ComparatorChallenges.PiExponent

/-! # Target O, family O9 (irrationality exponent of π): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped. Closed: the "more precisely" inequality of every
reader. Closed: μ(π) = 2 for every reader (the frozen second conjunct, with rationals and a real `sSup`, gives
`IsLUB` of the exponent set — a real `sSup` of 2 forces the set nonempty and bounded — and the rationals
with denominator ≥ 2 correspond to the readers' coprime pairs). Not closed: the Flint–Hills consequence
(no frozen statement in this family). -/

namespace TargetO.PiExp

theorem A_precise : (type_of% @OAI.PiExponent.main) →
    (type_of% @ReaderA.ReadingA.PiExp.readingPiExp_precise) := by
  intro h ν hν
  obtain ⟨Q, -, hQ⟩ := h.1 ν hν
  exact ⟨Q, fun p q _ hq => hQ p q hq⟩

theorem B_precise : (type_of% @OAI.PiExponent.main) →
    (type_of% @ReaderB.ReadingO9B.reading_thm_1_1_precise) := by
  intro h ν hν
  exact h.1 ν hν


/-- frozen set of exponents (rationals) -/
def SF (x : ℝ) : Set ℝ := {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧ 0 < |x - (r : ℝ)| ∧ |x - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}}

/-- pairs version (reader A uses IsCoprime, B and C use Int.gcd = 1) -/
def SP (x : ℝ) : Set ℝ := {ν | 0 < ν ∧
    {pq : ℤ × ℤ | Int.gcd pq.1 pq.2 = 1 ∧ 2 ≤ pq.2 ∧
        0 < |x - (pq.1 : ℝ) / pq.2| ∧ |x - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-ν)}.Infinite}

theorem pairs_eq_image (x ν : ℝ) :
    {pq : ℤ × ℤ | Int.gcd pq.1 pq.2 = 1 ∧ 2 ≤ pq.2 ∧
        0 < |x - (pq.1 : ℝ) / pq.2| ∧ |x - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-ν)} =
    (fun r : ℚ => ((r.num, (r.den : ℤ)) : ℤ × ℤ)) ''
      {r : ℚ | 2 ≤ r.den ∧ 0 < |x - (r : ℝ)| ∧ |x - (r : ℝ)| < (r.den : ℝ) ^ (-ν)} := by
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨hg, hq, h0, h1⟩
    have hq0 : (0 : ℤ) < q := by omega
    set r : ℚ := (p : ℚ) / q
    have hcop : Nat.Coprime p.natAbs q.natAbs := by
      rw [Int.gcd_eq_natAbs] at hg; exact hg
    have hnum : r.num = p := Rat.num_div_eq_of_coprime hq0 hcop
    have hden : (r.den : ℤ) = q := Rat.den_div_eq_of_coprime hq0 hcop
    have hr : ((r : ℝ)) = (p : ℝ) / q := by simp [r]
    refine ⟨r, ⟨by omega, ?_, ?_⟩, hnum, hden⟩
    · rw [hr]; exact h0
    · rw [hr, show ((r.den : ℝ)) = ((q : ℤ) : ℝ) by exact_mod_cast hden]; exact h1
  · rintro ⟨r, ⟨hd, h0, h1⟩, rfl, rfl⟩
    have hr : (r : ℝ) = (r.num : ℝ) / ((r.den : ℤ) : ℝ) := by
      rw [Rat.cast_def]; push_cast; rfl
    refine ⟨?_, by exact_mod_cast hd, by rw [← hr]; exact h0, ?_⟩
    · rw [Int.gcd_eq_natAbs]; simpa using r.reduced
    · rw [← hr]; push_cast; exact h1

theorem SP_eq_SF (x : ℝ) : SP x = SF x := by
  ext ν
  simp only [SP, SF, Set.mem_setOf_eq, pairs_eq_image]
  rw [Set.infinite_image_iff]
  intro a _ b _ h
  simp only [Prod.mk.injEq] at h
  exact Rat.ext h.1 (by exact_mod_cast h.2)

theorem isLUB_of_sSup (S : Set ℝ) (h : sSup S = 2) : IsLUB S 2 := by
  have hne : S.Nonempty := by
    by_contra hne; rw [Set.not_nonempty_iff_eq_empty] at hne; rw [hne, Real.sSup_empty] at h; norm_num at h
  have hbdd : BddAbove S := by
    by_contra hb; rw [Real.sSup_of_not_bddAbove hb] at h; norm_num at h
  rw [← h]; exact isLUB_csSup hne hbdd

theorem frozen_isLUB : (type_of% @OAI.PiExponent.main) → IsLUB (SF Real.pi) 2 :=
  fun h => isLUB_of_sSup _ h.2

theorem coe_isLUB {S : Set ℝ} (h : IsLUB S 2) :
    IsLUB ((fun ν : ℝ => (ν : EReal)) '' S) 2 := by
  obtain ⟨ν0, hν0⟩ : S.Nonempty := by
    by_contra hne; rw [Set.not_nonempty_iff_eq_empty] at hne; rw [hne] at h
    have := h.2 (show (0:ℝ) ∈ upperBounds (∅ : Set ℝ) by simp); norm_num at this
  constructor
  · rintro _ ⟨ν, hν, rfl⟩
    show ((ν : ℝ) : EReal) ≤ 2
    rw [show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast]
    exact EReal.coe_le_coe_iff.mpr (h.1 hν)
  · intro b hb
    induction b using EReal.rec with
    | bot => exact absurd (hb ⟨ν0, hν0, rfl⟩) (by simp)
    | coe b =>
      have : b ∈ upperBounds S := fun ν hν => EReal.coe_le_coe_iff.mp (hb ⟨ν, hν, rfl⟩)
      rw [show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast]
      exact EReal.coe_le_coe_iff.mpr (h.2 this)
    | top => exact le_top

theorem A_set : ReaderA.ReadingA.PiExp.approxExponents Real.pi = SP Real.pi := by
  ext ν; simp only [ReaderA.ReadingA.PiExp.approxExponents, SP, Set.mem_setOf_eq,
    Int.isCoprime_iff_gcd_eq_one]

theorem A_isLUB : (type_of% @OAI.PiExponent.main) →
    (type_of% @ReaderA.ReadingA.PiExp.readingPiExp_mu_isLUB) := by
  intro h; show IsLUB (ReaderA.ReadingA.PiExp.approxExponents Real.pi) 2
  rw [A_set, SP_eq_SF]; exact frozen_isLUB h

theorem A_mu : (type_of% @OAI.PiExponent.main) →
    (type_of% @ReaderA.ReadingA.PiExp.readingPiExp_mu) := by
  intro h; show sSup _ = _
  have := A_isLUB h
  exact (coe_isLUB this).sSup_eq

theorem C_set (ν : ℝ) : {pq : ℤ × ℤ | 2 ≤ pq.2 ∧ Int.gcd pq.1 pq.2 = 1 ∧
      0 < |Real.pi - (pq.1 : ℝ) / (pq.2 : ℝ)| ∧
      |Real.pi - (pq.1 : ℝ) / (pq.2 : ℝ)| < (pq.2 : ℝ) ^ (-ν)} =
    {pq : ℤ × ℤ | Int.gcd pq.1 pq.2 = 1 ∧ 2 ≤ pq.2 ∧
        0 < |Real.pi - (pq.1 : ℝ) / pq.2| ∧ |Real.pi - (pq.1 : ℝ) / pq.2| < (pq.2 : ℝ) ^ (-ν)} := by
  ext pq; simp only [Set.mem_setOf_eq]; tauto

theorem B_set : {e : EReal | ∃ ν : ℝ, 0 < ν ∧ e = (ν : EReal) ∧
    {pq : ℤ × ℤ | 2 ≤ pq.2 ∧ Int.gcd pq.1 pq.2 = 1 ∧
      0 < |Real.pi - (pq.1 : ℝ) / pq.2| ∧ |Real.pi - (pq.1 : ℝ) / pq.2| < ((pq.2 : ℝ)) ^ (-ν)}.Infinite}
    = (fun ν : ℝ => (ν : EReal)) '' SP Real.pi := by
  ext e
  simp only [SP, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨ν, h0, rfl, hinf⟩
    exact ⟨ν, ⟨h0, (C_set ν) ▸ hinf⟩, rfl⟩
  · rintro ⟨ν, ⟨h0, hinf⟩, rfl⟩
    exact ⟨ν, h0, rfl, (C_set ν).symm ▸ hinf⟩

theorem B_mu : (type_of% @OAI.PiExponent.main) → (type_of% @ReaderB.ReadingO9B.reading_thm_1_1_mu) := by
  intro h
  show sSup _ = _
  rw [B_set]
  have := frozen_isLUB h
  rw [← SP_eq_SF] at this
  exact (coe_isLUB this).sSup_eq

theorem C_thm : (type_of% @OAI.PiExponent.main) → (type_of% @ReaderC.reading_thm1) := by
  intro h
  have hl : IsLUB (SP Real.pi) 2 := by rw [SP_eq_SF]; exact frozen_isLUB h
  refine ⟨?_, fun ν hν => ?_⟩
  · show (⨆ (ν : ℝ) (_ : 0 < ν ∧ Set.Infinite _), ENNReal.ofReal ν) = 2
    simp only [C_set]
    apply le_antisymm
    · refine iSup₂_le fun ν hν => ?_
      have : ν ≤ 2 := hl.1 hν
      calc ENNReal.ofReal ν ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
        _ = 2 := by norm_num
    · refine le_of_forall_lt fun c hc => ?_
      have hct : c.toReal < 2 := by
        have : c ≠ ⊤ := ne_top_of_lt hc
        have := (ENNReal.toReal_lt_toReal this (by norm_num)).mpr hc
        simpa using this
      obtain ⟨ν, hν, hcν⟩ := (lt_isLUB_iff hl).mp hct
      refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun ν (_ : ν ∈ SP Real.pi) => ENNReal.ofReal ν) ν hν)
      rw [← ENNReal.ofReal_toReal (ne_top_of_lt hc)]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hcν)).mpr hcν
  · obtain ⟨Q, -, hQ⟩ := h.1 ν hν
    exact ⟨Q, fun p q hq _ => hQ p q hq⟩

end TargetO.PiExp

#print axioms TargetO.PiExp.A_precise
#print axioms TargetO.PiExp.B_precise
#print axioms TargetO.PiExp.A_isLUB
#print axioms TargetO.PiExp.A_mu
#print axioms TargetO.PiExp.B_mu
#print axioms TargetO.PiExp.C_thm
