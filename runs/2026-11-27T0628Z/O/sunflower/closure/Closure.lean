import Mathlib
import Readings.Sunflower
import ComparatorChallenges.Sunflower

/-! # Target O, family O14 (an exponential bound for sunflowers): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: k-uniform families, `∃ C : ℕ, 1 ≤ C` per r.
Closed here: every reader's qualitative reading. Reader C's (finite families of sets of size ≤ k) from the
uniform frozen statement by splitting the family into its k + 1 layers (B = 2C); readers A and B's (possibly
infinite `Set` families, finiteness part of the conclusion; reader A also `M_r(k) ≤ B_r^k`) from reader C's,
since a set family whose finite subfamilies are bounded is finite. Not closed: every quantitative reading (the
manuscript's B_r = 2^{C H⁴ L^{5/2}} with an absolute C has no Lean statement) and reader C's separate
`M_r(k)` theorem (sSup over ℕ). -/

namespace TargetO.Sunflower

universe u

theorem C_qual : (type_of% @OAI.Combinatorics.Sunflower.erdosRadoSunflower.{u}) →
    (type_of% @ReaderC.ReadingC.reading_sunflower_qualitative.{u}) := by
  intro h r hr
  obtain ⟨Cn, hC1, hC⟩ := h r hr
  refine ⟨2 * (Cn : ℝ), fun α _ k hk F hsize hno => ?_⟩
  have layer : ∀ j, (F.filter (fun A => A.card = j)).card ≤ Cn ^ j := by
    intro j
    by_contra hlt
    push Not at hlt
    obtain ⟨G, hG, hGc, K, hK⟩ :=
      hC j α (F.filter (fun A => A.card = j)) (fun A hA => (Finset.mem_filter.mp hA).2) hlt
    apply hno
    refine ⟨G, hG.trans (Finset.filter_subset _ _), hGc, K, fun A hA B hB hAB => ?_⟩
    convert hK A hA B hB hAB
  have hsum : F.card = ∑ j ∈ Finset.range (k + 1), (F.filter (fun A => A.card = j)).card :=
    Finset.card_eq_sum_card_fiberwise (fun A hA => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsize A hA)))
  have hle : F.card ≤ (k + 1) * Cn ^ k := by
    rw [hsum]
    calc ∑ j ∈ Finset.range (k + 1), (F.filter (fun A => A.card = j)).card
        ≤ ∑ _j ∈ Finset.range (k + 1), Cn ^ k := by
          refine Finset.sum_le_sum fun j hj => (layer j).trans ?_
          exact Nat.pow_le_pow_right hC1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = (k + 1) * Cn ^ k := by simp
  have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hnat : F.card ≤ (2 * Cn) ^ k := by
    calc F.card ≤ (k + 1) * Cn ^ k := hle
      _ ≤ 2 ^ k * Cn ^ k := Nat.mul_le_mul_right _ h2
      _ = (2 * Cn) ^ k := by rw [mul_pow]
  exact_mod_cast hnat

/-- From a bound for finite families (reader C's form) to families given as a `Set`: a set family all of
whose finite subfamilies are sunflower-free is finite, and bounded by the same `B ^ k`. -/
theorem set_version {B : ℝ} {k : ℕ} (hk : 1 ≤ k) {r : ℕ}
    (hB : ∀ (α : Type) [DecidableEq α] (k : ℕ), 1 ≤ k → ∀ F : Finset (Finset α),
      (∀ A ∈ F, A.card ≤ k) → ReaderC.ReadingC.NoSunflower r F → (F.card : ℝ) ≤ B ^ k)
    {α : Type} [DecidableEq α] (F : Set (Finset α)) (hsize : ∀ A ∈ F, A.card ≤ k)
    (hno : ¬ ∃ S : Finset (Finset α), (↑S : Set (Finset α)) ⊆ F ∧ S.card = r ∧
      ∃ C : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C) :
    F.Finite ∧ (F.ncard : ℝ) ≤ B ^ k := by
  have fin_bound : ∀ G : Finset (Finset α), (↑G : Set (Finset α)) ⊆ F → (G.card : ℝ) ≤ B ^ k := by
    intro G hG
    refine hB α k hk G (fun A hA => hsize A (hG hA)) ?_
    rintro ⟨S, hS, hSc, C, hC⟩
    exact hno ⟨S, (Finset.coe_subset.mpr hS).trans hG, hSc, C, hC⟩
  have hfin : F.Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := exists_nat_gt (B ^ k)
    obtain ⟨G, hG, hGc⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have := fin_bound G hG
    rw [hGc] at this
    linarith
  refine ⟨hfin, ?_⟩
  have := fin_bound hfin.toFinset (by simp)
  rwa [Set.ncard_eq_toFinset_card F hfin]

/-- Reader B's qualitative reading (families as `Set`s, finiteness part of the conclusion). -/
theorem B_qual : (type_of% @OAI.Combinatorics.Sunflower.erdosRadoSunflower.{0}) →
    (type_of% @ReaderB.reading_sunflower_qualitative) := by
  intro h r hr
  obtain ⟨B, hB⟩ := C_qual.{0} h r hr
  refine ⟨B, fun k hk α _ F hsize hno => set_version hk hB F hsize ?_⟩
  rintro ⟨S, hS, hSc, C, hC⟩
  exact hno ⟨S, hS, hSc, C, hC⟩

/-- An `r`-element family with a common pairwise core, listed injectively by `Fin r` (reader A's form). -/
theorem listed {α : Type} [DecidableEq α] {r : ℕ} {F : Set (Finset α)} (S : Finset (Finset α))
    (hS : (↑S : Set (Finset α)) ⊆ F) (hSc : S.card = r) (C : Finset α)
    (hC : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C) : ReaderA.ReadingO14.ContainsSunflower r F := by
  let e := Finset.equivFinOfCardEq hSc
  refine ⟨fun i => (e.symm i).1, fun i => hS (e.symm i).2, ?_, C, fun i j hij => ?_⟩
  · exact Subtype.val_injective.comp e.symm.injective
  · refine hC _ (e.symm i).2 _ (e.symm j).2 ?_
    intro hEq
    exact hij (e.symm.injective (Subtype.val_injective hEq))

/-- Reader A's qualitative reading: the `Set` form and `M_r(k) ≤ B_r^k`. -/
theorem A_qual : (type_of% @OAI.Combinatorics.Sunflower.erdosRadoSunflower.{0}) →
    (type_of% @ReaderA.ReadingO14.reading_O14_qualitative) := by
  intro h r hr
  obtain ⟨B, hB⟩ := C_qual.{0} h r hr
  have hset : ∀ (α : Type) [DecidableEq α] (F : Set (Finset α)) (k : ℕ), 1 ≤ k →
      (∀ A ∈ F, A.card ≤ k) → ¬ ReaderA.ReadingO14.ContainsSunflower r F →
      F.Finite ∧ (F.ncard : ℝ) ≤ B ^ k := by
    intro α _ F k hk hsize hno
    refine set_version hk hB F hsize ?_
    rintro ⟨S, hS, hSc, C, hC⟩
    exact hno (listed S hS hSc C hC)
  refine ⟨B, hset, fun k hk => ?_⟩
  have h0 : (0 : ℝ) ≤ B ^ k := by
    have := (hset ℕ (∅ : Set (Finset ℕ)) k hk (by simp) (by
      rintro ⟨A, hA, -⟩
      have := hA ⟨0, by omega⟩
      simp at this)).2
    simpa using this
  have hM : ReaderA.ReadingO14.M r k ≤ ((⌊B ^ k⌋₊ : ℕ) : ℕ∞) := by
    refine iSup_le fun F => iSup_le fun hF => iSup_le fun hno => ?_
    have := (hset ℕ (F : Set (Finset ℕ)) k hk (fun A hA => (hF A hA).le) hno).2
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast Nat.le_floor this
  calc ((ReaderA.ReadingO14.M r k : ℕ∞) : ENNReal) ≤ (((⌊B ^ k⌋₊ : ℕ) : ℕ∞) : ENNReal) :=
        ENat.toENNReal_le.mpr hM
    _ = ENNReal.ofReal ((⌊B ^ k⌋₊ : ℕ) : ℝ) := by simp
    _ ≤ ENNReal.ofReal (B ^ k) := ENNReal.ofReal_le_ofReal (Nat.floor_le h0)

end TargetO.Sunflower

#print axioms TargetO.Sunflower.C_qual
#print axioms TargetO.Sunflower.B_qual
#print axioms TargetO.Sunflower.A_qual
