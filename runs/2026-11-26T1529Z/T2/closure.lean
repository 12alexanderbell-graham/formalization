import ZChallenge
import Readings.T2
import Closure.T2Dec

/-! Target 2: closure of the blind reading (runs/2026-11-26T1529Z/T2/reading.lean) against the frozen
`Challenge.lean` of anthropics/zeta-23-lean at 11b6c7e (here `ZChallenge`, the file verbatim), statements
taken with `type_of%`. Direction: frozen ⟹ reading. `reading_cumulative` (with the rate
O(log log T/log T)) is not implied: the frozen cumulative statements carry only o(1). -/

open Set

namespace ExternalT2

section Zeta

lemma zset (T₁ T₂ : ℝ) : Reading.zerosIn riemannZeta T₁ T₂ = _root_.zerosIn T₁ T₂ := by
  ext ρ; simp [Reading.zerosIn, _root_.zerosIn, IsNontrivialZero, and_assoc]

lemma N_eq (T₁ T₂ : ℝ) : Reading.N riemannZeta T₁ T₂ = Ncount T₁ T₂ := by
  unfold Reading.N Ncount; rw [zset]; rfl

lemma Nd_eq (T₁ T₂ : ℝ) : Reading.Nd riemannZeta T₁ T₂ = Ndist T₁ T₂ := by
  unfold Reading.Nd Ndist; rw [zset]

lemma N0star_eq (T₁ T₂ : ℝ) : Reading.N0star riemannZeta T₁ T₂ = _root_.N0star T₁ T₂ := by
  unfold Reading.N0star _root_.N0star; rw [zset]; rfl

lemma N0s_eq (T₁ T₂ : ℝ) : Reading.N0s riemannZeta T₁ T₂ = N0simple T₁ T₂ := by
  unfold Reading.N0s N0simple; rw [zset]; congr 1; ext ρ
  simp only [Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_setOf_eq, Reading.mult, zeroMult]; tauto

end Zeta

section L
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

lemma zsetL (T₁ T₂ : ℝ) :
    Reading.zerosIn (DirichletCharacter.LFunction χ) T₁ T₂ = zerosInL χ T₁ T₂ := by
  ext ρ; simp [Reading.zerosIn, zerosInL, IsNontrivialZeroL, and_assoc]

lemma N_eqL (T₁ T₂ : ℝ) : Reading.N (DirichletCharacter.LFunction χ) T₁ T₂ = NcountL χ T₁ T₂ := by
  unfold Reading.N NcountL; rw [zsetL]; rfl

lemma Nd_eqL (T₁ T₂ : ℝ) : Reading.Nd (DirichletCharacter.LFunction χ) T₁ T₂ = NdistL χ T₁ T₂ := by
  unfold Reading.Nd NdistL; rw [zsetL]

lemma N0s_eqL (T₁ T₂ : ℝ) :
    Reading.N0s (DirichletCharacter.LFunction χ) T₁ T₂ = N0simpleL χ T₁ T₂ := by
  unfold Reading.N0s N0simpleL; rw [zsetL]; congr 1; ext ρ
  simp only [Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_setOf_eq, Reading.mult, zeroMultL]; tauto

end L

theorem c_1i : (type_of% @two_thirds_simple_on_critical_line) → (type_of% @Reading.reading_1i) := by
  intro h ε hε; obtain ⟨T₀, hT⟩ := h ε hε
  exact ⟨T₀, fun T hT' => by dsimp only; rw [N0s_eq, N_eq]; exact hT T hT'⟩

theorem c_1ii : (type_of% @five_sixths_distinct) → (type_of% @Reading.reading_1ii) := by
  intro h ε hε; obtain ⟨T₀, hT⟩ := h ε hε
  exact ⟨T₀, fun T hT' => by dsimp only; rw [Nd_eq, N_eq]; exact hT T hT'⟩

theorem c_afortiori : (type_of% @two_thirds_on_critical_line) →
    (type_of% @Reading.reading_1_afortiori) := by
  intro h ε hε; obtain ⟨T₀, hT⟩ := h ε hε
  exact ⟨T₀, fun T hT' => by dsimp only; rw [N0star_eq, N_eq]; exact hT T hT'⟩

lemma cMTinv_eq : Reading.cMTinv = 1 / cMT := by
  have h := ExternalT2.Dec.inv_eq
  unfold Reading.cMTinv cMT
  rw [one_div (Real.sqrt 2 * _ / _)]
  simp only [ExternalT2.Dec.θ] at h
  rw [h]

theorem c_MT : (type_of% @montgomery_taylor_simple_on_critical_line_mult) ∧
    (type_of% @montgomery_taylor_distinct_mult) → (type_of% @Reading.reading_1_MT) := by
  rintro ⟨h1, h2⟩
  refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
  · obtain ⟨T₀, hT⟩ := h1 ε hε
    exact ⟨T₀, fun T hT' => by dsimp only; rw [N0s_eq, N_eq, cMTinv_eq]; exact hT T hT'⟩
  · obtain ⟨T₀, hT⟩ := h2 ε hε
    refine ⟨T₀, fun T hT' => ?_⟩
    dsimp only
    rw [Nd_eq, N_eq, cMTinv_eq]
    have := hT T hT'
    convert this using 3; ring

theorem c_2 : (type_of% @two_thirds_simple_on_critical_line) ∧ (type_of% @five_sixths_distinct) ∧
    (type_of% @dirichlet_two_thirds_simple_on_critical_line) ∧
    (type_of% @dirichlet_five_sixths_distinct) → (type_of% @Reading.reading_2) := by
  rintro ⟨hz1, hz2, hl1, hl2⟩ q _ χ hχ
  rcases Nat.lt_or_ge 1 q with hq | hq
  · refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨T₀, hT⟩ := hl1 χ hq hχ ε hε
      exact ⟨T₀, fun T hT' => by dsimp only; rw [N0s_eqL, N_eqL]; exact hT T hT'⟩
    · obtain ⟨T₀, hT⟩ := hl2 χ hq hχ ε hε
      exact ⟨T₀, fun T hT' => by dsimp only; rw [Nd_eqL, N_eqL]; exact hT T hT'⟩
  · obtain rfl : q = 1 := by have := NeZero.ne q; omega
    simp only [DirichletCharacter.LFunction_modOne_eq]
    exact ⟨c_1i hz1, c_1ii hz2⟩

/-- Simple zeros on the line are at most the line zeros counted with multiplicity, whenever the
total count is not the junk value of an infinite window. -/
lemma simple_le (T₁ T₂ : ℝ) (ε : ℝ) :
    ((672 / 1000 - ε) * (Ncount T₁ T₂ : ℝ) ≤ N0simple T₁ T₂ → (672 / 1000 - ε) * (Ncount T₁ T₂ : ℝ)
      ≤ (Reading.N0 riemannZeta T₁ T₂ : ℝ)) := by
  intro h
  set L := {ρ ∈ _root_.zerosIn T₁ T₂ | ρ.re = 1 / 2}
  by_cases hfin : (L ∩ Function.support zeroMult).Finite
  · refine h.trans ?_
    have hS : (_root_.zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}) ⊆
        L ∩ Function.support zeroMult := by
      rintro ρ ⟨⟨hz, hre⟩, hm⟩
      exact ⟨⟨hz, hre⟩, by simp only [Function.mem_support]; rw [show zeroMult ρ = 1 from hm]; norm_num⟩
    have hSfin := hfin.subset hS
    unfold Reading.N0 N0simple
    rw [zset]
    show (((_root_.zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard : ℕ) : ℝ) ≤
      ((∑ᶠ ρ ∈ L, zeroMult ρ : ℕ) : ℝ)
    rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Set.ncard_eq_toFinset_card _ hSfin]
    norm_cast
    calc hSfin.toFinset.card = ∑ ρ ∈ hSfin.toFinset, zeroMult ρ := by
          rw [Finset.card_eq_sum_ones]; apply Finset.sum_congr rfl; intro ρ hρ
          simp only [Set.Finite.mem_toFinset] at hρ; exact hρ.2.symm
      _ ≤ ∑ ρ ∈ hfin.toFinset, zeroMult ρ :=
          Finset.sum_le_sum_of_subset (by intro ρ hρ; simp only [Set.Finite.mem_toFinset] at hρ ⊢; exact hS hρ)
  · have hinf : (_root_.zerosIn T₁ T₂ ∩ Function.support zeroMult).Infinite := by
      intro hf; apply hfin; exact hf.subset (fun ρ hρ => ⟨hρ.1.1, hρ.2⟩)
    have h0 : Ncount T₁ T₂ = 0 := by unfold Ncount; exact finsum_mem_eq_zero_of_infinite hinf
    rw [h0]; simp

theorem c_headline : (type_of% @montgomery_taylor_simple_on_critical_line_mult_cumulative) →
    (type_of% @Reading.reading_headline) := by
  intro h ε hε
  obtain ⟨T₀, hT⟩ := h ε hε
  refine ⟨T₀, fun T hT' => ?_⟩
  dsimp only
  rw [N_eq]
  apply simple_le 0 T ε
  have hd := ExternalT2.Dec.headline_decimal
  have hb := hT T hT'
  refine le_trans ?_ hb
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold cMT; linarith

end ExternalT2
#print axioms ExternalT2.c_1i
#print axioms ExternalT2.c_1ii
#print axioms ExternalT2.c_afortiori
#print axioms ExternalT2.c_MT
#print axioms ExternalT2.c_2
#print axioms ExternalT2.c_headline
