import Mathlib
import Readings.Littlewood
import ComparatorChallenges.AsymptoticallyMinimalLittlewood
import Closure.Littlewood

/-! # Target O, family O15: the "lim m_N = 1" readings (run 2026-11-27T0628Z).
The frozen statement gives the upper bound m_N ≤ 1 + η (through each reader's "Equivalently" form, closed in
`Closure.Littlewood`). The lower bound m_N ≥ 1, which the manuscript takes as known ("Orthogonality gives
‖P‖₂² = N"), is proved here, not assumed: at the N-th roots of unity ∑_j |P(ω^j)|² = N² (discrete
orthogonality), so some root has |P| ≥ √N. Together: every reader's limit form follows from the frozen
statement (frozen ⇒ reading), standard axioms. -/

open Complex Finset Filter Topology

namespace TargetO.LittlewoodLimit


/-- The polynomial `∑_{k<N} c_k z^k` with real coefficients. -/
noncomputable def Q (N : ℕ) (c : ℕ → ℝ) (z : ℂ) : ℂ := ∑ k ∈ range N, (c k : ℂ) * z ^ k

theorem norm_e (t : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * t)‖ = 1 := by
  have : (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- On the unit circle a ±1 polynomial of length `N` has modulus at most `N`. -/
theorem Q_le (N : ℕ) (c : ℕ → ℝ) (hc : ∀ k < N, c k = 1 ∨ c k = -1) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖Q N c z‖ ≤ N := by
  unfold Q
  calc ‖∑ k ∈ range N, (c k : ℂ) * z ^ k‖ ≤ ∑ k ∈ range N, ‖(c k : ℂ) * z ^ k‖ := norm_sum_le _ _
    _ = ∑ _k ∈ range N, (1 : ℝ) := by
        refine sum_congr rfl fun k hk => ?_
        rw [norm_mul, norm_pow, hz, one_pow, mul_one]
        rcases hc k (mem_range.mp hk) with h | h <;> simp [h]
    _ = N := by simp

/-- Orthogonality at the `N`-th roots of unity: `∑_{j<N} |Q(ω^j)|² = N · ∑_{k<N} c_k²`. -/
theorem sum_sq (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℝ) :
    ∑ j ∈ range N, (Q N c (Complex.exp (2 * Real.pi * Complex.I / N) ^ j) *
      (starRingEnd ℂ) (Q N c (Complex.exp (2 * Real.pi * Complex.I / N) ^ j))) =
      (N : ℂ) * ∑ k ∈ range N, ((c k : ℂ)) ^ 2 := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hω
  have hprim : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N (by omega)
  have hnorm : ‖ω‖ = 1 := hprim.norm'_eq_one (by omega)
  have hωc : ω * (starRingEnd ℂ) ω = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  have hpowN : ω ^ N = 1 := hprim.pow_eq_one
  have hcpowN : ((starRingEnd ℂ) ω) ^ N = 1 := by rw [← map_pow, hpowN, map_one]
  -- expand
  have expand : ∀ j, Q N c (ω ^ j) * (starRingEnd ℂ) (Q N c (ω ^ j)) =
      ∑ k ∈ range N, ∑ l ∈ range N, (c k : ℂ) * (c l : ℂ) * (ω ^ k * (starRingEnd ℂ ω) ^ l) ^ j := by
    intro j
    unfold Q
    rw [map_sum, sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    simp only [map_mul, map_pow, Complex.conj_ofReal]
    ring
  simp_rw [expand]
  have swap : ∑ j ∈ range N, ∑ k ∈ range N, ∑ l ∈ range N,
      (c k : ℂ) * (c l : ℂ) * (ω ^ k * (starRingEnd ℂ ω) ^ l) ^ j =
      ∑ k ∈ range N, ∑ l ∈ range N, (c k : ℂ) * (c l : ℂ) *
        ∑ j ∈ range N, (ω ^ k * (starRingEnd ℂ ω) ^ l) ^ j := by
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_sum]
  rw [swap]
  have inner : ∀ k ∈ range N, ∀ l ∈ range N,
      ∑ j ∈ range N, (ω ^ k * (starRingEnd ℂ ω) ^ l) ^ j = if k = l then (N : ℂ) else 0 := by
    intro k hk l hl
    split_ifs with hkl
    · subst hkl
      rw [← mul_pow, hωc, one_pow]; simp
    · have hx1 : ω ^ k * (starRingEnd ℂ ω) ^ l ≠ 1 := by
        intro h1
        apply hkl
        have : ω ^ k = ω ^ l := by
          calc ω ^ k = ω ^ k * ((starRingEnd ℂ ω) ^ l * ω ^ l) := by
                rw [← mul_pow, mul_comm (starRingEnd ℂ ω), hωc, one_pow, mul_one]
            _ = (ω ^ k * (starRingEnd ℂ ω) ^ l) * ω ^ l := by ring
            _ = ω ^ l := by rw [h1, one_mul]
        exact hprim.pow_inj (mem_range.mp hk) (mem_range.mp hl) this
      rw [geom_sum_eq hx1, mul_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm l N, pow_mul, pow_mul,
        hpowN, hcpowN, one_pow, one_pow, one_mul, sub_self, zero_div]
  calc ∑ k ∈ range N, ∑ l ∈ range N, (c k : ℂ) * (c l : ℂ) *
        ∑ j ∈ range N, (ω ^ k * (starRingEnd ℂ ω) ^ l) ^ j
      = ∑ k ∈ range N, ∑ l ∈ range N, (c k : ℂ) * (c l : ℂ) * (if k = l then (N : ℂ) else 0) := by
        refine sum_congr rfl fun k hk => sum_congr rfl fun l hl => ?_
        rw [inner k hk l hl]
    _ = (N : ℂ) * ∑ k ∈ range N, ((c k : ℂ)) ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun k hk => ?_
        simp only [mul_ite, mul_zero, sum_ite_eq, hk, ite_true]
        ring

/-- Some `N`-th root of unity `e(j/N)` has `|Q| ≥ √N`. -/
theorem exists_large (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℝ) (hc : ∀ k < N, c k = 1 ∨ c k = -1) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ Real.sqrt N ≤ ‖Q N c (Complex.exp (2 * Real.pi * Complex.I * t))‖ := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / N)
  have hroot : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * (((j : ℝ) / N : ℝ) : ℂ)) = ω ^ j := by
    intro j
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hs := sum_sq N hN c
  have hcsq : ∑ k ∈ range N, ((c k : ℂ)) ^ 2 = N := by
    rw [show (N : ℂ) = ∑ _k ∈ range N, (1 : ℂ) by simp]
    refine sum_congr rfl fun k hk => ?_
    rcases hc k (mem_range.mp hk) with h | h <;> simp [h]
  rw [hcsq] at hs
  have hreal : ∑ j ∈ range N, ‖Q N c (ω ^ j)‖ ^ 2 = (N : ℝ) * N := by
    have : ∀ j, ((‖Q N c (ω ^ j)‖ ^ 2 : ℝ) : ℂ) = Q N c (ω ^ j) * (starRingEnd ℂ) (Q N c (ω ^ j)) := by
      intro j
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : ((∑ j ∈ range N, ‖Q N c (ω ^ j)‖ ^ 2 : ℝ) : ℂ) = ((N * N : ℝ) : ℂ) := by
      push_cast
      simp_rw [← Complex.ofReal_pow, this]
      rw [hs]
    exact_mod_cast h2
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le (s := range N) (f := fun _ => (N : ℝ))
    (g := fun j => ‖Q N c (ω ^ j)‖ ^ 2) (nonempty_range_iff.mpr (by omega))
    (by rw [hreal]; simp)
  have hjN : (j : ℝ) < N := by exact_mod_cast mem_range.mp hj
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨(j : ℝ) / N, by positivity, by rw [div_le_one hN0]; exact hjN.le, ?_⟩
  rw [hroot]
  rw [show ‖Q N c (ω ^ j)‖ = Real.sqrt (‖Q N c (ω ^ j)‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt hle


/-- Squeeze: `1 ≤ m N` for `N ≥ 1`, and eventually `m N ≤ 1 + η` for each `η > 0`. -/
theorem squeeze (m : ℕ → ℝ) (hlow : ∀ N, 1 ≤ N → 1 ≤ m N)
    (hup : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → m N ≤ 1 + η) : Tendsto m atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N₀, hN₀⟩ := hup (δ / 2) (by positivity)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have h1 := hlow N (le_of_max_le_right hN)
  have h2 := hN₀ N (le_of_max_le_left hN)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Extend a `Fin N` coefficient vector by `1`. -/
noncomputable def ext {N : ℕ} (ε : Fin N → ℝ) (k : ℕ) : ℝ := if h : k < N then ε ⟨k, h⟩ else 1

theorem fin_eq_Q {N : ℕ} (ε : Fin N → ℝ) (z : ℂ) :
    ∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ) = Q N (ext ε) z := by
  unfold Q ext
  rw [Finset.sum_range (fun k => (((if h : k < N then ε ⟨k, h⟩ else 1 : ℝ)) : ℂ) * z ^ k)]
  simp

theorem ext_sign {N : ℕ} (ε : Fin N → ℝ) (hε : ∀ k, ε k = 1 ∨ ε k = -1) :
    ∀ k < N, ext ε k = 1 ∨ ext ε k = -1 := by
  intro k hk
  unfold ext
  simp only [hk, dite_true]
  exact hε _

theorem sqrt_pos' {N : ℕ} (hN : 1 ≤ N) : 0 < Real.sqrt N :=
  Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))

/-- Sup over `t : ℝ` of a ±1 polynomial on the circle is at least `√N`. -/
theorem iSup_ge (N : ℕ) (hN : 1 ≤ N) (c : ℕ → ℝ) (hc : ∀ k < N, c k = 1 ∨ c k = -1) :
    Real.sqrt N ≤ ⨆ t : ℝ, ‖Q N c (Complex.exp (2 * Real.pi * Complex.I * t))‖ := by
  obtain ⟨t, -, -, ht⟩ := exists_large N hN c hc
  have hb : BddAbove (Set.range fun s : ℝ => ‖Q N c (Complex.exp (2 * Real.pi * Complex.I * s))‖) := by
    refine ⟨N, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact Q_le N c hc _ (norm_e s)
  exact ht.trans (le_ciSup hb t)

/-- Reader A's limit form. -/
theorem A_limit : (type_of% @OAI.AsymptoticallyMinimalLittlewood.main) →
    (type_of% @ReaderA.ReadingO15.reading_O15_limit) := by
  intro h
  have hP : ∀ {N : ℕ} (ε : Fin N → ℤˣ) (z : ℂ),
      ReaderA.ReadingO15.P ε z = Q N (ext (fun k => (((ε k : ℤ) : ℝ)))) z := by
    intro N ε z
    rw [← fin_eq_Q]
    unfold ReaderA.ReadingO15.P
    simp
  have hsgn : ∀ {N : ℕ} (ε : Fin N → ℤˣ), ∀ k, (((ε k : ℤ) : ℝ)) = 1 ∨ (((ε k : ℤ) : ℝ)) = -1 := by
    intro N ε k
    rcases Int.units_eq_one_or (ε k) with h1 | h1 <;> simp [h1]
  have hsup : ∀ {N : ℕ} (ε : Fin N → ℤˣ), ReaderA.ReadingO15.supNorm ε =
      ⨆ t : ℝ, ‖Q N (ext (fun k => (((ε k : ℤ) : ℝ)))) (Complex.exp (2 * Real.pi * Complex.I * t))‖ := by
    intro N ε
    unfold ReaderA.ReadingO15.supNorm ReaderA.ReadingO15.e
    simp only [hP]
  apply squeeze
  · intro N hN
    unfold ReaderA.ReadingO15.m
    refine Finset.le_inf' _ _ fun ε _ => ?_
    rw [hsup, one_div, le_inv_mul_iff₀ (sqrt_pos' hN), mul_one]
    exact iSup_ge N hN _ (ext_sign _ (hsgn ε))
  · intro η hη
    obtain ⟨N₀, hN₀⟩ := TargetO.Littlewood.A_equiv h η hη
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    obtain ⟨ε, hb⟩ := hN₀ N (le_of_max_le_left hN)
    unfold ReaderA.ReadingO15.m
    refine (Finset.inf'_le _ (Finset.mem_univ ε)).trans ?_
    have hs : ReaderA.ReadingO15.supNorm ε ≤ (1 + η) * Real.sqrt N := by
      unfold ReaderA.ReadingO15.supNorm
      refine ciSup_le fun t => ?_
      unfold ReaderA.ReadingO15.P ReaderA.ReadingO15.e
      exact hb _ (norm_e t)
    rw [one_div, inv_mul_le_iff₀ (sqrt_pos' hN1)]
    linarith

/-- Reader B's limit form. -/
theorem B_limit : (type_of% @OAI.AsymptoticallyMinimalLittlewood.main) →
    (type_of% @ReaderB.reading_littlewood_limit) := by
  intro h
  have hsup : ∀ {N : ℕ} (ε : Fin N → ℝ), ReaderB.supNorm ε =
      ⨆ t : ℝ, ‖Q N (ext ε) (Complex.exp (2 * Real.pi * Complex.I * t))‖ := by
    intro N ε
    unfold ReaderB.supNorm ReaderB.littlePoly
    simp only [fin_eq_Q]
  have hne : ∀ N, Nonempty (ReaderB.Signs N) := fun N => ⟨⟨fun _ => 1, fun _ => Or.inl rfl⟩⟩
  have hnn : ∀ {N : ℕ} (ε : Fin N → ℝ), 0 ≤ ReaderB.supNorm ε := fun ε =>
    Real.iSup_nonneg fun _ => norm_nonneg _
  apply squeeze
  · intro N hN
    unfold ReaderB.mN
    have := hne N
    refine le_ciInf fun ε => ?_
    rw [le_div_iff₀ (sqrt_pos' hN), one_mul, hsup]
    exact iSup_ge N hN _ (ext_sign _ ε.2)
  · intro η hη
    obtain ⟨N₀, hN₀⟩ := TargetO.Littlewood.B_equiv h η hη
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    obtain ⟨ε, hs, hb⟩ := hN₀ N (le_of_max_le_left hN)
    unfold ReaderB.mN
    refine (ciInf_le ⟨0, ?_⟩ (⟨ε, hs⟩ : ReaderB.Signs N)).trans ?_
    · rintro _ ⟨e, rfl⟩
      exact div_nonneg (hnn _) (Real.sqrt_nonneg _)
    · have hs' : ReaderB.supNorm ε ≤ (1 + η) * Real.sqrt N := by
        unfold ReaderB.supNorm ReaderB.littlePoly
        exact ciSup_le fun t => hb _ (norm_e t)
      rw [div_le_iff₀ (sqrt_pos' hN1)]
      exact hs'

/-- Reader C's limit form. -/
theorem C_limit : (type_of% @OAI.AsymptoticallyMinimalLittlewood.main) →
    (type_of% @ReaderC.ReadingC.reading_littlewood_limit) := by
  intro h
  have hbdd : ∀ (N : ℕ) (ε : ℕ → ℝ), ReaderC.ReadingC.IsSignVec N ε →
      BddAbove ((fun t : ℝ => ‖∑ k ∈ Finset.range N,
          ((ε k : ℝ) : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) ^ k‖) '' Set.Icc (0 : ℝ) 1) := by
    intro N ε hε
    refine ⟨N, ?_⟩
    rintro _ ⟨s, -, rfl⟩
    exact Q_le N ε hε _ (norm_e s)
  have hnn : ∀ (N : ℕ) (ε : ℕ → ℝ), 0 ≤ ReaderC.ReadingC.lwMaxMod N ε := by
    intro N ε
    unfold ReaderC.ReadingC.lwMaxMod
    exact Real.sSup_nonneg (by rintro _ ⟨s, -, rfl⟩; exact norm_nonneg _)
  apply squeeze
  · intro N hN
    unfold ReaderC.ReadingC.lwMN
    refine le_csInf ⟨_, ⟨fun _ => 1, fun _ _ => Or.inl rfl, rfl⟩⟩ ?_
    rintro _ ⟨ε, hε, rfl⟩
    rw [one_div, le_inv_mul_iff₀ (sqrt_pos' hN), mul_one]
    obtain ⟨t, ht0, ht1, ht⟩ := exists_large N hN ε hε
    unfold ReaderC.ReadingC.lwMaxMod
    exact ht.trans (le_csSup (hbdd N ε hε) ⟨t, ⟨ht0, ht1⟩, rfl⟩)
  · intro η hη
    obtain ⟨N₀, hN₀⟩ := TargetO.Littlewood.C_equiv h η hη
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    obtain ⟨ε, hs, hb⟩ := hN₀ N (le_of_max_le_left hN)
    unfold ReaderC.ReadingC.lwMN
    have hbb : BddBelow ((fun ε : ℕ → ℝ => (1 / Real.sqrt (N : ℝ)) * ReaderC.ReadingC.lwMaxMod N ε) ''
        {ε | ReaderC.ReadingC.IsSignVec N ε}) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨e, -, rfl⟩
      exact mul_nonneg (by positivity) (hnn N e)
    refine (csInf_le hbb ⟨ε, hs, rfl⟩).trans ?_
    · have hs' : ReaderC.ReadingC.lwMaxMod N ε ≤ (1 + η) * Real.sqrt N := by
        unfold ReaderC.ReadingC.lwMaxMod
        refine csSup_le ((Set.nonempty_Icc.mpr zero_le_one).image _) ?_
        rintro _ ⟨s, -, rfl⟩
        exact hb _ (norm_e s)
      rw [one_div, inv_mul_le_iff₀ (sqrt_pos' hN1)]
      linarith

end TargetO.LittlewoodLimit

#print axioms TargetO.LittlewoodLimit.A_limit
#print axioms TargetO.LittlewoodLimit.B_limit
#print axioms TargetO.LittlewoodLimit.C_limit
