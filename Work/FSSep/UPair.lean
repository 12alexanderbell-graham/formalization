import Mathlib
import Work.FSSep.UCompare

/-!
# Falkner–Skan separation is unique in β: the two Crocco curves read at equal velocity, and the
# tail argument (run 2026-11-11T0232Z, fork D)

`pairS`: for two zero-wall-shear solutions A (βA) and B (βB) with βA < βB < 0, on common Crocco
ranges: fA < fB at equal velocity, fB − fA nondecreasing in the velocity, and step 1 of
Theorem U′. `sep_core`: if B also has the decay condition, A cannot exist (Theorem U′'s tail
argument, `Work.FalknerSkan.NegUPrime.u_prime`, with the roles of the two solutions as there).
-/

namespace Work.FSSep.UPair
open Set Filter Topology
open Work.FSSep.UCompare

theorem pairS {βA βB EA EB : ℝ} (hβ : βA < βB) (hβB : βB < 0) (hEA : 0 < EA) (hEB : 0 < EB)
    {fA pA qA fB pB qB : ℝ → ℝ} (A : SolB βA fA pA qA) (B : SolB βB fB pB qB) :
    (∀ uA ∈ Ioo 0 EA, ∀ uB ∈ Ico 0 EB, pA uA = pB uB → fA uA < fB uB) ∧
    (∀ uA ∈ Ico 0 EA, ∀ uB ∈ Ico 0 EB, ∀ vA ∈ Ico 0 EA, ∀ vB ∈ Ico 0 EB,
      pA uA = pB uB → pA vA = pB vB → pA uA ≤ pA vA → fB uB - fA uA ≤ fB vB - fA vA) ∧
    (∀ uA ∈ Ioo 0 EA, ∀ uB ∈ Ico 0 EB, ∀ vA ∈ Ico 0 EA, ∀ vB ∈ Ico 0 EB,
      pA uA = pB uB → pA vA = pB vB → pA uA ≤ pA vA →
      (fB uB - fA uA) * (pA vA - pA uA) ≤ qA vA - qB vB + 2 * (-βB) * ((vB - fB vB) - (uB - fB uB))) := by
  have restrict : ∀ {g g' : ℝ → ℝ} {E : ℝ},
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η) →
      ∀ η ∈ Icc 0 E, HasDerivWithinAt g (g' η) (Icc 0 E) η := fun hg η hη =>
    (hg η hη.1).mono Icc_subset_Ici_self
  obtain ⟨ψA, hψA, backA, czA, cFA, dFA, dzA, cψA, dψA⟩ :=
    Work.FSSep.UCrocco.crocco_b hEA (restrict A.hf) (restrict A.hp) (restrict A.hq) A.hp0
      (fun η hη => A.hpos η hη.1)
  obtain ⟨ψB, hψB, backB, czB, cFB, dFB, dzB, cψB, dψB⟩ :=
    Work.FSSep.UCrocco.crocco_b hEB (restrict B.hf) (restrict B.hp) (restrict B.hq) B.hp0
      (fun η hη => B.hpos η hη.1)
  set L := min (pA EA) (pB EB) with hL
  have hL1 : Ico 0 L ⊆ Ico 0 (pA EA) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hL2 : Ico 0 L ⊆ Ico 0 (pB EB) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hI1 : Ioo 0 L ⊆ Ioo 0 (pA EA) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hI2 : Ioo 0 L ⊆ Ioo 0 (pB EB) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hLle : L ≤ 1 := le_trans (min_le_left _ _) (A.bounds EA hEA.le).2.le
  have hψ0A : ψA 0 = 0 := by have := backA 0 ⟨le_rfl, hEA⟩; rwa [A.hp0] at this
  have hψ0B : ψB 0 = 0 := by have := backB 0 ⟨le_rfl, hEB⟩; rwa [B.hp0] at this
  -- positivity of z inside
  have posA : ∀ t ∈ Ioo 0 L, 0 < qA (ψA t) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hψA t (hL1 (Ioo_subset_Ico_self ht))
    refine A.hpos _ (lt_of_le_of_ne h1.1 ?_)
    intro h; rw [← h, A.hp0] at h2; exact absurd h2 (ne_of_lt ht.1)
  have posB : ∀ t ∈ Ioo 0 L, 0 < qB (ψB t) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hψB t (hL2 (Ioo_subset_Ico_self ht))
    refine B.hpos _ (lt_of_le_of_ne h1.1 ?_)
    intro h; rw [← h, B.hp0] at h2; exact absurd h2 (ne_of_lt ht.1)
  have hzA0 : qA (ψA 0) = 0 := by rw [hψ0A, A.hq0]
  have hzB0 : qB (ψB 0) = 0 := by rw [hψ0B, B.hq0]
  have hF0 : fA (ψA 0) = fB (ψB 0) := by rw [hψ0A, hψ0B, A.hf0, B.hf0]
  have hnc := Work.FSSep.UCompare.no_cross_s hβ hLle posA posB
    (czA.mono hL1) (czB.mono hL2) (cFA.mono hL1) (cFB.mono hL2)
    (fun t ht => dFA t (hI1 ht)) (fun t ht => dFB t (hI2 ht))
    (fun t ht => dzA t (hI1 ht)) (fun t ht => dzB t (hI2 ht)) hzA0 hzB0 hF0
  -- E = FB − FA: monotone on [0, L), positive on (0, L)
  have hEm : MonotoneOn (fun t => fB (ψB t) - fA (ψA t)) (Ico 0 L) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => t / qB (ψB t) - t / qA (ψA t)) (convex_Ico 0 L)
      ((cFB.mono hL2).sub (cFA.mono hL1))
    · intro t ht
      rw [interior_Ico] at ht
      exact ((dFB t (hI2 ht)).sub (dFA t (hI1 ht))).hasDerivWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      have : t / qA (ψA t) ≤ t / qB (ψB t) :=
        div_le_div_of_nonneg_left ht.1.le (posB t ht) (hnc t ht).le
      linarith
  have hEp : ∀ t ∈ Ioo 0 L, fA (ψA t) < fB (ψB t) := by
    intro t ht
    have hsub : Icc 0 t ⊆ Ico 0 L := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hsm : StrictMonoOn (fun t => fB (ψB t) - fA (ψA t)) (Icc 0 t) := by
      apply strictMonoOn_of_hasDerivWithinAt_pos
        (f' := fun t => t / qB (ψB t) - t / qA (ψA t)) (convex_Icc 0 t)
        ((cFB.mono (hsub.trans hL2)).sub (cFA.mono (hsub.trans hL1)))
      · intro s hs
        rw [interior_Icc] at hs
        have hsI : s ∈ Ioo 0 L := ⟨hs.1, lt_trans hs.2 ht.2⟩
        exact ((dFB s (hI2 hsI)).sub (dFA s (hI1 hsI))).hasDerivWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hsI : s ∈ Ioo 0 L := ⟨hs.1, lt_trans hs.2 ht.2⟩
        have : s / qA (ψA s) < s / qB (ψB s) :=
          div_lt_div_of_pos_left hs.1 (posB s hsI) (hnc s hsI)
        linarith
    have := hsm ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩ ht.1
    simp only at this
    rw [hF0] at this
    linarith
  have inL : ∀ uA ∈ Ico 0 EA, ∀ uB ∈ Ico 0 EB, pA uA = pB uB → pA uA ∈ Ico 0 L := by
    intro uA huA uB huB he
    refine ⟨(A.bounds uA huA.1).1, lt_min ?_ ?_⟩
    · exact A.smono huA.1 (le_of_lt (lt_of_le_of_lt huA.1 huA.2)) huA.2
    · rw [he]; exact B.smono huB.1 (le_of_lt (lt_of_le_of_lt huB.1 huB.2)) huB.2
  have posLev : ∀ uA ∈ Ioo 0 EA, 0 < pA uA := by
    intro uA huA
    have := A.smono (mem_Ici.2 le_rfl) (mem_Ici.2 huA.1.le) huA.1
    rwa [A.hp0] at this
  refine ⟨?_, ?_, ?_⟩
  · intro uA huA uB huB he
    have huA' : uA ∈ Ico 0 EA := Ioo_subset_Ico_self huA
    have hin := inL uA huA' uB huB he
    have := hEp (pA uA) ⟨posLev uA huA, hin.2⟩
    rw [backA uA huA', he, backB uB huB] at this
    exact this
  · intro uA huA uB huB vA hvA vB hvB hu hv huv
    have hinu := inL uA huA uB huB hu
    have hinv := inL vA hvA vB hvB hv
    have := hEm hinu hinv huv
    simp only at this
    have e2 : ψB (pA uA) = uB := by rw [hu]; exact backB uB huB
    have e2v : ψB (pA vA) = vB := by rw [hv]; exact backB vB hvB
    rw [backA uA huA, backA vA hvA, e2, e2v] at this
    exact this
  · intro uA huA uB huB vA hvA vB hvB hu hv huv
    have huA' : uA ∈ Ico 0 EA := Ioo_subset_Ico_self huA
    have hinu := inL uA huA' uB huB hu
    have hinv := inL vA hvA vB hvB hv
    have hpos := posLev uA huA
    have hG : ∀ s ∈ Ioo 0 L, HasDerivAt (fun t => ψB t - fB (ψB t)) ((1 - s) / qB (ψB s)) s := by
      intro s hs
      have := (dψB s (hI2 hs)).sub (dFB s (hI2 hs))
      refine this.congr_deriv ?_
      have hne := (posB s hs).ne'
      field_simp
    have hcG : ContinuousOn (fun t => ψB t - fB (ψB t)) (Ico 0 L) :=
      (cψB.mono hL2).sub (cFB.mono hL2)
    have hD : qB (ψB (pA uA)) ≤ qA (ψA (pA uA)) := (hnc _ ⟨hpos, hinu.2⟩).le
    have h := Work.FSSep.UCompare.stepS (by linarith) hβB.le hLle hpos huv hinv.2 posA posB
      (czA.mono hL1) (czB.mono hL2) hcG
      (fun t ht => dzA t (hI1 ht)) (fun t ht => dzB t (hI2 ht)) hG hEm hD
    have e2 : ψB (pA uA) = uB := by rw [hu]; exact backB uB huB
    have e2v : ψB (pA vA) = vB := by rw [hv]; exact backB vB hvB
    rw [backA uA huA', backA vA hvA, e2, e2v] at h
    linarith

/-- The tail argument: a zero-wall-shear solution A with βA < βB cannot coexist with a
zero-wall-shear solution B in the decay class. -/
theorem sep_core {βA βB : ℝ} (hβ : βA < βB)
    {fA pA qA fB pB qB : ℝ → ℝ} (A : SolB βA fA pA qA) (B : SolB βB fB pB qB)
    (hexp : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - pB η) ≤ qB η) : False := by
  have hβB : βB < 0 := B.beta_neg
  have hbB : 0 < -βB := by linarith
  -- t* = pB 1 and its partner a on the curve of A
  have hb1 := B.bounds 1 (by norm_num)
  have htstar : 0 < pB 1 := by
    have := B.smono (mem_Ici.2 le_rfl) (show (1 : ℝ) ∈ Ici 0 by norm_num) one_pos
    rwa [B.hp0] at this
  obtain ⟨a, ha, hpa⟩ := A.reach htstar.le hb1.2
  have ha0 : 0 < a := by
    rcases eq_or_lt_of_le (mem_Ici.1 ha) with h | h
    · rw [← h, A.hp0] at hpa; linarith
    · exact h
  have hEstar : fA a < fB 1 :=
    (pairS hβ hβB (show 0 < a + 1 by linarith) (show (0 : ℝ) < 2 by norm_num) A B).1
      a ⟨ha0, by linarith⟩ 1 ⟨by norm_num, by norm_num⟩ hpa
  set Es := fB 1 - fA a with hEs
  have hEs0 : 0 < Es := by linarith
  set M := 4 * (-βB) / Es with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨N, hN⟩ := (hexp M).exists_forall_of_atTop
  set η₀ := max N 1 with hη₀
  have hη₀1 : 1 ≤ η₀ := le_max_right _ _
  have hη₀0 : 0 ≤ η₀ := by linarith
  have htail : ∀ η ∈ Ici η₀, M * (1 - pB η) ≤ qB η := fun η hη =>
    hN η (le_trans (le_max_left _ _) hη)
  set t₀ := pB η₀ with ht₀
  have hb0 := B.bounds η₀ hη₀0
  have ht₀star : pB 1 ≤ t₀ :=
    B.smono.monotoneOn (show (1 : ℝ) ∈ Ici 0 by norm_num) (mem_Ici.2 hη₀0) hη₀1
  set ε := Es * (1 - t₀) / 8 with hε
  have h1t₀ : 0 < 1 - t₀ := by linarith [hb0.2]
  have hε0 : 0 < ε := by rw [hε]; positivity
  -- a point of A beyond velocity (1 + t₀)/2 with small qA
  obtain ⟨T, hT0, hT⟩ := A.reach (s := (1 + t₀) / 2) (by linarith [hb0.1]) (by linarith [hb0.2])
  obtain ⟨η₂, hη₂T, hq₂⟩ := A.small hε0 hT0
  have hη₂0 : 0 ≤ η₂ := le_trans hT0 hη₂T
  set t := pA η₂ with ht
  have htT : (1 + t₀) / 2 ≤ t := by
    rw [← hT]; exact A.smono.monotoneOn hT0 (mem_Ici.2 hη₂0) hη₂T
  have hb2 := A.bounds η₂ hη₂0
  obtain ⟨x, hx0, hpx⟩ := B.reach (s := t) (by linarith [hb0.1]) hb2.2
  obtain ⟨b₀, hb₀0, hpb₀⟩ := A.reach (s := t₀) hb0.1 hb0.2
  have hxη₀ : η₀ ≤ x := by
    by_contra hc
    push Not at hc
    have := B.smono (mem_Ici.2 hx0) (mem_Ici.2 hη₀0) hc
    rw [hpx] at this
    linarith [hb0.2]
  have hη₂b : b₀ ≤ η₂ ∧ a ≤ b₀ := by
    constructor
    · by_contra hc
      push Not at hc
      have := A.smono (mem_Ici.2 hη₂0) (mem_Ici.2 hb₀0) hc
      rw [hpb₀] at this
      linarith [hb0.2]
    · by_contra hc
      push Not at hc
      have := A.smono (mem_Ici.2 hb₀0) ha hc
      rw [hpb₀, hpa] at this
      linarith
  have hb₀pos : 0 < b₀ := lt_of_lt_of_le ha0 hη₂b.2
  -- the final Crocco range
  set EA := η₂ + 1
  set EB := x + 1
  obtain ⟨_, hmon, hstep⟩ := pairS hβ hβB (show 0 < EA by linarith) (show 0 < EB by linarith) A B
  have hmemA : ∀ y, 0 ≤ y → y ≤ η₂ → y ∈ Ico 0 EA := fun y h0 h1 => ⟨h0, by linarith⟩
  have hmemB : ∀ y, 0 ≤ y → y ≤ x → y ∈ Ico 0 EB := fun y h0 h1 => ⟨h0, by linarith⟩
  -- E(t₀) ≥ E*
  have hEt₀ : Es ≤ fB η₀ - fA b₀ :=
    hmon a (hmemA a ha (le_trans hη₂b.2 hη₂b.1)) 1 (hmemB 1 zero_le_one (le_trans hη₀1 hxη₀))
      b₀ (hmemA b₀ hb₀0 hη₂b.1) η₀ (hmemB η₀ hη₀0 hxη₀) hpa (by rw [hpb₀])
      (by rw [hpa, hpb₀]; exact ht₀star)
  -- Step 1
  have h1 := hstep b₀ ⟨hb₀pos, by linarith⟩ η₀ (hmemB η₀ hη₀0 hxη₀) η₂ (hmemA η₂ hη₂0 le_rfl)
    x (hmemB x hx0 le_rfl) (by rw [hpb₀]) (by rw [hpx]) (by rw [hpb₀]; linarith)
  -- Step 2 (tail of B)
  have h2 := Work.FalknerSkan.NegUStep.step2 hM0 hη₀0 B.hf B.hp htail x hxη₀
  rw [hpx] at h2
  rw [hpb₀] at h1
  have hq₂x : 0 < qB x := B.hpos x (lt_of_lt_of_le (by linarith) hxη₀)
  -- combine
  have htt : 0 ≤ t - t₀ := by linarith [hb0.2]
  have hA : Es * (t - t₀) ≤ (fB η₀ - fA b₀) * (t - t₀) := mul_le_mul_of_nonneg_right hEt₀ htt
  have hB : 2 * (-βB) * ((t - t₀) / M) = Es * (t - t₀) / 2 := by
    have hβne : βB ≠ 0 := hβB.ne
    have hEne : Es ≠ 0 := hEs0.ne'
    rw [hM]; field_simp; ring
  have h2' : 2 * (-βB) * ((x - fB x) - (η₀ - fB η₀)) ≤ 2 * (-βB) * ((t - t₀) / M) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have hfin : Es * (t - t₀) / 2 ≤ ε := by linarith
  have hfin2 : Es * (1 - t₀) / 4 ≤ Es * (t - t₀) / 2 := by
    have := mul_le_mul_of_nonneg_left (show (1 - t₀) / 2 ≤ t - t₀ by linarith) hEs0.le
    linarith
  have : 0 < Es * (1 - t₀) := by positivity
  linarith

end Work.FSSep.UPair
