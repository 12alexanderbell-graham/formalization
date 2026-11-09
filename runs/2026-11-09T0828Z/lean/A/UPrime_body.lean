/-! Theorem U′ of the β < 0 research note (§2): among BVP solutions with q > 0 on [0, ∞), one
with a Gaussian-type tail (q ≥ M(1 − p) eventually, every M) has the largest wall shear. -/

namespace Scratch.UPrime
open Set Filter Topology
open Checked.FalknerSkan.LimitCore

/-- Hypotheses of one solution of the adverse-pressure system in the monotone class. -/
structure Sol (K : ℝ) (f p q : ℝ → ℝ) : Prop where
  hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η
  hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η
  hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η
  hf0 : f 0 = 0
  hp0 : p 0 = 0
  hlim : Tendsto p atTop (𝓝 1)
  hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η

theorem Sol.smono {K : ℝ} {f p q : ℝ → ℝ} (S : Sol K f p q) : StrictMonoOn p (Ici 0) :=
  Checked.FalknerSkan.CroccoWindow.smono_Ici S.hp S.hpos

theorem Sol.bounds {K : ℝ} {f p q : ℝ → ℝ} (S : Sol K f p q) :
    ∀ η ∈ Ici (0 : ℝ), 0 ≤ p η ∧ p η < 1 :=
  Checked.FalknerSkan.BoundedTools.bounded_of_pos S.hp S.hp0 S.hlim S.hpos

/-- Every velocity level s ∈ [0, 1) is reached. -/
theorem Sol.reach {K : ℝ} {f p q : ℝ → ℝ} (S : Sol K f p q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ u ∈ Ici (0 : ℝ), p u = s := by
  obtain ⟨R, hR⟩ := (S.hlim.eventually (lt_mem_nhds hs1)).exists_forall_of_atTop
  set R' := max R 0
  have hR' : s < p R' := hR R' (le_max_left _ _)
  have hc : ContinuousOn p (Icc 0 R') := cont_of S.hp le_rfl
  obtain ⟨u, hu, hpu⟩ := intermediate_value_Icc (le_max_right R 0) hc
    (show s ∈ Icc (p 0) (p R') by rw [S.hp0]; exact ⟨hs0, hR'.le⟩)
  exact ⟨u, hu.1, hpu⟩

/-- q stays above any ε > 0 on no half-line [T, ∞). -/
theorem Sol.small {K : ℝ} {f p q : ℝ → ℝ} (S : Sol K f p q) {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    ∃ η ∈ Ici T, q η < ε := by
  by_contra hcon
  push Not at hcon
  have hmono : ∀ η ∈ Ici T, p T + ε * (η - T) ≤ p η := by
    intro η hη
    have hg : ∀ x ∈ Ici (0 : ℝ),
        HasDerivWithinAt (fun y => p y - ε * y) (q x - ε * 1) (Ici 0) x := fun x hx =>
      (S.hp x hx).sub ((hasDerivWithinAt_id x _).const_mul ε)
    have hm := mono hg hT (b := η) (fun x hx => by
      have := hcon x hx.1.le
      linarith)
    have := hm ⟨le_refl T, hη⟩ ⟨hη, le_refl η⟩ hη
    simp only at this
    nlinarith
  have hpos' : 0 ≤ T + 1 / ε := by positivity
  have hb := S.bounds (T + 1 / ε) hpos'
  have hinv : 0 < 1 / ε := by positivity
  have := hmono (T + 1 / ε) (mem_Ici.2 (by linarith))
  have h1 : ε * (T + 1 / ε - T) = 1 := by field_simp; ring
  have h2 := (S.bounds T hT).1
  linarith [hb.2]

/-- The two Crocco curves on a common range, read at points of equal velocity. -/
theorem pair {K E₁ E₂ : ℝ} (hK : 0 < K) (hE₁ : 0 < E₁) (hE₂ : 0 < E₂)
    {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ} (S₁ : Sol K f₁ p₁ q₁) (S₂ : Sol K f₂ p₂ q₂)
    (hlt : q₁ 0 < q₂ 0) :
    (∀ u₁ ∈ Ioo 0 E₁, ∀ u₂ ∈ Ico 0 E₂, p₁ u₁ = p₂ u₂ → f₂ u₂ < f₁ u₁) ∧
    (∀ u₁ ∈ Ico 0 E₁, ∀ u₂ ∈ Ico 0 E₂, ∀ v₁ ∈ Ico 0 E₁, ∀ v₂ ∈ Ico 0 E₂,
      p₁ u₁ = p₂ u₂ → p₁ v₁ = p₂ v₂ → p₁ u₁ ≤ p₁ v₁ → f₁ u₁ - f₂ u₂ ≤ f₁ v₁ - f₂ v₂) ∧
    (∀ u₁ ∈ Ioo 0 E₁, ∀ u₂ ∈ Ico 0 E₂, ∀ v₁ ∈ Ico 0 E₁, ∀ v₂ ∈ Ico 0 E₂,
      p₁ u₁ = p₂ u₂ → p₁ v₁ = p₂ v₂ → p₁ u₁ ≤ p₁ v₁ →
      K * (f₁ u₁ - f₂ u₂) * (p₁ v₁ - p₁ u₁) ≤ q₂ v₂ - q₁ v₁ + 2 * ((v₁ - f₁ v₁) - (u₁ - f₁ u₁))) := by
  have restrict : ∀ {g g' : ℝ → ℝ} {E : ℝ},
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η) →
      ∀ η ∈ Icc 0 E, HasDerivWithinAt g (g' η) (Icc 0 E) η := fun hg η hη =>
    (hg η hη.1).mono Icc_subset_Ici_self
  obtain ⟨ψ₁, hψ₁, hψp₁, cz₁, cF₁, dF₁, dz₁, cψ₁, dψ₁⟩ :=
    Scratch.NegCrocco.crocco_pos hE₁ (restrict S₁.hf) (restrict S₁.hp) (restrict S₁.hq) S₁.hp0
      (fun η hη => S₁.hpos η hη.1)
  obtain ⟨ψ₂, hψ₂, hψp₂, cz₂, cF₂, dF₂, dz₂, _, _⟩ :=
    Scratch.NegCrocco.crocco_pos hE₂ (restrict S₂.hf) (restrict S₂.hp) (restrict S₂.hq) S₂.hp0
      (fun η hη => S₂.hpos η hη.1)
  set L := min (p₁ E₁) (p₂ E₂) with hL
  have hL1 : Ico 0 L ⊆ Ico 0 (p₁ E₁) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hL2 : Ico 0 L ⊆ Ico 0 (p₂ E₂) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hI1 : Ioo 0 L ⊆ Ioo 0 (p₁ E₁) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hI2 : Ioo 0 L ⊆ Ioo 0 (p₂ E₂) := fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
  have hLle : L ≤ 1 := le_trans (min_le_left _ _) (S₁.bounds E₁ hE₁.le).2.le
  have hz₁ : ∀ t ∈ Ico 0 L, 0 < q₁ (ψ₁ t) := fun t ht => S₁.hpos _ (hψ₁ t (hL1 ht)).1.1
  have hz₂ : ∀ t ∈ Ico 0 L, 0 < q₂ (ψ₂ t) := fun t ht => S₂.hpos _ (hψ₂ t (hL2 ht)).1.1
  have hψ0₁ : ψ₁ 0 = 0 := by have := hψp₁ 0 ⟨le_rfl, hE₁⟩; rwa [S₁.hp0] at this
  have hψ0₂ : ψ₂ 0 = 0 := by have := hψp₂ 0 ⟨le_rfl, hE₂⟩; rwa [S₂.hp0] at this
  have hF0 : f₁ (ψ₁ 0) = f₂ (ψ₂ 0) := by rw [hψ0₁, hψ0₂, S₁.hf0, S₂.hf0]
  have hz0 : q₁ (ψ₁ 0) < q₂ (ψ₂ 0) := by rw [hψ0₁, hψ0₂]; exact hlt
  obtain ⟨hEmono, hEpos⟩ := Scratch.NoCross.no_cross_E hK hz₁
    (cz₁.mono hL1) (cz₂.mono hL2) (cF₁.mono hL1) (cF₂.mono hL2)
    (fun t ht => dF₁ t (hI1 ht)) (fun t ht => dF₂ t (hI2 ht))
    (fun t ht => dz₁ t (hI1 ht)) (fun t ht => dz₂ t (hI2 ht)) hF0 hz0
  have hnc := Scratch.NoCross.no_cross hK hz₁
    (cz₁.mono hL1) (cz₂.mono hL2) (cF₁.mono hL1) (cF₂.mono hL2)
    (fun t ht => dF₁ t (hI1 ht)) (fun t ht => dF₂ t (hI2 ht))
    (fun t ht => dz₁ t (hI1 ht)) (fun t ht => dz₂ t (hI2 ht)) hF0 hz0
  -- a point of Ico 0 E₁ has velocity in Ico 0 L when it equals a velocity of the other
  have inL : ∀ u₁ ∈ Ico 0 E₁, ∀ u₂ ∈ Ico 0 E₂, p₁ u₁ = p₂ u₂ → p₁ u₁ ∈ Ico 0 L := by
    intro u₁ hu₁ u₂ hu₂ he
    refine ⟨(S₁.bounds u₁ hu₁.1).1, lt_min ?_ ?_⟩
    · exact S₁.smono hu₁.1 (le_of_lt (lt_of_le_of_lt hu₁.1 hu₁.2)) hu₁.2
    · rw [he]; exact S₂.smono hu₂.1 (le_of_lt (lt_of_le_of_lt hu₂.1 hu₂.2)) hu₂.2
  have back₁ : ∀ u₁ ∈ Ico 0 E₁, ψ₁ (p₁ u₁) = u₁ := hψp₁
  have back₂ : ∀ u₂ ∈ Ico 0 E₂, ψ₂ (p₂ u₂) = u₂ := hψp₂
  refine ⟨?_, ?_, ?_⟩
  · intro u₁ hu₁ u₂ hu₂ he
    have hu₁' : u₁ ∈ Ico 0 E₁ := Ioo_subset_Ico_self hu₁
    have hin := inL u₁ hu₁' u₂ hu₂ he
    have hpos : 0 < p₁ u₁ := by
      have := S₁.smono (mem_Ici.2 le_rfl) hu₁'.1 hu₁.1
      rwa [S₁.hp0] at this
    have := hEpos (p₁ u₁) ⟨hpos, hin.2⟩
    rw [back₁ u₁ hu₁', he, back₂ u₂ hu₂] at this
    exact this
  · intro u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ hu hv huv
    have hinu := inL u₁ hu₁ u₂ hu₂ hu
    have hinv := inL v₁ hv₁ v₂ hv₂ hv
    have := hEmono hinu hinv huv
    simp only at this
    have e2 : ψ₂ (p₁ u₁) = u₂ := by rw [hu]; exact back₂ u₂ hu₂
    have e2v : ψ₂ (p₁ v₁) = v₂ := by rw [hv]; exact back₂ v₂ hv₂
    rw [back₁ u₁ hu₁, back₁ v₁ hv₁, e2, e2v] at this
    exact this
  · intro u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ hu hv huv
    have hu₁' : u₁ ∈ Ico 0 E₁ := Ioo_subset_Ico_self hu₁
    have hinu := inL u₁ hu₁' u₂ hu₂ hu
    have hinv := inL v₁ hv₁ v₂ hv₂ hv
    have hpos : 0 < p₁ u₁ := by
      have := S₁.smono (mem_Ici.2 le_rfl) hu₁'.1 hu₁.1
      rwa [S₁.hp0] at this
    have hG : ∀ s ∈ Ioo 0 L, HasDerivAt (fun t => ψ₁ t - f₁ (ψ₁ t)) ((1 - s) / q₁ (ψ₁ s)) s := by
      intro s hs
      have := (dψ₁ s (hI1 hs)).sub (dF₁ s (hI1 hs))
      refine this.congr_deriv ?_
      have hne := (hz₁ s (Ioo_subset_Ico_self hs)).ne'
      field_simp
    have hcG : ContinuousOn (fun t => ψ₁ t - f₁ (ψ₁ t)) (Ico 0 L) :=
      (cψ₁.mono hL1).sub (cF₁.mono hL1)
    have hD : q₁ (ψ₁ (p₁ u₁)) ≤ q₂ (ψ₂ (p₁ u₁)) := (hnc _ hinu).le
    have h := Scratch.UStep.step1 hK.le hLle hpos huv hinv.2 hz₁ hz₂
      (cz₁.mono hL1) (cz₂.mono hL2) hcG
      (fun t ht => dz₁ t (hI1 ht)) (fun t ht => dz₂ t (hI2 ht)) hG hEmono hD
    have e2 : ψ₂ (p₁ u₁) = u₂ := by rw [hu]; exact back₂ u₂ hu₂
    have e2v : ψ₂ (p₁ v₁) = v₂ := by rw [hv]; exact back₂ v₂ hv₂
    rw [back₁ u₁ hu₁', back₁ v₁ hv₁, e2, e2v] at h
    linarith

/-- Theorem U′: a solution in the monotone class with the Gaussian-type tail has wall shear at
least that of any solution in the monotone class (adverse pressure, any K > 0). -/
theorem u_prime {K : ℝ} (hK : 0 < K)
    {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ} (S₁ : Sol K f₁ p₁ q₁) (S₂ : Sol K f₂ p₂ q₂)
    (hexp : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₁ η) ≤ q₁ η) :
    q₂ 0 ≤ q₁ 0 := by
  by_contra hcon
  push Not at hcon
  -- t* = p₁ 1 and its partner on the second curve
  have hb1 := S₁.bounds 1 (by norm_num)
  have htstar : 0 < p₁ 1 := by
    have := S₁.smono (mem_Ici.2 le_rfl) (show (1 : ℝ) ∈ Ici 0 by norm_num) one_pos
    rwa [S₁.hp0] at this
  obtain ⟨a₂, ha₂, hpa₂⟩ := S₂.reach htstar.le hb1.2
  -- E* > 0
  have hEstar : f₂ a₂ < f₁ 1 :=
    (pair hK (show (0 : ℝ) < 2 by norm_num) (show 0 < a₂ + 1 by linarith [mem_Ici.1 ha₂])
      S₁ S₂ hcon).1 1 ⟨one_pos, by norm_num⟩ a₂ ⟨ha₂, by linarith⟩ hpa₂.symm
  set Es := f₁ 1 - f₂ a₂ with hEs
  have hEs0 : 0 < Es := by linarith
  set M := 4 / (K * Es) with hM
  have hKE : 0 < K * Es := mul_pos hK hEs0
  have hM0 : 0 < M := by positivity
  obtain ⟨N, hN⟩ := (hexp M).exists_forall_of_atTop
  set η₀ := max N 1 with hη₀
  have hη₀1 : 1 ≤ η₀ := le_max_right _ _
  have hη₀0 : 0 ≤ η₀ := by linarith
  have htail : ∀ η ∈ Ici η₀, M * (1 - p₁ η) ≤ q₁ η := fun η hη =>
    hN η (le_trans (le_max_left _ _) hη)
  set t₀ := p₁ η₀ with ht₀
  have hb0 := S₁.bounds η₀ hη₀0
  have ht₀star : p₁ 1 ≤ t₀ :=
    S₁.smono.monotoneOn (show (1 : ℝ) ∈ Ici 0 by norm_num) (mem_Ici.2 hη₀0) hη₀1
  set ε := K * Es * (1 - t₀) / 8 with hε
  have h1t₀ : 0 < 1 - t₀ := by linarith [hb0.2]
  have hε0 : 0 < ε := by rw [hε]; positivity
  -- a point of the second curve beyond velocity (1 + t₀)/2 with small q₂
  obtain ⟨T, hT0, hT⟩ := S₂.reach (s := (1 + t₀) / 2) (by linarith [hb0.1]) (by linarith [hb0.2])
  obtain ⟨η₂, hη₂T, hq₂⟩ := S₂.small hε0 hT0
  have hη₂0 : 0 ≤ η₂ := le_trans hT0 hη₂T
  set t := p₂ η₂ with ht
  have htT : (1 + t₀) / 2 ≤ t := by
    rw [← hT]; exact S₂.smono.monotoneOn hT0 (mem_Ici.2 hη₂0) hη₂T
  have hb2 := S₂.bounds η₂ hη₂0
  obtain ⟨x, hx0, hpx⟩ := S₁.reach (s := t) (by linarith [hb0.1]) hb2.2
  obtain ⟨b₀, hb₀0, hpb₀⟩ := S₂.reach (s := t₀) hb0.1 hb0.2
  have hxη₀ : η₀ ≤ x := by
    by_contra hc
    push Not at hc
    have := S₁.smono (mem_Ici.2 hx0) (mem_Ici.2 hη₀0) hc
    rw [hpx] at this
    linarith [hb0.2]
  have hη₂b : b₀ ≤ η₂ ∧ a₂ ≤ b₀ := by
    constructor
    · by_contra hc
      push Not at hc
      have := S₂.smono (mem_Ici.2 hη₂0) (mem_Ici.2 hb₀0) hc
      rw [hpb₀] at this
      linarith [hb0.2]
    · by_contra hc
      push Not at hc
      have := S₂.smono (mem_Ici.2 hb₀0) ha₂ hc
      rw [hpb₀, hpa₂] at this
      linarith
  -- the final Crocco range
  set E₁ := x + 1
  set E₂ := η₂ + 1
  obtain ⟨_, hmon, hstep⟩ := pair hK (show 0 < E₁ by linarith) (show 0 < E₂ by linarith) S₁ S₂ hcon
  have hmem1 : ∀ y, 0 ≤ y → y ≤ x → y ∈ Ico 0 E₁ := fun y h0 h1 => ⟨h0, by linarith⟩
  have hmem2 : ∀ y, 0 ≤ y → y ≤ η₂ → y ∈ Ico 0 E₂ := fun y h0 h1 => ⟨h0, by linarith⟩
  -- E(t₀) ≥ E*
  have hEt₀ : Es ≤ f₁ η₀ - f₂ b₀ :=
    hmon 1 (hmem1 1 zero_le_one (le_trans hη₀1 hxη₀)) a₂ (hmem2 a₂ ha₂ (le_trans hη₂b.2 hη₂b.1))
      η₀ (hmem1 η₀ hη₀0 hxη₀) b₀ (hmem2 b₀ hb₀0 hη₂b.1) hpa₂.symm (by rw [hpb₀]) ht₀star
  -- Step 1
  have h1 := hstep η₀ ⟨by linarith, by linarith⟩ b₀ (hmem2 b₀ hb₀0 hη₂b.1) x (hmem1 x hx0 le_rfl)
    η₂ (hmem2 η₂ hη₂0 le_rfl) (by rw [hpb₀]) (by rw [hpx]) (by rw [hpx]; linarith)
  -- Step 2
  have h2 := Scratch.UStep.step2 hM0 hη₀0 S₁.hf S₁.hp htail x hxη₀
  rw [hpx] at h1 h2
  have hq₁x : 0 < q₁ x := S₁.hpos x hx0
  -- combine
  have htt : 0 ≤ t - t₀ := by linarith [hb0.2]
  have hA : K * Es * (t - t₀) ≤ K * (f₁ η₀ - f₂ b₀) * (t - t₀) := by
    have := mul_le_mul_of_nonneg_left hEt₀ hK.le
    exact mul_le_mul_of_nonneg_right this htt
  have hB : 2 * ((t - t₀) / M) = K * Es * (t - t₀) / 2 := by
    rw [hM]; field_simp; ring
  have hfin : K * Es * (t - t₀) / 2 ≤ ε := by nlinarith
  have hfin2 : K * Es * (1 - t₀) / 4 ≤ K * Es * (t - t₀) / 2 := by
    have := mul_le_mul_of_nonneg_left (show (1 - t₀) / 2 ≤ t - t₀ by linarith) hKE.le
    linarith
  have : 0 < K * Es * (1 - t₀) := by positivity
  linarith

/-- Theorem U: two solutions of the monotone class with the Gaussian-type tail have the same wall
shear. -/
theorem u_equal_shear {K : ℝ} (hK : 0 < K)
    {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ} (S₁ : Sol K f₁ p₁ q₁) (S₂ : Sol K f₂ p₂ q₂)
    (hexp₁ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₁ η) ≤ q₁ η)
    (hexp₂ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) :
    q₁ 0 = q₂ 0 :=
  le_antisymm (u_prime hK S₂ S₁ hexp₂) (u_prime hK S₁ S₂ hexp₁)

end Scratch.UPrime

#print axioms Scratch.UPrime.u_prime
#print axioms Scratch.UPrime.u_equal_shear
