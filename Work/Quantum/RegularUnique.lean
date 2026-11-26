import Work.Quantum.H2PlusConditional
/-!
# Solutions regular through ξ = 1 are the Frobenius solution; the certificate interface (run 2026-11-26T2228Z)

`H2PlusConditional.freeze_of_certificate` asks the certificate (route step 4) for `UnderAll k₁ A` and `OverAll k₂ A`:
statements about every radial solution regular through ξ = 1 with L(1) = 1. Here they are reduced to statements
about one initial value problem the certificate can compute:
* `regular_eq`: such a solution equals the Frobenius solution of `RadialStart` on [1, 2], and L′(2) is the
  Frobenius slope — the flux Wronskian W = L₁·(ξ² − 1)L′ − L·(ξ² − 1)L₁′ has derivative 0 and vanishes at ξ = 1;
  near 1, where L₁ > 0, (L/L₁)′ = W/((ξ² − 1)L₁²) = 0; past that, uniqueness for the regular linear system.
* `UnderIVP`, `OverIVP`: the sign facts for the Frobenius piece on [1, 2] and for every solution of the regular
  system L′ = P/(ξ² − 1), P′ = −(4ξ − kξ² + A)L on [2, T] from the Frobenius state (L(2), P(2)) = (RL(1), 3·RL′(1));
  `underAll_of_IVP`, `overAll_of_IVP` give the hypotheses of `freeze_of_certificate`. No numerics.
-/

namespace Work.Quantum.RegularUnique
open Set Filter Topology
open Work.Quantum.RadialStart (RL RLd RL_one radial_ode)
open Work.Quantum.RadialGlobal (vf)
open Work.Quantum.H2PlusConditional (UnderAll OverAll)

variable {k A : ℝ}

/-- The regular solution system: L′ and ((ξ² − 1)L′)′ on ξ > −1/4. -/
def Sol (k A : ℝ) (L L' : ℝ → ℝ) : Prop :=
  ∀ x, -(1 / 4 : ℝ) < x → HasDerivAt L (L' x) x ∧
    HasDerivAt (fun y => (y ^ 2 - 1) * L' y) (-((4 * x - k * x ^ 2 + A) * L x)) x

theorem regular_eq (hk : k ∈ Icc (0 : ℝ) 3) (hA : A ∈ Icc (0 : ℝ) 3) {L L' : ℝ → ℝ} (h1 : L 1 = 1)
    (hs : Sol k A L L') : (∀ x ∈ Icc (1 : ℝ) 2, L x = RL k A (x - 1)) ∧ L' 2 = RLd k A 1 := by
  set L₁ : ℝ → ℝ := fun x => RL k A (x - 1)
  set D₁ : ℝ → ℝ := fun x => RLd k A (x - 1)
  have hF : ∀ x ∈ Ioo (-(1 / 4 : ℝ)) (9 / 4), HasDerivAt L₁ (D₁ x) x ∧
      HasDerivAt (fun y => (y ^ 2 - 1) * D₁ y) (-((4 * x - k * x ^ 2 + A) * L₁ x)) x :=
    fun x hx => radial_ode hk hA hx
  -- the flux Wronskian vanishes on [1, 2]
  set W : ℝ → ℝ := fun x => L₁ x * ((x ^ 2 - 1) * L' x) - L x * ((x ^ 2 - 1) * D₁ x)
  have hW : ∀ x ∈ Ioo (-(1 / 4 : ℝ)) (9 / 4), HasDerivAt W 0 x := by
    intro x hx
    obtain ⟨a1, a2⟩ := hF x hx
    obtain ⟨b1, b2⟩ := hs x (by linarith [hx.1])
    have := (a1.mul b2).sub (b1.mul a2)
    convert this using 1
    ring
  have hW0 : ∀ x ∈ Icc (1 : ℝ) 2, W x = 0 := by
    have hc : ContinuousOn W (Icc 1 2) := fun x hx =>
      (hW x ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    have := constant_of_has_deriv_right_zero hc (fun x hx => (hW x ⟨by linarith [hx.1], by linarith [hx.2]⟩).hasDerivWithinAt)
    intro x hx
    rw [this x hx]
    simp [W]
  -- L₁ > 0 near 1
  have hL₁1 : L₁ 1 = 1 := by simp only [L₁, sub_self]; exact RL_one k A
  have hcont₁ : ContinuousAt L₁ 1 := (hF 1 ⟨by norm_num, by norm_num⟩).1.continuousAt
  obtain ⟨δ', hδ', hδ'L⟩ := Metric.continuousAt_iff.mp hcont₁ (1 / 2) (by norm_num)
  set δ := min (δ' / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hpos₁ : ∀ x ∈ Icc (1 : ℝ) (1 + δ), 0 < L₁ x := by
    intro x hx
    have hd : dist x 1 < δ' := by
      rw [Real.dist_eq, abs_lt]; constructor <;> [linarith [hx.1]; linarith [hx.2, min_le_left (δ' / 2) (1 / 2)]]
    have := hδ'L hd
    rw [Real.dist_eq, hL₁1, abs_lt] at this
    linarith [this.1]
  -- L = L₁ on [1, 1 + δ] by the mean value theorem for L / L₁
  have heq1 : ∀ x ∈ Icc (1 : ℝ) (1 + δ), L x = L₁ x := by
    intro x hx
    rcases hx.1.lt_or_eq with hlt | heq
    · set q : ℝ → ℝ := fun y => L y / L₁ y
      have hqd : ∀ y ∈ Ioo 1 x, HasDerivAt q 0 y := by
        intro y hy
        have hy' : y ∈ Icc (1 : ℝ) (1 + δ) := ⟨hy.1.le, hy.2.le.trans hx.2⟩
        have hL₁y := hpos₁ y hy'
        have hyF : y ∈ Ioo (-(1 / 4 : ℝ)) (9 / 4) := ⟨by linarith [hy.1], by linarith [hy'.2]⟩
        have hd := (hs y (by linarith [hy.1])).1.div (hF y hyF).1 hL₁y.ne'
        convert hd using 1
        -- W = 0 with y² − 1 > 0 gives L′ L₁ = L D₁
        have hWy := hW0 y ⟨hy.1.le, by linarith [hy'.2]⟩
        have hy2 : 0 < y ^ 2 - 1 := by nlinarith [hy.1]
        have : L' y * L₁ y - L y * D₁ y = 0 := by
          have e : W y = (y ^ 2 - 1) * (L' y * L₁ y - L y * D₁ y) := by simp only [W]; ring
          rw [e] at hWy
          rcases mul_eq_zero.mp hWy with h | h
          · linarith
          · exact h
        rw [this, zero_div]
      have hqc : ContinuousOn q (Icc 1 x) := by
        intro y hy
        have hy' : y ∈ Icc (1 : ℝ) (1 + δ) := ⟨hy.1, hy.2.trans hx.2⟩
        have hyF : y ∈ Ioo (-(1 / 4 : ℝ)) (9 / 4) := ⟨by linarith [hy.1], by linarith [hy'.2]⟩
        exact ((hs y (by linarith [hy.1])).1.continuousAt.div (hF y hyF).1.continuousAt
          (hpos₁ y hy').ne').continuousWithinAt
      obtain ⟨c, hc, hcq⟩ := exists_hasDerivAt_eq_slope q (fun _ => (0 : ℝ)) hlt hqc hqd
      have hq : q x = q 1 := by
        have hx1 : x - 1 ≠ 0 := by linarith
        field_simp at hcq
        linarith
      simp only [q, h1, hL₁1, div_one] at hq
      have := hpos₁ x hx
      field_simp at hq
      linarith
    · rw [← heq, h1, hL₁1]
  -- regular uniqueness on [1 + δ, 2]
  set c := 1 + δ
  have hc1 : 1 < c := by linarith
  have hc2 : c ≤ 2 := by linarith
  obtain ⟨hk3, hA3⟩ : |k| ≤ 3 ∧ |A| ≤ 3 :=
    ⟨abs_le.mpr ⟨by linarith [hk.1], hk.2⟩, abs_le.mpr ⟨by linarith [hA.1], hA.2⟩⟩
  set f : ℝ → ℝ × ℝ := fun t => (L t, (t ^ 2 - 1) * L' t)
  set g : ℝ → ℝ × ℝ := fun t => (L₁ t, (t ^ 2 - 1) * D₁ t)
  have hfd : ∀ t, 1 < t → HasDerivAt f (vf k A t (f t)) t := by
    intro t ht
    have hne : t ^ 2 - 1 ≠ 0 := by nlinarith
    refine ((hs t (by linarith)).1.prodMk (hs t (by linarith)).2).congr_deriv ?_
    simp only [vf, f]
    congr 1
    field_simp
  have hgd : ∀ t, 1 < t → t ≤ 2 → HasDerivAt g (vf k A t (g t)) t := by
    intro t ht ht2
    have hne : t ^ 2 - 1 ≠ 0 := by nlinarith
    have hF' := hF t ⟨by linarith, by linarith⟩
    refine (hF'.1.prodMk hF'.2).congr_deriv ?_
    simp only [vf, g]
    congr 1
    field_simp
  have hfg : f c = g c := by
    have hLc := heq1 c ⟨hc1.le, le_rfl⟩
    have hWc := hW0 c ⟨hc1.le, hc2⟩
    have hpc := hpos₁ c ⟨hc1.le, le_rfl⟩
    simp only [f, g, Prod.mk.injEq]
    refine ⟨hLc, ?_⟩
    simp only [W] at hWc
    rw [hLc] at hWc
    have := mul_left_cancel₀ hpc.ne' (sub_eq_zero.mp hWc)
    exact this
  have hu := ODE_solution_unique_of_mem_Icc_right (v := vf k A) (s := fun _ => univ)
    (K := Real.toNNReal (1 / (c ^ 2 - 1) + (4 * 2 + 3 * 2 ^ 2 + 3))) (f := f) (g := g) (a := c) (b := 2)
    (fun t ht => (H2Events.lip_sys hk3 hA3 hc1 (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hfd t (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => (hfd t (by linarith [ht.1])).hasDerivWithinAt) (fun _ _ => mem_univ _)
    (fun t ht => (hgd t (by linarith [ht.1]) ht.2).continuousAt.continuousWithinAt)
    (fun t ht => (hgd t (by linarith [ht.1]) ht.2.le).hasDerivWithinAt) (fun _ _ => mem_univ _) hfg
  refine ⟨fun x hx => ?_, ?_⟩
  · by_cases hxc : x ≤ c
    · exact heq1 x ⟨hx.1, hxc⟩
    · push Not at hxc
      have := hu ⟨hxc.le, hx.2⟩
      simp only [f, g, Prod.mk.injEq] at this
      exact this.1
  · have := hu ⟨hc2, le_rfl⟩
    simp only [f, g, Prod.mk.injEq] at this
    have h3 : ((2 : ℝ) ^ 2 - 1) ≠ 0 := by norm_num
    have := mul_left_cancel₀ h3 this.2
    rw [this]
    simp only [D₁]
    norm_num

/-- The certificate's form of "under": the Frobenius piece or the regular IVP from ξ = 2 goes negative. -/
def UnderIVP (k A : ℝ) : Prop :=
  (∃ ξ ∈ Icc (1 : ℝ) 2, RL k A (ξ - 1) < 0) ∨
  ∃ T, 2 ≤ T ∧ ∀ f : ℝ → ℝ × ℝ, f 2 = (RL k A 1, 3 * RLd k A 1) →
    (∀ t ∈ Icc (2 : ℝ) T, HasDerivWithinAt f (vf k A t (f t)) (Icc 2 T) t) → ∃ ξ ∈ Icc (2 : ℝ) T, (f ξ).1 < 0

/-- The certificate's form of "over": the Frobenius piece is positive on [1, 2] and the regular IVP from ξ = 2 is
positive on [2, b] with P(b) > 0. -/
def OverIVP (k A : ℝ) : Prop :=
  (∀ ξ ∈ Icc (1 : ℝ) 2, 0 < RL k A (ξ - 1)) ∧
  ∃ b, 5 / 2 ≤ b ∧ ∀ f : ℝ → ℝ × ℝ, f 2 = (RL k A 1, 3 * RLd k A 1) →
    (∀ t ∈ Icc (2 : ℝ) b, HasDerivWithinAt f (vf k A t (f t)) (Icc 2 b) t) →
    (∀ ξ ∈ Icc (2 : ℝ) b, 0 < (f ξ).1) ∧ 0 < (f b).2

theorem ivp_of_sol (hk : k ∈ Icc (0 : ℝ) 3) (hA : A ∈ Icc (0 : ℝ) 3) {L L' : ℝ → ℝ} (h1 : L 1 = 1)
    (hs : Sol k A L L') {T : ℝ} :
    (fun t => (L t, (t ^ 2 - 1) * L' t)) 2 = (RL k A 1, 3 * RLd k A 1) ∧
    ∀ t ∈ Icc (2 : ℝ) T, HasDerivWithinAt (fun t => (L t, (t ^ 2 - 1) * L' t))
      (vf k A t ((fun t => (L t, (t ^ 2 - 1) * L' t)) t)) (Icc 2 T) t := by
  obtain ⟨he, hd⟩ := regular_eq hk hA h1 hs
  refine ⟨?_, fun t ht => ?_⟩
  · have := he 2 ⟨by norm_num, le_rfl⟩
    simp only [Prod.mk.injEq]
    refine ⟨by rw [this]; norm_num, by rw [hd]; norm_num⟩
  · have hne : t ^ 2 - 1 ≠ 0 := by nlinarith [ht.1]
    refine (((hs t (by linarith [ht.1])).1.prodMk (hs t (by linarith [ht.1])).2).congr_deriv ?_).hasDerivWithinAt
    simp only [vf]
    congr 1
    field_simp

theorem underAll_of_IVP (hk : k ∈ Icc (0 : ℝ) 3) (hA : A ∈ Icc (0 : ℝ) 3) (h : UnderIVP k A) : UnderAll k A := by
  intro L L' h1 hs
  obtain ⟨he, -⟩ := regular_eq hk hA h1 hs
  rcases h with ⟨ξ, hξ, hneg⟩ | ⟨T, hT, hf⟩
  · exact ⟨ξ, hξ.1, by rw [he ξ hξ]; exact hneg⟩
  · obtain ⟨h2, hd⟩ := ivp_of_sol (T := T) hk hA h1 hs
    obtain ⟨ξ, hξ, hneg⟩ := hf _ h2 hd
    exact ⟨ξ, by linarith [hξ.1], hneg⟩

theorem overAll_of_IVP (hk : k ∈ Icc (0 : ℝ) 3) (hA : A ∈ Icc (0 : ℝ) 3) (h : OverIVP k A) : OverAll k A := by
  intro L L' h1 hs
  obtain ⟨he, -⟩ := regular_eq hk hA h1 hs
  obtain ⟨hfro, b, hb, hf⟩ := h
  obtain ⟨h2, hd⟩ := ivp_of_sol (T := b) hk hA h1 hs
  obtain ⟨hp, hP⟩ := hf _ h2 hd
  refine ⟨b, hb, fun ξ hξ => ?_, ?_⟩
  · by_cases h2' : ξ ≤ 2
    · rw [he ξ ⟨hξ.1, h2'⟩]; exact hfro ξ ⟨hξ.1, h2'⟩
    · push Not at h2'
      exact hp ξ ⟨h2'.le, hξ.2⟩
  · have hb2 : 0 < b ^ 2 - 1 := by nlinarith
    simp only at hP
    exact pos_of_mul_pos_right hP hb2.le

/-- **The frozen H₂⁺ statement from the certificate facts in IVP form** (what route step 4 must certify). -/
theorem freeze_of_IVP_certificate {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (hM : ∀ k ∈ Icc H2PlusConditional.k₁ H2PlusConditional.k₂, ∀ A ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      0 < AngularAssembly.M k A s)
    (hlo : ∀ k ∈ Icc H2PlusConditional.k₁ H2PlusConditional.k₂, AngularAssembly.g k a < 0)
    (hhi : ∀ k ∈ Icc H2PlusConditional.k₁ H2PlusConditional.k₂, 0 < AngularAssembly.g k b)
    (hunder : ∀ A ∈ Icc a b, UnderIVP H2PlusConditional.k₁ A)
    (hover : ∀ A ∈ Icc a b, OverIVP H2PlusConditional.k₂ A) :
    H2PlusBlindClosed.Freeze := by
  have hk₁ : H2PlusConditional.k₁ ∈ Icc (0 : ℝ) 3 := by unfold H2PlusConditional.k₁; constructor <;> norm_num
  have hk₂ : H2PlusConditional.k₂ ∈ Icc (0 : ℝ) 3 := by unfold H2PlusConditional.k₂; constructor <;> norm_num
  exact H2PlusConditional.freeze_of_certificate ha hab hb hM hlo hhi
    (fun A hA => underAll_of_IVP hk₁ ⟨ha.trans hA.1, hA.2.trans hb⟩ (hunder A hA))
    (fun A hA => overAll_of_IVP hk₂ ⟨ha.trans hA.1, hA.2.trans hb⟩ (hover A hA))

end Work.Quantum.RegularUnique
