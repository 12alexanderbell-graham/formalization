import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Checked.Math.BEH2Main
import Checked.Math.BEOChain
import Checked.Math.BEOTail

/-! Bonnor–Ebert sphere, `BEOMain`: the assembly of `BEH2Main` (the first three extrema of the mass) continued by the one-sided cells of `BEOChain`: the zero of 2u − v in the bracket of the second minimum, the monotonicity of u v³ on either side of it from the second-maximum bracket on, and Volterra's function beyond the cells (`BEOTail`, bound from below). Promoted from `Work/Math/BEOMain.lean`. -/

namespace Checked.Math.BEOMain
open Set Checked.Math.BEHMain

/-- The mass window at the second minimum from the window of u (v = 2u there). -/
theorem win_M {M U : ℝ} (hM : M ^ 2 * (4 * Real.pi) = 8 * U ^ 4) (hMpos : 0 < M)
    (u1 : 99378175 / 100000000 ≤ U) (u2 : U ≤ 99378323 / 100000000) : 0.787992 ≤ M ∧ M ≤ 0.787995 := by
  have pil := Real.pi_gt_d20
  have pih := Real.pi_lt_d20
  have v4l : (99378175 / 100000000 : ℝ) ^ 4 ≤ U ^ 4 := pow_le_pow_left₀ (by norm_num) u1 4
  have v4h : U ^ 4 ≤ (99378323 / 100000000 : ℝ) ^ 4 := pow_le_pow_left₀ (by linarith) u2 4
  constructor
  · by_contra hc
    push Not at hc
    have h2 : M ^ 2 < 0.787992 ^ 2 := pow_lt_pow_left₀ hc hMpos.le (by norm_num)
    have h3 : M ^ 2 * (4 * Real.pi) < 0.787992 ^ 2 * (4 * Real.pi) :=
      mul_lt_mul_of_pos_right h2 (by positivity)
    nlinarith
  · by_contra hc
    push Not at hc
    have h2 : (0.787995 : ℝ) ^ 2 < M ^ 2 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    have h3 : 0.787995 ^ 2 * (4 * Real.pi) < M ^ 2 * (4 * Real.pi) :=
      mul_lt_mul_of_pos_right h2 (by positivity)
    nlinarith

/-- The contrast window at the second minimum. -/
theorem win_C {ξ U : ℝ} (hU0 : 0 < U) (hξ1 : 15699 / 2 ≤ ξ) (hξ2 : ξ ≤ 31399 / 4)
    (u1 : 99378175 / 100000000 ≤ U) (u2 : U ≤ 99378323 / 100000000) :
    31193900 ≤ ξ ^ 2 / (2 * U ^ 2) ∧ ξ ^ 2 / (2 * U ^ 2) ≤ 31196100 := by
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have : (99378323 / 100000000 : ℝ) ^ 2 ≥ U ^ 2 := pow_le_pow_left₀ hU0.le u2 2
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have : (99378175 / 100000000 : ℝ) ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (by norm_num) u1 2
    nlinarith

/-- u v³ at the second minimum is below the tail bound. -/
theorem P_lt {U : ℝ} (hU0 : 0 < U) (u2 : U ≤ 99378323 / 100000000) : 8 * U ^ 4 < 7805 / 1000 := by
  have : U ^ 4 ≤ (99378323 / 100000000 : ℝ) ^ 4 := pow_le_pow_left₀ hU0.le u2 4
  nlinarith

/-- u v³ on the second-maximum bracket is above the tail bound. -/
theorem P_box {U V : ℝ} (h1 : 102 / 100 ≤ U) (h2 : 204 / 100 ≤ V) : 7805 / 1000 < U * V ^ 3 := by
  have : (204 / 100 : ℝ) ^ 3 ≤ V ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
  have h3 : (102 / 100 : ℝ) * (204 / 100) ^ 3 ≤ U * V ^ 3 :=
    mul_le_mul h1 this (by positivity) (by linarith)
  have : (7805 / 1000 : ℝ) < 102 / 100 * (204 / 100) ^ 3 := by norm_num
  linarith

set_option maxHeartbeats 8000000 in
/-- The assembly behind `Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min`. -/
theorem main (S : ℝ) (hS : 20000 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ ξ₃ ξ₄ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧ 7849.5 ≤ ξ₄ ∧ ξ₄ ≤ 7849.75 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₂ S, s ≠ ξ₃ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₃ ^ 2 * (-φ ξ₃) * Real.exp (w ξ₃ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₃ S, s ≠ ξ₄ →
        ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.787992 ≤ ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.787995 ∧
      31193900 ≤ Real.exp (-w ξ₄) ∧ Real.exp (-w ξ₄) ≤ 31196100 := by
  have hS150 : (150 : ℝ) ≤ S := by linarith
  have hS7 : (7 : ℝ) ≤ S := by linarith
  -- the first maximum, as in `bonnor_ebert_max`
  have hsub : Icc (0 : ℝ) 7 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS7
  have hw7 : ∀ s ∈ Icc (0 : ℝ) 7, HasDerivWithinAt w (φ s) (Icc 0 7) s :=
    fun s hs => (hw s (hsub hs)).mono hsub
  have hφ07 : ContinuousWithinAt φ (Icc 0 7) 0 := hφ0.mono hsub
  have hφ7 : ∀ s ∈ Ioc (0 : ℝ) 7,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 7) s :=
    fun s hs => (hφ s ⟨hs.1, hs.2.trans hS7⟩).mono hsub
  obtain ⟨e1, e2, p1, p2⟩ := Checked.Math.BEEnd.chain_end hw7 hφ07 hφ7 h0
  have T7 := Checked.Math.BETail.tail S hS7 w φ hw hφ e1 e2 p1 p2
  obtain ⟨ξ, hξ1, hξ2, hmono, hanti, hm1, hm2, -, -⟩ :=
    Checked.Math.BonnorEbert.bonnor_ebert_critical S hS7 w φ hw hφ0 hφ h0
  set M : ℝ → ℝ := fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) with hM
  set U : ℝ → ℝ := fun x => x * Real.exp (w x) / -φ x with hU
  set V : ℝ → ℝ := fun x => -(x * φ x) with hV
  have dv : ∀ x ∈ Ioo (0 : ℝ) S, HasDerivAt w (φ x) x ∧
      HasDerivAt φ (-(2 / x * φ x) - Real.exp (w x)) x :=
    fun x hx => Checked.Math.GFinal.derivs_at hw hφ hx
  have hsub7 : Icc (7 : ℝ) S ⊆ Icc 0 S := Icc_subset_Icc (by norm_num) le_rfl
  have cφ : ContinuousOn φ (Icc 7 S) := fun s hs =>
    (hφ s ⟨by linarith [hs.1], hs.2⟩).continuousWithinAt.mono hsub7
  -- φ < 0 on [7, S]
  have gA : StrictAntiOn (fun s => s ^ 2 * φ s) (Icc 7 S) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 7 S) ((continuousOn_pow 2).mul cφ)
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨-, h2⟩ := dv x ⟨by linarith [hx.1], hx.2⟩
    have hd := (hasDerivAt_pow 2 x).mul h2
    rw [hd.deriv]
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have e : ((2 : ℕ) : ℝ) * x ^ (2 - 1) * φ x + x ^ 2 * (-(2 / x * φ x) - Real.exp (w x)) =
        -(x ^ 2 * Real.exp (w x)) := by push_cast; field_simp; ring
    rw [e]
    have := Real.exp_pos (w x)
    have : 0 < x ^ 2 := by positivity
    nlinarith
  have φneg : ∀ s ∈ Icc (7 : ℝ) S, φ s < 0 := by
    intro s hs
    have h : s ^ 2 * φ s ≤ 7 ^ 2 * φ 7 := gA.antitoneOn ⟨le_rfl, hS7⟩ hs hs.1
    have h7 : (7 : ℝ) ^ 2 * φ 7 < 0 := by nlinarith
    have hs2 : 0 < s ^ 2 := by have := hs.1; positivity
    by_contra hc
    push_neg at hc
    nlinarith
  -- homology derivatives within [7, S] and at interior points
  have dW : ∀ t ∈ Icc (7 : ℝ) S,
      HasDerivWithinAt U (U t * (3 - U t - V t) / t) (Icc 0 S) t ∧
      HasDerivWithinAt V (V t * (U t - 1) / t) (Icc 0 S) t := fun t ht =>
    homology_deriv (by linarith [ht.1]) (φneg t ht) (hw t (hsub7 ht)) (hφ t ⟨by linarith [ht.1], ht.2⟩)
  have dA : ∀ t ∈ Ioo (7 : ℝ) S,
      HasDerivAt U (U t * (3 - U t - V t) / t) t ∧ HasDerivAt V (V t * (U t - 1) / t) t := fun t ht =>
    homology_deriv_at (by linarith [ht.1]) (φneg t (Ioo_subset_Icc_self ht))
      (dv t ⟨by linarith [ht.1], ht.2⟩).1 (dv t ⟨by linarith [ht.1], ht.2⟩).2
  have cU : ContinuousOn U (Icc 7 S) := fun t ht => ((dW t ht).1.continuousWithinAt).mono hsub7
  have cV : ContinuousOn V (Icc 7 S) := fun t ht => ((dW t ht).2.continuousWithinAt).mono hsub7
  have Upos : ∀ s ∈ Icc (7 : ℝ) S, 0 < U s := fun s hs => by
    have := φneg s hs; have := Real.exp_pos (w s); have : (0 : ℝ) < s := by linarith [hs.1]
    exact div_pos (by positivity) (by linarith)
  have Vpos : ∀ s ∈ Icc (7 : ℝ) S, 0 < V s := fun s hs => by
    have := φneg s hs; have : (0 : ℝ) < s := by linarith [hs.1]
    have : s * φ s < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    show 0 < -(s * φ s); linarith
  -- the certified chain on [7, 150]
  have h150 : (150 : ℝ) ≤ S := hS150
  have sub150 : Icc ((7 : ℚ) : ℝ) ((150 : ℚ) : ℝ) ⊆ Icc 0 S := by
    intro x hx; push_cast at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have u7lo : (577619974100737 / 500000000000000 - 115479 / 1000000000000000 : ℝ) ≤ U 7 := by
    show _ ≤ 7 * Real.exp (w 7) / -φ 7
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have u7hi : U 7 ≤ 577619974100737 / 500000000000000 + 115479 / 1000000000000000 := by
    show 7 * Real.exp (w 7) / -φ 7 ≤ _
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have v7 : |V 7 - 494348330833 / 200000000000| ≤ 115479 / 1000000000000000 := by
    show |-(7 * φ 7) - _| ≤ _
    rw [abs_le]; constructor <;> linarith
  obtain ⟨cdec, cbr, cinc, k150u, k150v⟩ := Checked.Math.BEHChain.chain (u := U) (v := V)
    (fun t ht => (dW t ⟨ht.1, ht.2.trans h150⟩).1.mono sub150)
    (fun t ht => (dW t ⟨ht.1, ht.2.trans h150⟩).2.mono sub150)
    (by rw [abs_le]; constructor <;> linarith) v7
  obtain ⟨x1, x2, ξ₃, a1, a2, a3, a4, a5, a6, hmax, hmin, hmax2, M3lo, -, -, -⟩ :=
    Checked.Math.BEH2Main.main S (by linarith) w φ hw hφ0 hφ h0
  -- the one-sided cells on [150, 20000]
  have h20 : (20000 : ℝ) ≤ S := hS
  have sub20 : Icc ((150 : ℚ) : ℝ) ((20000 : ℚ) : ℝ) ⊆ Icc 0 S := by
    intro x hx; push_cast at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have k150u' : |U 150 - 2105111091 / 2000000000| ≤ 1 / 5000000 := by
    have := abs_le.1 k150u; rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have k150v' : |V 150 - 2331774279 / 1250000000| ≤ 1 / 5000000 := by
    have := abs_le.1 k150v; rw [abs_le]; constructor <;> linarith [this.1, this.2]
  obtain ⟨o1, o2, o3, o4, o5, k20u, k20v⟩ := Checked.Math.BEOChain.chain (u := U) (v := V)
    (fun t ht => (dW t ⟨by linarith [ht.1], ht.2.trans h20⟩).1.mono sub20)
    (fun t ht => (dW t ⟨by linarith [ht.1], ht.2.trans h20⟩).2.mono sub20) k150u' k150v'
  -- P = U V³
  have cP : ContinuousOn (fun s => U s * V s ^ 3) (Icc 7 S) := cU.mul (cV.pow 3)
  have dP : ∀ x ∈ Ioo (7 : ℝ) S, HasDerivAt (fun s => U s * V s ^ 3)
      (U x * V x ^ 3 * (2 * U x - V x) / x) x := by
    intro x hx
    obtain ⟨d1, d2⟩ := dA x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hd : HasDerivAt (fun s => U s * V s ^ 3)
        (U x * (3 - U x - V x) / x * V x ^ 3 + U x * (↑3 * V x ^ (3 - 1) * (V x * (U x - 1) / x))) x :=
      d1.mul (d2.pow 3)
    refine hd.congr_deriv ?_
    field_simp; ring
  -- the zero ξ₄ of g = 2U − V in the bracket of the second minimum
  set A4 : ℝ := 15699 / 2 with hA4
  set B4 : ℝ := 31399 / 4 with hB4
  set B3 : ℝ := 36689 / 50 with hB3
  have hAB4 : A4 ≤ B4 := by norm_num [hA4, hB4]
  have hB3A4 : B3 ≤ A4 := by norm_num [hA4, hB3]
  have hB420 : B4 ≤ 20000 := by norm_num [hB4]
  have h7B3 : (7 : ℝ) < B3 := by norm_num [hB3]
  have subAB4 : Icc A4 B4 ⊆ Icc 7 S := Icc_subset_Icc (by linarith) (by linarith)
  have cg4 : ContinuousOn (fun s => 2 * U s - V s) (Icc A4 B4) :=
    ((continuousOn_const.mul cU).sub cV).mono subAB4
  have gA4 : 2 * U A4 - V A4 < 0 := o3 A4 ⟨hB3A4, le_rfl⟩
  have gB4 : 0 < 2 * U B4 - V B4 := o5 B4 ⟨le_rfl, hB420⟩
  obtain ⟨ξ₄, hξ₄, hg4⟩ := intermediate_value_Icc hAB4 cg4 ⟨gA4.le, gB4.le⟩
  have gmono4 : StrictMonoOn (fun s => 2 * U s - V s) (Icc A4 B4) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc A4 B4) cg4
    intro x hx
    rw [interior_Icc] at hx
    have hx7 : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨d1, d2⟩ := dA x hx7
    have hd : HasDerivAt (fun s => 2 * U s - V s)
        (2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x) x := (d1.const_mul 2).sub d2
    rw [hd.deriv]
    have hG := (o4 x ⟨hx.1.le, hx.2.le⟩).1
    have hx0 : 0 < x := by linarith [hx.1]
    have e : 2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x =
        (6 * U x - 2 * U x ^ 2 - 3 * (U x * V x) + V x) / x := by field_simp; ring
    rw [e]; positivity
  have ξ4a : A4 ≤ ξ₄ := hξ₄.1
  have ξ4b : ξ₄ ≤ B4 := hξ₄.2
  have gneg4 : ∀ s ∈ Icc B3 ξ₄, s ≠ ξ₄ → 2 * U s - V s < 0 := by
    intro s hs hne
    rcases le_or_gt s A4 with h | h
    · exact o3 s ⟨hs.1, h⟩
    · have hlt : s < ξ₄ := lt_of_le_of_ne hs.2 hne
      have := gmono4 ⟨h.le, by linarith⟩ hξ₄ hlt
      simp only at this hg4; linarith
  have gpos4 : ∀ s ∈ Icc ξ₄ 20000, s ≠ ξ₄ → 0 < 2 * U s - V s := by
    intro s hs hne
    rcases le_or_gt B4 s with h | h
    · exact o5 s ⟨h, hs.2⟩
    · have hlt : ξ₄ < s := lt_of_le_of_ne hs.1 (Ne.symm hne)
      have := gmono4 hξ₄ ⟨by linarith, h.le⟩ hlt
      simp only at this hg4; linarith
  have Panti4 : StrictAntiOn (fun s => U s * V s ^ 3) (Icc B3 ξ₄) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc B3 ξ₄) (cP.mono (Icc_subset_Icc h7B3.le (by linarith)))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := gneg4 x ⟨hx.1.le, hx.2.le⟩ hx.2.ne
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    have : 0 < U x * V x ^ 3 := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg this hg) hx0
  have Pmono4 : StrictMonoOn (fun s => U s * V s ^ 3) (Icc ξ₄ 20000) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ξ₄ 20000) (cP.mono (Icc_subset_Icc (by linarith) h20))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := gpos4 x ⟨hx.1.le, hx.2.le⟩ hx.1.ne'
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  have Pmono1 : StrictMonoOn (fun s => U s * V s ^ 3) (Icc 150 (18344 / 25)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 150 (18344 / 25))
      (cP.mono (Icc_subset_Icc (by norm_num) (by linarith)))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := o1 x ⟨hx.1.le, hx.2.le⟩
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  -- the state at ξ₄: v = 2u, u in the bracket window
  obtain ⟨-, ub1, ub2⟩ := o4 ξ₄ hξ₄
  have hVξ4 : V ξ₄ = 2 * U ξ₄ := by simp only at hg4; linarith
  have ξ4I : ξ₄ ∈ Icc (7 : ℝ) S := ⟨by linarith, by linarith⟩
  have ξ40 : 0 < ξ₄ := by linarith
  obtain ⟨Mξ4, Mξ4pos⟩ := mass_sq (w := w) ξ40 (φneg ξ₄ ξ4I)
  have hP84 : U ξ₄ * V ξ₄ ^ 3 = 8 * U ξ₄ ^ 4 := by rw [hVξ4]; ring
  have hMξ4 : M ξ₄ ^ 2 * (4 * Real.pi) = 8 * U ξ₄ ^ 4 := by
    rw [← hP84]; exact Mξ4
  obtain ⟨M4lo, M4hi⟩ := win_M hMξ4 Mξ4pos ub1 ub2
  have hUV4 : U ξ₄ * V ξ₄ = ξ₄ ^ 2 * Real.exp (w ξ₄) := by
    have hp0 : φ ξ₄ ≠ 0 := (φneg ξ₄ ξ4I).ne
    simp only [hU, hV]; field_simp
  have hu40 : (0 : ℝ) < U ξ₄ := Upos ξ₄ ξ4I
  have hcon4 : Real.exp (-w ξ₄) = ξ₄ ^ 2 / (2 * U ξ₄ ^ 2) := by
    have h2 : U ξ₄ * V ξ₄ = 2 * U ξ₄ ^ 2 := by rw [hVξ4]; ring
    rw [hUV4] at h2
    have hE : Real.exp (w ξ₄) = 2 * U ξ₄ ^ 2 / ξ₄ ^ 2 := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [Real.exp_neg, hE]; field_simp
  have hAξ4 : (15699 / 2 : ℝ) ≤ ξ₄ := ξ4a
  have hBξ4 : ξ₄ ≤ 31399 / 4 := ξ4b
  obtain ⟨C4lo, C4hi⟩ := win_C hu40 hAξ4 hBξ4 ub1 ub2
  rw [← hcon4] at C4lo C4hi
  have Pξ4lt : U ξ₄ * V ξ₄ ^ 3 < 7805 / 1000 := by rw [hP84]; exact P_lt hu40 ub2
  -- beyond 20000: Volterra's function from below
  set Vf : ℝ → ℝ := fun s => U s + V s - Real.log (U s) - 2 * Real.log (V s / 2) with hVf
  have cVf : ContinuousOn Vf (Icc 150 S) := by
    have sub : Icc (150 : ℝ) S ⊆ Icc 7 S := Icc_subset_Icc (by norm_num) le_rfl
    exact (((cU.mono sub).add (cV.mono sub)).sub ((cU.mono sub).log
      (fun s hs => (Upos s (sub hs)).ne'))).sub
      ((((cV.mono sub).div_const 2).log (fun s hs => by have := Vpos s (sub hs); positivity)).const_smul
        (2 : ℝ))
  have VfA : AntitoneOn Vf (Icc 150 S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 150 S) cVf
    · intro x hx
      rw [interior_Icc] at hx
      have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], hx.2⟩
      obtain ⟨d1, d2⟩ := dA x hxS
      have hu := Upos x (Ioo_subset_Icc_self hxS)
      have hv := Vpos x (Ioo_subset_Icc_self hxS)
      exact (((d1.add d2).sub (d1.log hu.ne')).sub
        (((d2.div_const 2).log (by positivity)).const_mul 2)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], hx.2⟩
      obtain ⟨d1, d2⟩ := dA x hxS
      have hu := Upos x (Ioo_subset_Icc_self hxS)
      have hv := Vpos x (Ioo_subset_Icc_self hxS)
      have hx0 : 0 < x := by linarith [hx.1]
      have hd : HasDerivAt Vf (U x * (3 - U x - V x) / x + V x * (U x - 1) / x -
          U x * (3 - U x - V x) / x / U x - 2 * (V x * (U x - 1) / x / 2 / (V x / 2))) x :=
        ((d1.add d2).sub (d1.log hu.ne')).sub (((d2.div_const 2).log (by positivity)).const_mul 2)
      rw [hd.deriv]
      have e : U x * (3 - U x - V x) / x + V x * (U x - 1) / x -
          U x * (3 - U x - V x) / x / U x - 2 * (V x * (U x - 1) / x / 2 / (V x / 2)) =
          -((U x - 1) ^ 2 / x) := by field_simp; ring
      rw [e]
      have : 0 ≤ (U x - 1) ^ 2 / x := by positivity
      linarith
  have I20 : (20000 : ℝ) ∈ Icc 150 S := ⟨by norm_num, h20⟩
  have P20 : ∀ s ∈ Icc (20000 : ℝ) S, 7805 / 1000 < U s * V s ^ 3 := by
    intro s hs
    have hVs := VfA I20 ⟨by linarith [hs.1], hs.2⟩ hs.1
    have k1 := abs_le.1 k20u
    have k2 := abs_le.1 k20v
    have hsI : s ∈ Icc (7 : ℝ) S := ⟨by linarith [hs.1], hs.2⟩
    exact Checked.Math.BEOTail.uv_lower2 (Upos s hsI) (Vpos s hsI) (by linarith [k1.1]) (by linarith [k1.2])
      (by linarith [k2.1]) (by linarith [k2.2]) hVs
  -- from ξ₃ to the end of the second-maximum bracket
  have ξ3I : ξ₃ ∈ Icc (7 : ℝ) S := ⟨by norm_num at a5 ⊢; linarith, by norm_num at a6 ⊢; linarith⟩
  have ξ30 : 0 < ξ₃ := by linarith [ξ3I.1]
  have Pξ3gt : 865 / 100 < U ξ₃ * V ξ₃ ^ 3 :=
    Checked.Math.BEH2Main.P_gt (mass_sq (w := w) ξ30 (φneg ξ₃ ξ3I)).1 M3lo
  have hmin2 : ∀ s ∈ Icc ξ₃ S, s ≠ ξ₄ →
      M ξ₄ < M s := by
    intro s hs hne
    have sI : s ∈ Icc (7 : ℝ) S := ⟨by linarith [hs.1, ξ3I.1], hs.2⟩
    have hs0 : 0 < s := by linarith [sI.1]
    have h735 : (1467 / 2 : ℝ) ≤ ξ₃ := by norm_num at a5 ⊢; linarith
    apply mass_lt ξ40 (φneg ξ₄ ξ4I) hs0 (φneg s sI)
    show U ξ₄ * V ξ₄ ^ 3 < U s * V s ^ 3
    rcases le_or_gt s (18344 / 25) with h1 | h1
    · have hξ3s : U ξ₃ * V ξ₃ ^ 3 ≤ U s * V s ^ 3 :=
        Pmono1.monotoneOn ⟨by linarith, by linarith [hs.1]⟩ ⟨by linarith [hs.1], h1⟩ hs.1
      linarith
    rcases le_or_gt s B3 with h2 | h2
    · obtain ⟨-, b1, b2⟩ := o2 s ⟨h1.le, h2⟩
      linarith [P_box b1 b2]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Panti4 ⟨h2.le, hlt.le⟩ ⟨by linarith, le_rfl⟩ hlt
    · rcases le_or_gt s 20000 with h3 | h3
      · exact Pmono4 ⟨le_rfl, by linarith⟩ ⟨hgt.le, h3⟩ hgt
      · exact lt_trans Pξ4lt (P20 s ⟨h3.le, hs.2⟩)
  refine ⟨x1, x2, ξ₃, ξ₄, a1, a2, a3, a4, a5, a6, by norm_num at hAξ4 ⊢; linarith,
    by norm_num at hBξ4 ⊢; linarith, hmax, hmin, hmax2, hmin2, M4lo, M4hi, C4lo, C4hi⟩

end Checked.Math.BEOMain
