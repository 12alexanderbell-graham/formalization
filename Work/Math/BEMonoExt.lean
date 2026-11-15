import Mathlib.Order.Monotone.Union
import Checked.Math.BE3Ext

/-! Bonnor–Ebert sphere, `BEMonoExt`: the assembly of `Checked.Math.BE3Ext.main_ext` repeated with five more outputs: the mass is strictly monotone on [0, ξ₁] and between consecutive certified extrema up to ξ₅ (the sign of 2u − v from the certified chains between the brackets, a zero of 2u − v in each bracket identified with the extremum by strictness). For `Work.Math.BEMonoMain`. -/

namespace Work.Math.BEMonoExt
open Set Checked.Math.BEHMain Checked.Math.BE3Main

/-- Strict monotonicity of u v³ gives strict monotonicity of the mass where φ < 0. -/
theorem tmono {w φ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hn : ∀ s ∈ Icc a b, φ s < 0)
    (h : StrictMonoOn (fun s => s * Real.exp (w s) / -φ s * (-(s * φ s)) ^ 3) (Icc a b)) :
    StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc a b) :=
  fun x hx y hy hxy =>
    mass_lt (lt_of_lt_of_le ha hx.1) (hn x hx) (lt_of_lt_of_le ha hy.1) (hn y hy) (h hx hy hxy)

theorem tanti {w φ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hn : ∀ s ∈ Icc a b, φ s < 0)
    (h : StrictAntiOn (fun s => s * Real.exp (w s) / -φ s * (-(s * φ s)) ^ 3) (Icc a b)) :
    StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc a b) :=
  fun x hx y hy hxy =>
    mass_lt (lt_of_lt_of_le ha hy.1) (hn y hy) (lt_of_lt_of_le ha hx.1) (hn x hx) (h hx hy hxy)

set_option maxHeartbeats 16000000 in
/-- `Checked.Math.BE3Ext.main_ext` (copied) with the monotone segments of the mass up to the third maximum. -/
theorem main_mono (S : ℝ) (hS : 300000 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      733.5 ≤ ξ₃ ∧ ξ₃ ≤ 734 ∧ 7849.5 ≤ ξ₄ ∧ ξ₄ ≤ 7849.75 ∧ 84497 ≤ ξ₅ ∧ ξ₅ ≤ 84516 ∧
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
      (∀ s ∈ Icc ξ₄ S, s ≠ ξ₅ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₅ ^ 2 * (-φ ξ₅) * Real.exp (w ξ₅ / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.80091 ≤ ξ₅ ^ 2 * (-φ ξ₅) * Real.exp (w ξ₅ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₅ ^ 2 * (-φ ξ₅) * Real.exp (w ξ₅ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.800916 ∧
      3556300000 ≤ Real.exp (-w ξ₅) ∧ Real.exp (-w ξ₅) ≤ 3558000000 ∧
      ξ₄ ^ 2 * (-φ ξ₄) * Real.exp (w ξ₄ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.787995 ∧
      StrictAntiOn (fun s => s * Real.exp (w s) / -φ s * (-(s * φ s)) ^ 3) (Icc ξ₅ 300000) ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc 0 ξ₁) ∧
      StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc ξ₁ ξ₂) ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc ξ₂ ξ₃) ∧
      StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc ξ₃ ξ₄) ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc ξ₄ ξ₅) := by
  -- the first four extrema
  obtain ⟨x1, x2, x3, ξ₄, a1, a2, a3, a4, a5, a6, a7, a8, hmax, hmin, hmax2, hmin2, -, m4hi, -, -⟩ :=
    Checked.Math.BEOMain.main S (by linarith) w φ hw hφ0 hφ h0
  have hS20 : (20000 : ℝ) ≤ S := by linarith
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
  -- the one-sided cells on [150, 20000]
  have h20 : (20000 : ℝ) ≤ S := hS20
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
  -- the zero ζ of g = 2U − V in the bracket of the second minimum (it is ξ₄ by uniqueness)
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
  obtain ⟨ζ, hζ, hgζ⟩ := intermediate_value_Icc hAB4 cg4 ⟨gA4.le, gB4.le⟩
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
  have ζa : A4 ≤ ζ := hζ.1
  have ζb : ζ ≤ B4 := hζ.2
  have gneg4 : ∀ s ∈ Icc B3 ζ, s ≠ ζ → 2 * U s - V s < 0 := by
    intro s hs hne
    rcases le_or_gt s A4 with h | h
    · exact o3 s ⟨hs.1, h⟩
    · have hlt : s < ζ := lt_of_le_of_ne hs.2 hne
      have := gmono4 ⟨h.le, by linarith⟩ hζ hlt
      simp only at this hgζ; linarith
  have gpos4 : ∀ s ∈ Icc ζ 20000, s ≠ ζ → 0 < 2 * U s - V s := by
    intro s hs hne
    rcases le_or_gt B4 s with h | h
    · exact o5 s ⟨h, hs.2⟩
    · have hlt : ζ < s := lt_of_le_of_ne hs.1 (Ne.symm hne)
      have := gmono4 hζ ⟨by linarith, h.le⟩ hlt
      simp only at this hgζ; linarith
  have Panti4 : StrictAntiOn (fun s => U s * V s ^ 3) (Icc B3 ζ) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc B3 ζ) (cP.mono (Icc_subset_Icc h7B3.le (by linarith)))
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
  have Pmono4 : StrictMonoOn (fun s => U s * V s ^ 3) (Icc ζ 20000) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ζ 20000) (cP.mono (Icc_subset_Icc (by linarith) h20))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := gpos4 x ⟨hx.1.le, hx.2.le⟩ hx.1.ne'
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  -- the one-sided cells on [20000, 300000]
  have h30 : (300000 : ℝ) ≤ S := hS
  have sub30 : Icc ((20000 : ℚ) : ℝ) ((300000 : ℚ) : ℝ) ⊆ Icc 0 S := by
    intro x hx; push_cast at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨q1, q2, q3, k3u, k3v⟩ := Checked.Math.BE3Chain.chain (u := U) (v := V)
    (fun t ht => (dW t ⟨by linarith [ht.1], ht.2.trans h30⟩).1.mono sub30)
    (fun t ht => (dW t ⟨by linarith [ht.1], ht.2.trans h30⟩).2.mono sub30) k20u k20v
  -- ζ is ξ₄: both are strict minimisers of the mass from the second-maximum bracket on
  have ζI : ζ ∈ Icc (7 : ℝ) S := ⟨by linarith, by linarith⟩
  have ζ0 : 0 < ζ := by linarith
  have ξ4I : ξ₄ ∈ Icc (7 : ℝ) S := ⟨by norm_num at a7 ⊢; linarith, by norm_num at a8 ⊢; linarith⟩
  have ξ40 : 0 < ξ₄ := by linarith [ξ4I.1]
  have hx3 : x3 ≤ 734 := by norm_num at a6 ⊢; linarith
  have h4a : (15699 / 2 : ℝ) ≤ ξ₄ := by norm_num at a7 ⊢; linarith
  have h4b : ξ₄ ≤ 31399 / 4 := by norm_num at a8 ⊢; linarith
  have hζ1 : (15699 / 2 : ℝ) ≤ ζ := hζ.1
  have hζ2 : ζ ≤ 31399 / 4 := hζ.2
  have hB3n : B3 ≤ ξ₄ := by rw [hB3]; linarith
  have hid : ξ₄ = ζ := by
    by_contra hne
    have h1 := hmin2 ζ ⟨by linarith, by linarith⟩ (Ne.symm hne)
    have hP : U ζ * V ζ ^ 3 < U ξ₄ * V ξ₄ ^ 3 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact Panti4 ⟨hB3n, h.le⟩ ⟨hB3n.trans h.le, le_rfl⟩ h
      · exact Pmono4 ⟨le_rfl, by linarith⟩ ⟨h.le, by linarith⟩ h
    have h2 := mass_lt ζ0 (φneg ζ ζI) ξ40 (φneg ξ₄ ξ4I) hP
    exact lt_asymm h1 h2
  -- the zero ξ₅ of g = 2U − V in the bracket of the third maximum
  set A5 : ℝ := 84497 with hA5
  set B5 : ℝ := 84516 with hB5
  have hAB5 : A5 ≤ B5 := by norm_num [hA5, hB5]
  have subAB5 : Icc A5 B5 ⊆ Icc 7 S := Icc_subset_Icc (by norm_num [hA5]) (by linarith [hB5])
  have cg5 : ContinuousOn (fun s => 2 * U s - V s) (Icc A5 B5) :=
    ((continuousOn_const.mul cU).sub cV).mono subAB5
  have gA5 : 0 < 2 * U A5 - V A5 := q1 A5 ⟨by norm_num [hA5], le_rfl⟩
  have gB5 : 2 * U B5 - V B5 < 0 := q3 B5 ⟨le_rfl, by norm_num [hB5]⟩
  obtain ⟨ξ₅, hξ₅, hg5⟩ := intermediate_value_Icc' hAB5 cg5 ⟨gB5.le, gA5.le⟩
  have ganti5 : StrictAntiOn (fun s => 2 * U s - V s) (Icc A5 B5) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc A5 B5) cg5
    intro x hx
    rw [interior_Icc] at hx
    have hx7 : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1, hA5], by linarith [hx.2, hB5]⟩
    obtain ⟨d1, d2⟩ := dA x hx7
    have hd : HasDerivAt (fun s => 2 * U s - V s)
        (2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x) x := (d1.const_mul 2).sub d2
    rw [hd.deriv]
    have hG := (q2 x ⟨hx.1.le, hx.2.le⟩).1
    have hx0 : 0 < x := by linarith [hx.1, hA5]
    have e : 2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x =
        (6 * U x - 2 * U x ^ 2 - 3 * (U x * V x) + V x) / x := by field_simp; ring
    rw [e]; exact div_neg_of_neg_of_pos hG hx0
  have ξ5a : A5 ≤ ξ₅ := hξ₅.1
  have ξ5b : ξ₅ ≤ B5 := hξ₅.2
  have h5a : (84497 : ℝ) ≤ ξ₅ := hξ₅.1
  have h5b : ξ₅ ≤ 84516 := hξ₅.2
  have gpos5 : ∀ s ∈ Icc ζ ξ₅, s ≠ ζ → s ≠ ξ₅ → 0 < 2 * U s - V s := by
    intro s hs hne hne5
    rcases le_or_gt s 20000 with h | h
    · exact gpos4 s ⟨hs.1, h⟩ hne
    rcases le_or_gt s A5 with h' | h'
    · exact q1 s ⟨h.le, h'⟩
    · have hlt : s < ξ₅ := lt_of_le_of_ne hs.2 hne5
      have := ganti5 ⟨h'.le, by linarith⟩ hξ₅ hlt
      simp only at this hg5; linarith
  have gneg5 : ∀ s ∈ Icc ξ₅ 300000, s ≠ ξ₅ → 2 * U s - V s < 0 := by
    intro s hs hne
    rcases le_or_gt B5 s with h | h
    · exact q3 s ⟨h, hs.2⟩
    · have hlt : ξ₅ < s := lt_of_le_of_ne hs.1 (Ne.symm hne)
      have := ganti5 hξ₅ ⟨by linarith, h.le⟩ hlt
      simp only at this hg5; linarith
  have Pmono5 : StrictMonoOn (fun s => U s * V s ^ 3) (Icc ζ ξ₅) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ζ ξ₅)
      (cP.mono (Icc_subset_Icc (by linarith) (by linarith [hB5])))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2, hB5]⟩
    rw [(dP x hxS).deriv]
    have hg := gpos5 x ⟨hx.1.le, hx.2.le⟩ hx.1.ne' hx.2.ne
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  have Panti5 : StrictAntiOn (fun s => U s * V s ^ 3) (Icc ξ₅ 300000) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc ξ₅ 300000)
      (cP.mono (Icc_subset_Icc (by linarith [hA5]) h30))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1, hA5], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := gneg5 x ⟨hx.1.le, hx.2.le⟩ hx.1.ne'
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1, hA5]
    have : 0 < U x * V x ^ 3 := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg this hg) hx0
  -- the state at ξ₅: v = 2u, u in the bracket window
  obtain ⟨-, ub1, ub2⟩ := q2 ξ₅ hξ₅
  have hVξ5 : V ξ₅ = 2 * U ξ₅ := by simp only at hg5; linarith
  have ξ5I : ξ₅ ∈ Icc (7 : ℝ) S := ⟨by linarith [hA5], by linarith [hB5]⟩
  have ξ50 : 0 < ξ₅ := by linarith [ξ5I.1]
  obtain ⟨Mξ5, Mξ5pos⟩ := mass_sq (w := w) ξ50 (φneg ξ₅ ξ5I)
  have hP85 : U ξ₅ * V ξ₅ ^ 3 = 8 * U ξ₅ ^ 4 := by rw [hVξ5]; ring
  have hMξ5 : M ξ₅ ^ 2 * (4 * Real.pi) = 8 * U ξ₅ ^ 4 := by
    rw [← hP85]; exact Mξ5
  obtain ⟨M5lo, M5hi⟩ := win_M hMξ5 Mξ5pos ub1 ub2
  have hUV5 : U ξ₅ * V ξ₅ = ξ₅ ^ 2 * Real.exp (w ξ₅) := by
    have hp0 : φ ξ₅ ≠ 0 := (φneg ξ₅ ξ5I).ne
    simp only [hU, hV]; field_simp
  have hu50 : (0 : ℝ) < U ξ₅ := Upos ξ₅ ξ5I
  have hcon5 : Real.exp (-w ξ₅) = ξ₅ ^ 2 / (2 * U ξ₅ ^ 2) := by
    have h2 : U ξ₅ * V ξ₅ = 2 * U ξ₅ ^ 2 := by rw [hVξ5]; ring
    rw [hUV5] at h2
    have hE : Real.exp (w ξ₅) = 2 * U ξ₅ ^ 2 / ξ₅ ^ 2 := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [Real.exp_neg, hE]; field_simp
  obtain ⟨C5lo, C5hi⟩ := win_C hu50 h5a h5b ub1 ub2
  rw [← hcon5] at C5lo C5hi
  have Pξ5gt : 805 / 100 < U ξ₅ * V ξ₅ ^ 3 := by rw [hP85]; exact P_gt ub1

  -- beyond 300000: Volterra's function from above
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
  have I30 : (300000 : ℝ) ∈ Icc 150 S := ⟨by norm_num, h30⟩
  have P30 : ∀ s ∈ Icc (300000 : ℝ) S, U s * V s ^ 3 < 805 / 100 := by
    intro s hs
    have hVs := VfA I30 ⟨by linarith [hs.1], hs.2⟩ hs.1
    have k1 := abs_le.1 k3u
    have k2 := abs_le.1 k3v
    have hsI : s ∈ Icc (7 : ℝ) S := ⟨by linarith [hs.1], hs.2⟩
    exact Checked.Math.BE3Tail.uv_upper3 (Upos s hsI) (Vpos s hsI) (by linarith [k1.1]) (by linarith [k1.2])
      (by linarith [k2.1]) (by linarith [k2.2]) hVs
  have hmax3 : ∀ s ∈ Icc ξ₄ S, s ≠ ξ₅ → M s < M ξ₅ := by
    intro s hs hne
    rw [hid] at hs
    have sI : s ∈ Icc (7 : ℝ) S := ⟨by linarith [hs.1], hs.2⟩
    have hs0 : 0 < s := by linarith [sI.1]
    apply mass_lt hs0 (φneg s sI) ξ50 (φneg ξ₅ ξ5I)
    show U s * V s ^ 3 < U ξ₅ * V ξ₅ ^ 3
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Pmono5 ⟨hs.1, hlt.le⟩ ⟨by linarith [hs.1], le_rfl⟩ hlt
    · rcases le_or_gt s 300000 with h3 | h3
      · exact Panti5 ⟨le_rfl, by linarith⟩ ⟨hgt.le, h3⟩ hgt
      · exact lt_trans (P30 s ⟨h3.le, hs.2⟩) Pξ5gt
  -- monotone segments: P = u v³ strictly monotone where 2u − v has a sign
  have Pmon : ∀ a b : ℝ, 7 ≤ a → b ≤ S → (∀ x ∈ Ioo a b, 0 < 2 * U x - V x) →
      StrictMonoOn (fun s => U s * V s ^ 3) (Icc a b) := by
    intro a b ha hb hg
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) (cP.mono (Icc_subset_Icc ha hb))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := hg x hx
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  have Pant : ∀ a b : ℝ, 7 ≤ a → b ≤ S → (∀ x ∈ Ioo a b, 2 * U x - V x < 0) →
      StrictAntiOn (fun s => U s * V s ^ 3) (Icc a b) := by
    intro a b ha hb hg
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) (cP.mono (Icc_subset_Icc ha hb))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := hg x hx
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    have : 0 < U x * V x ^ 3 := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg this hg) hx0
  -- the zero ζ₂ of g = 2U − V in the bracket of the first minimum
  have hA2B2 : (418797 / 6250 : ℝ) ≤ 3350379 / 50000 := by norm_num
  have subAB2 : Icc (418797 / 6250 : ℝ) (3350379 / 50000) ⊆ Icc 7 S :=
    Icc_subset_Icc (by norm_num) (by linarith)
  have cg2 : ContinuousOn (fun s => 2 * U s - V s) (Icc (418797 / 6250 : ℝ) (3350379 / 50000)) :=
    ((continuousOn_const.mul cU).sub cV).mono subAB2
  have gA2 : 2 * U (418797 / 6250) - V (418797 / 6250) < 0 := cdec _ ⟨by norm_num, le_rfl⟩
  have gB2 : 0 < 2 * U (3350379 / 50000) - V (3350379 / 50000) := cinc _ ⟨le_rfl, by norm_num⟩
  obtain ⟨ζ₂, hζ₂, hg2⟩ := intermediate_value_Icc hA2B2 cg2 ⟨gA2.le, gB2.le⟩
  have gmono2 : StrictMonoOn (fun s => 2 * U s - V s) (Icc (418797 / 6250 : ℝ) (3350379 / 50000)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) cg2
    intro x hx
    rw [interior_Icc] at hx
    have hx7 : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨d1, d2⟩ := dA x hx7
    have hd : HasDerivAt (fun s => 2 * U s - V s)
        (2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x) x := (d1.const_mul 2).sub d2
    rw [hd.deriv]
    have hG := (cbr x ⟨hx.1.le, hx.2.le⟩).1
    have hx0 : 0 < x := by linarith [hx.1]
    have e : 2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x =
        (6 * U x - 2 * U x ^ 2 - 3 * (U x * V x) + V x) / x := by field_simp; ring
    rw [e]; positivity
  have ζ₂a : (418797 / 6250 : ℝ) ≤ ζ₂ := hζ₂.1
  have ζ₂b : ζ₂ ≤ 3350379 / 50000 := hζ₂.2
  have gneg2 : ∀ x ∈ Ioo (7 : ℝ) ζ₂, 2 * U x - V x < 0 := by
    intro s hs
    rcases le_or_gt s (418797 / 6250) with h | h
    · exact cdec s ⟨hs.1.le, h⟩
    · have := gmono2 ⟨h.le, by linarith [hs.2]⟩ hζ₂ hs.2
      simp only at this hg2; linarith
  have gpos2 : ∀ s ∈ Icc ζ₂ 150, s ≠ ζ₂ → 0 < 2 * U s - V s := by
    intro s hs hne
    rcases le_or_gt (3350379 / 50000) s with h | h
    · exact cinc s ⟨h, hs.2⟩
    · have hlt : ζ₂ < s := lt_of_le_of_ne hs.1 (Ne.symm hne)
      have := gmono2 hζ₂ ⟨by linarith, h.le⟩ hlt
      simp only at this hg2; linarith
  -- the zero ζ₃ of g in the bracket of the second maximum
  have hA3B3 : (18344 / 25 : ℝ) ≤ B3 := by norm_num [hB3]
  have subAB3 : Icc (18344 / 25 : ℝ) B3 ⊆ Icc 7 S :=
    Icc_subset_Icc (by norm_num) (by linarith)
  have cg3 : ContinuousOn (fun s => 2 * U s - V s) (Icc (18344 / 25 : ℝ) B3) :=
    ((continuousOn_const.mul cU).sub cV).mono subAB3
  have gA3 : 0 < 2 * U (18344 / 25) - V (18344 / 25) := o1 _ ⟨by norm_num, le_rfl⟩
  have gB3 : 2 * U B3 - V B3 < 0 := o3 B3 ⟨le_rfl, hB3A4⟩
  obtain ⟨ζ₃, hζ₃, hg3⟩ := intermediate_value_Icc' hA3B3 cg3 ⟨gB3.le, gA3.le⟩
  have ganti3 : StrictAntiOn (fun s => 2 * U s - V s) (Icc (18344 / 25 : ℝ) B3) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) cg3
    intro x hx
    rw [interior_Icc] at hx
    have hx7 : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨d1, d2⟩ := dA x hx7
    have hd : HasDerivAt (fun s => 2 * U s - V s)
        (2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x) x := (d1.const_mul 2).sub d2
    rw [hd.deriv]
    have hG := (o2 x ⟨hx.1.le, hx.2.le⟩).1
    have hx0 : 0 < x := by linarith [hx.1]
    have e : 2 * (U x * (3 - U x - V x) / x) - V x * (U x - 1) / x =
        (6 * U x - 2 * U x ^ 2 - 3 * (U x * V x) + V x) / x := by field_simp; ring
    rw [e]; exact div_neg_of_neg_of_pos hG hx0
  have ζ₃a : (18344 / 25 : ℝ) ≤ ζ₃ := hζ₃.1
  have ζ₃b : ζ₃ ≤ B3 := hζ₃.2
  have hB3v : B3 = 36689 / 50 := hB3
  have gpos23 : ∀ x ∈ Ioo ζ₂ ζ₃, 0 < 2 * U x - V x := by
    intro s hs
    rcases le_or_gt s 150 with h | h
    · exact gpos2 s ⟨hs.1.le, h⟩ hs.1.ne'
    rcases le_or_gt s (18344 / 25) with h' | h'
    · exact o1 s ⟨h.le, h'⟩
    · have := ganti3 ⟨h'.le, by linarith [hs.2]⟩ hζ₃ hs.2
      simp only at this hg3; linarith
  have gneg34 : ∀ x ∈ Ioo ζ₃ ζ, 2 * U x - V x < 0 := by
    intro s hs
    rcases le_or_gt B3 s with h | h
    · exact gneg4 s ⟨h, hs.2.le⟩ hs.2.ne
    · have := ganti3 hζ₃ ⟨by linarith [hs.1], h.le⟩ hs.1
      simp only at this hg3; linarith
  have Panti2 : StrictAntiOn (fun s => U s * V s ^ 3) (Icc 7 ζ₂) :=
    Pant 7 ζ₂ le_rfl (by linarith) gneg2
  have Pmono23 : StrictMonoOn (fun s => U s * V s ^ 3) (Icc ζ₂ ζ₃) :=
    Pmon ζ₂ ζ₃ (by linarith) (by linarith) gpos23
  have Panti34 : StrictAntiOn (fun s => U s * V s ^ 3) (Icc ζ₃ ζ) :=
    Pant ζ₃ ζ (by linarith) (by linarith) gneg34
  -- identification of the extrema with the zeros
  have b2l : (7 : ℝ) ≤ x2 := by norm_num at a3 ⊢; linarith
  have b2h : x2 ≤ 150 := by norm_num at a4 ⊢; linarith
  have b3l : (150 : ℝ) ≤ x3 := by norm_num at a5 ⊢; linarith
  have b3h : x3 ≤ 734 := by norm_num at a6 ⊢; linarith
  have b1h : x1 ≤ 7 := by norm_num at a2 ⊢; linarith
  have b1l : 0 ≤ x1 := by norm_num at a1 ⊢; linarith
  have hid2 : x2 = ζ₂ := by
    by_contra hne
    have h1 := hmin ζ₂ ⟨by linarith, by linarith⟩ (Ne.symm hne)
    have hP : U ζ₂ * V ζ₂ ^ 3 < U x2 * V x2 ^ 3 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact Panti2 ⟨b2l, h.le⟩ ⟨by linarith, le_rfl⟩ h
      · exact Pmono23 ⟨le_rfl, by linarith⟩ ⟨h.le, by linarith⟩ h
    have h2 := mass_lt (by linarith) (φneg ζ₂ ⟨by linarith, by linarith⟩) (by linarith)
      (φneg x2 ⟨b2l, by linarith⟩) hP
    exact lt_asymm h1 h2
  have hid3 : x3 = ζ₃ := by
    by_contra hne
    have h1 := hmax2 ζ₃ ⟨by linarith, by linarith⟩ (Ne.symm hne)
    have hP : U x3 * V x3 ^ 3 < U ζ₃ * V ζ₃ ^ 3 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact Pmono23 ⟨by linarith, h.le⟩ ⟨by linarith, le_rfl⟩ h
      · exact Panti34 ⟨le_rfl, by linarith⟩ ⟨h.le, by linarith⟩ h
    have h2 := mass_lt (by linarith) (φneg x3 ⟨by linarith, by linarith⟩) (by linarith)
      (φneg ζ₃ ⟨by linarith, by linarith⟩) hP
    exact lt_asymm h1 h2
  have hξc1 : 6.4507514 ≤ ξ := hξ1
  have hξc2 : ξ ≤ 6.4507515 := hξ2
  have hc0 : 0 ≤ ξ := by norm_num at hξc1 ⊢; linarith
  have hc7 : ξ ≤ 7 := by norm_num at hξc2 ⊢; linarith
  have hidc : ξ = x1 := by
    by_contra hne
    have h1 := hmax ξ ⟨hc0, by linarith⟩ hne
    have h2 : M x1 < M ξ := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact hanti ⟨le_rfl, hc7⟩ ⟨h.le, b1h⟩ h
      · exact hmono ⟨b1l, h.le⟩ ⟨hc0, le_rfl⟩ h
    exact lt_asymm h1 h2
  have Mm1 : StrictMonoOn M (Icc 0 x1) := by rw [← hidc]; exact hmono
  have Ma12 : StrictAntiOn M (Icc x1 x2) := by
    have A1 : StrictAntiOn M (Icc x1 7) := by rw [← hidc]; exact hanti
    have A2 : StrictAntiOn M (Icc 7 x2) := by
      rw [hid2]
      exact tanti (by norm_num) (fun s hs => φneg s ⟨hs.1, by linarith [hs.2]⟩) Panti2
    rw [← Icc_union_Icc_eq_Icc b1h b2l]
    exact StrictAntiOn.union A1 A2 (isGreatest_Icc b1h) (isLeast_Icc b2l)
  have Mm23 : StrictMonoOn M (Icc x2 x3) := by
    rw [hid2, hid3]
    exact tmono (by linarith) (fun s hs => φneg s ⟨by linarith [hs.1], by linarith [hs.2]⟩) Pmono23
  have Ma34 : StrictAntiOn M (Icc x3 ξ₄) := by
    rw [hid3, hid]
    exact tanti (by linarith) (fun s hs => φneg s ⟨by linarith [hs.1], by linarith [hs.2]⟩) Panti34
  have Mm45 : StrictMonoOn M (Icc ξ₄ ξ₅) := by
    rw [hid]
    exact tmono (by linarith) (fun s hs => φneg s ⟨by linarith [hs.1], by linarith [hs.2, hB5]⟩) Pmono5
  refine ⟨x1, x2, x3, ξ₄, ξ₅, a1, a2, a3, a4, a5, a6, a7, a8, h5a, h5b, hmax, hmin, hmax2, hmin2, hmax3, M5lo, M5hi, C5lo, C5hi, m4hi, Panti5,
    Mm1, Ma12, Mm23, Ma34, Mm45⟩

end Work.Math.BEMonoExt
