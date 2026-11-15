import Checked.Math.BE3Chain
import Checked.Math.BEHMain
import Checked.Math.BEOChain

/-! Bonnor–Ebert sphere, `BEState300`: what the certified chains of `BE3Main` say at the end radius of the one-sided cells, exported for `BonnorEbertExtrema`: φ < 0 beyond the decrease range of the first maximum, the homology state (u, v) at the end radius in a small box about a rational point, and 2u − v < 0 from the third-maximum bracket to the end radius. Promoted from `Work/Math/BEState300.lean`. -/

namespace Checked.Math.BEState300
open Set Checked.Math.BEHMain

theorem state300 (S : ℝ) (hS : 300000 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    (∀ s ∈ Icc (7 : ℝ) S, φ s < 0) ∧
    |300000 * Real.exp (w 300000) / -φ 300000 - 998005545 / 1000000000| ≤ 4 / 10000000 ∧
    |-(300000 * φ 300000) - 2002054156 / 1000000000| ≤ 4 / 10000000 ∧
    (∀ t ∈ Icc (84516 : ℝ) 300000, 2 * (t * Real.exp (w t) / -φ t) - -(t * φ t) < 0) := by
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
  have h30 : (300000 : ℝ) ≤ S := hS
  have sub30 : Icc ((20000 : ℚ) : ℝ) ((300000 : ℚ) : ℝ) ⊆ Icc 0 S := by
    intro x hx; push_cast at hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨q1, q2, q3, k3u, k3v⟩ := Checked.Math.BE3Chain.chain (u := U) (v := V)
    (fun t ht => (dW t ⟨by linarith [ht.1], ht.2.trans h30⟩).1.mono sub30)
    (fun t ht => (dW t ⟨by linarith [ht.1], ht.2.trans h30⟩).2.mono sub30) k20u k20v
  exact ⟨φneg, k3u, k3v, q3⟩

end Checked.Math.BEState300
