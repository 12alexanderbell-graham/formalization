import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Checked.Math.GFinal
import Checked.Math.BEEnd
import Checked.Math.BETail
import Checked.Math.BonnorEbert
import Work.Math.BEHChain
import Work.Math.BEHTail

/-! Bonnor–Ebert sphere, `BEHMain`: from a regular solution (w, φ) of the isothermal equation on [0, S],
S ≥ 150, to its homology variables u = s e^w / (−φ), v = −s φ on [7, S]; the certified cells of `BEHChain`
on [7, 150], the zero ξ₂ of 2u − v in the bracket cell (the first minimum of the mass), the monotonicity of
u v³ = 4π m² on either side, and Volterra's function beyond 150 (`BEHTail`). Written by run
2026-11-14T0428Z. -/

namespace Work.Math.BEHMain
open Set

/-- The homology variables solve the homology system wherever (w, φ) solve the isothermal equation and
φ ≠ 0 (derivatives within any set). -/
theorem homology_deriv {w φ : ℝ → ℝ} {s : Set ℝ} {t : ℝ} (ht : 0 < t) (hp : φ t < 0)
    (hw : HasDerivWithinAt w (φ t) s t)
    (hφ : HasDerivWithinAt φ (-(2 / t * φ t) - Real.exp (w t)) s t) :
    HasDerivWithinAt (fun x => x * Real.exp (w x) / -φ x)
      ((t * Real.exp (w t) / -φ t) * (3 - t * Real.exp (w t) / -φ t - -(t * φ t)) / t) s t ∧
    HasDerivWithinAt (fun x => -(x * φ x))
      (-(t * φ t) * (t * Real.exp (w t) / -φ t - 1) / t) s t := by
  have hp0 : φ t ≠ 0 := hp.ne
  have hE := hw.exp
  constructor
  · have hu := ((hasDerivWithinAt_id t s).mul hE).div hφ.neg (by simp only [Pi.neg_apply]; linarith)
    refine hu.congr_deriv ?_
    simp only [id, Pi.neg_apply, Pi.mul_apply, Pi.div_apply, id_eq]
    field_simp
    ring
  · have hv := ((hasDerivWithinAt_id t s).mul hφ).neg
    refine hv.congr_deriv ?_
    simp only [id, Pi.neg_apply, Pi.mul_apply, Pi.div_apply, id_eq]
    field_simp
    ring

/-- Homology derivatives at an interior radius, as two-sided derivatives. -/
theorem homology_deriv_at {w φ : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hp : φ t < 0)
    (hw : HasDerivAt w (φ t) t) (hφ : HasDerivAt φ (-(2 / t * φ t) - Real.exp (w t)) t) :
    HasDerivAt (fun x => x * Real.exp (w x) / -φ x)
      ((t * Real.exp (w t) / -φ t) * (3 - t * Real.exp (w t) / -φ t - -(t * φ t)) / t) t ∧
    HasDerivAt (fun x => -(x * φ x)) (-(t * φ t) * (t * Real.exp (w t) / -φ t - 1) / t) t := by
  obtain ⟨a, b⟩ := homology_deriv (s := univ) ht hp hw.hasDerivWithinAt hφ.hasDerivWithinAt
  exact ⟨hasDerivWithinAt_univ.mp a, hasDerivWithinAt_univ.mp b⟩

/-- The mass in terms of the homology variables: m² · 4π = u v³, m > 0. -/
theorem mass_sq {w φ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hp : φ s < 0) :
    (s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ^ 2 * (4 * Real.pi) =
      s * Real.exp (w s) / -φ s * (-(s * φ s)) ^ 3 ∧
    0 < s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) := by
  have hpi : 0 < 4 * Real.pi := by positivity
  have hsq : Real.sqrt (4 * Real.pi) ^ 2 = 4 * Real.pi := Real.sq_sqrt hpi.le
  have hsq0 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.mpr hpi
  have he2 : Real.exp (w s / 2) ^ 2 = Real.exp (w s) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hp0 : φ s ≠ 0 := hp.ne
  constructor
  · rw [div_pow, mul_pow, mul_pow, he2, hsq]
    field_simp
  · have : 0 < -φ s := by linarith
    positivity

/-- Strictly smaller u v³ means strictly smaller mass (both radii with φ < 0). -/
theorem mass_lt {w φ : ℝ → ℝ} {s t : ℝ} (hs : 0 < s) (hp : φ s < 0) (ht : 0 < t) (hq : φ t < 0)
    (h : s * Real.exp (w s) / -φ s * (-(s * φ s)) ^ 3 < t * Real.exp (w t) / -φ t * (-(t * φ t)) ^ 3) :
    s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
      t ^ 2 * (-φ t) * Real.exp (w t / 2) / Real.sqrt (4 * Real.pi) := by
  obtain ⟨a1, a2⟩ := mass_sq (w := w) hs hp
  obtain ⟨b1, b2⟩ := mass_sq (w := w) ht hq
  rw [← a1, ← b1] at h
  have hpi : 0 < 4 * Real.pi := by positivity
  have h' := lt_of_mul_lt_mul_right h hpi.le
  exact lt_of_pow_lt_pow_left₀ 2 b2.le h'

set_option maxHeartbeats 8000000 in
/-- The assembly: the statement of `Work.Math.BonnorEbertMin.bonnor_ebert_min`. -/
theorem main (S : ℝ) (hS : 150 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ ξ₂ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧ 67.0075 ≤ ξ₂ ∧ ξ₂ ≤ 67.0076 ∧
      (∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ₁ →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ s ∈ Icc ξ₁ S, s ≠ ξ₂ →
        ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      0.694366 ≤ ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₂ ^ 2 * (-φ ξ₂) * Real.exp (w ξ₂ / 2) / Real.sqrt (4 * Real.pi) ≤ 0.694367 ∧
      2579.69 ≤ Real.exp (-w ξ₂) ∧ Real.exp (-w ξ₂) ≤ 2579.71 := by
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
  have h150 : (150 : ℝ) ≤ S := hS
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
  obtain ⟨cdec, cbr, cinc, k150u, k150v⟩ := Work.Math.BEHChain.chain (u := U) (v := V)
    (fun t ht => (dW t ⟨ht.1, ht.2.trans h150⟩).1.mono sub150)
    (fun t ht => (dW t ⟨ht.1, ht.2.trans h150⟩).2.mono sub150)
    (by rw [abs_le]; constructor <;> linarith) v7
  -- the zero of g = 2U − V in the bracket
  set A : ℝ := 418797 / 6250 with hA
  set B : ℝ := 3350379 / 50000 with hB
  have hAB : A ≤ B := by norm_num [hA, hB]
  have hA7 : (7 : ℝ) ≤ A := by norm_num [hA]
  have hBS : B ≤ 150 := by norm_num [hB]
  have subAB : Icc A B ⊆ Icc 7 S := Icc_subset_Icc hA7 (by linarith)
  have cg : ContinuousOn (fun s => 2 * U s - V s) (Icc A B) :=
    ((continuousOn_const.mul cU).sub cV).mono subAB
  have gA0 : 2 * U A - V A < 0 := cdec A ⟨hA7, le_rfl⟩
  have gB0 : 0 < 2 * U B - V B := cinc B ⟨le_rfl, by linarith⟩
  obtain ⟨ξ₂, hξ₂, hg0⟩ := intermediate_value_Icc hAB cg ⟨gA0.le, gB0.le⟩
  have gmono : StrictMonoOn (fun s => 2 * U s - V s) (Icc A B) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc A B) cg
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
  have hA7' : (7 : ℝ) < A := by norm_num [hA]
  have ξ7 : (7 : ℝ) < ξ₂ := by linarith [hξ₂.1]
  have ξS : ξ₂ ≤ 150 := by linarith [hξ₂.2]
  have gneg : ∀ s ∈ Icc (7 : ℝ) ξ₂, s ≠ ξ₂ → 2 * U s - V s < 0 := by
    intro s hs hne
    rcases le_or_gt s A with h | h
    · exact cdec s ⟨hs.1, h⟩
    · have hlt : s < ξ₂ := lt_of_le_of_ne hs.2 hne
      have := gmono ⟨h.le, by linarith [hξ₂.2]⟩ hξ₂ hlt
      simp only at this hg0; linarith
  have gpos : ∀ s ∈ Icc ξ₂ 150, s ≠ ξ₂ → 0 < 2 * U s - V s := by
    intro s hs hne
    rcases le_or_gt B s with h | h
    · exact cinc s ⟨h, hs.2⟩
    · have hlt : ξ₂ < s := lt_of_le_of_ne hs.1 (Ne.symm hne)
      have := gmono hξ₂ ⟨by linarith [hξ₂.1], h.le⟩ hlt
      simp only at this hg0; linarith
  -- P = U V³ on either side of ξ₂
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
  have Panti : StrictAntiOn (fun s => U s * V s ^ 3) (Icc 7 ξ₂) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 7 ξ₂) (cP.mono (Icc_subset_Icc le_rfl (by linarith)))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨hx.1, by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := gneg x ⟨hx.1.le, hx.2.le⟩ hx.2.ne
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    have : 0 < U x * V x ^ 3 := by positivity
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg this hg) hx0
  have Pmono : StrictMonoOn (fun s => U s * V s ^ 3) (Icc ξ₂ 150) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ξ₂ 150) (cP.mono (Icc_subset_Icc ξ7.le h150))
    intro x hx
    rw [interior_Icc] at hx
    have hxS : x ∈ Ioo (7 : ℝ) S := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [(dP x hxS).deriv]
    have hg := gpos x ⟨hx.1.le, hx.2.le⟩ hx.1.ne'
    have hu := Upos x (Ioo_subset_Icc_self hxS)
    have hv := Vpos x (Ioo_subset_Icc_self hxS)
    have hx0 : 0 < x := by linarith [hx.1]
    positivity
  -- the state at ξ₂: v = 2u, u in the bracket window
  obtain ⟨-, ub1, ub2⟩ := cbr ξ₂ hξ₂
  have hVξ : V ξ₂ = 2 * U ξ₂ := by simp only at hg0; linarith
  have ξI : ξ₂ ∈ Icc (7 : ℝ) S := ⟨ξ7.le, by linarith⟩
  have ξ0 : 0 < ξ₂ := by linarith
  obtain ⟨Mξ2, Mξpos⟩ := mass_sq (w := w) ξ0 (φneg ξ₂ ξI)
  have hP8 : U ξ₂ * V ξ₂ ^ 3 = 8 * U ξ₂ ^ 4 := by rw [hVξ]; ring
  have hMξ : M ξ₂ ^ 2 * (4 * Real.pi) = 8 * U ξ₂ ^ 4 := by
    rw [← hP8]; exact Mξ2
  have pil := Real.pi_gt_d20
  have pih := Real.pi_lt_d20
  have u4l : (932876650 / 1000000000 : ℝ) ^ 4 ≤ U ξ₂ ^ 4 := pow_le_pow_left₀ (by norm_num) ub1 4
  have u4h : U ξ₂ ^ 4 ≤ (932877060 / 1000000000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by linarith [Upos ξ₂ ξI]) ub2 4
  have Mlo : (0.694366 : ℝ) ≤ M ξ₂ := by
    by_contra hc
    push_neg at hc
    have h2 : M ξ₂ ^ 2 < 0.694366 ^ 2 := pow_lt_pow_left₀ hc Mξpos.le (by norm_num)
    have h3 : M ξ₂ ^ 2 * (4 * Real.pi) < 0.694366 ^ 2 * (4 * Real.pi) :=
      mul_lt_mul_of_pos_right h2 (by positivity)
    nlinarith
  have Mhi : M ξ₂ ≤ 0.694367 := by
    by_contra hc
    push_neg at hc
    have h2 : (0.694367 : ℝ) ^ 2 < M ξ₂ ^ 2 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
    have h3 : 0.694367 ^ 2 * (4 * Real.pi) < M ξ₂ ^ 2 * (4 * Real.pi) :=
      mul_lt_mul_of_pos_right h2 (by positivity)
    nlinarith
  -- the density contrast: e^{−w} = s² / (u v)
  have hUV : U ξ₂ * V ξ₂ = ξ₂ ^ 2 * Real.exp (w ξ₂) := by
    have hp0 : φ ξ₂ ≠ 0 := (φneg ξ₂ ξI).ne
    simp only [hU, hV]; field_simp
  have hcon : Real.exp (-w ξ₂) = ξ₂ ^ 2 / (2 * U ξ₂ ^ 2) := by
    have h2 : U ξ₂ * V ξ₂ = 2 * U ξ₂ ^ 2 := by rw [hVξ]; ring
    rw [hUV] at h2
    have hu0' : (0 : ℝ) < U ξ₂ := Upos ξ₂ ξI
    have hE : Real.exp (w ξ₂) = 2 * U ξ₂ ^ 2 / ξ₂ ^ 2 := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [Real.exp_neg, hE]; field_simp
  have hu0 : (0 : ℝ) < U ξ₂ := Upos ξ₂ ξI
  have hAξ : (418797 / 6250 : ℝ) ≤ ξ₂ := hξ₂.1
  have hBξ : ξ₂ ≤ 3350379 / 50000 := hξ₂.2
  have Clo : (2579.69 : ℝ) ≤ Real.exp (-w ξ₂) := by
    rw [hcon, le_div_iff₀ (by positivity)]
    have : (0.932877060 : ℝ) ^ 2 ≥ U ξ₂ ^ 2 := pow_le_pow_left₀ hu0.le (by norm_num at ub2 ⊢; linarith) 2
    nlinarith
  have Chi : Real.exp (-w ξ₂) ≤ 2579.71 := by
    rw [hcon, div_le_iff₀ (by positivity)]
    have : (0.932876650 : ℝ) ^ 2 ≤ U ξ₂ ^ 2 := pow_le_pow_left₀ (by norm_num) (by norm_num at ub1 ⊢; linarith) 2
    nlinarith
  -- beyond 150: Volterra's function
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
  have I150 : (150 : ℝ) ∈ Icc 150 S := ⟨le_rfl, hS⟩
  have P150 : ∀ s ∈ Icc (150 : ℝ) S, 6059 / 1000 < U s * V s ^ 3 := by
    intro s hs
    have hVs := VfA I150 hs hs.1
    have k1 := abs_le.1 k150u
    have k2 := abs_le.1 k150v
    have hsI : s ∈ Icc (7 : ℝ) S := ⟨by linarith [hs.1], hs.2⟩
    exact Work.Math.BEHTail.uv_lower (Upos s hsI) (Vpos s hsI) (by linarith [k1.1]) (by linarith [k1.2])
      (by linarith [k2.1]) (by linarith [k2.2]) hVs
  have Pξlt : U ξ₂ * V ξ₂ ^ 3 < 6059 / 1000 := by
    rw [← Mξ2]
    have h2 : M ξ₂ ^ 2 ≤ 0.694367 ^ 2 := pow_le_pow_left₀ Mξpos.le Mhi 2
    have pi6 := Real.pi_lt_d6
    nlinarith
  -- assembly
  have hmax : ∀ s ∈ Icc (0 : ℝ) S, s ≠ ξ → M s < M ξ := by
    intro s hs hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hmono ⟨hs.1, hlt.le⟩ ⟨by linarith, le_rfl⟩ hlt
    · rcases le_or_gt s 7 with h7 | h7
      · exact hanti ⟨le_rfl, by linarith⟩ ⟨hgt.le, h7⟩ hgt
      · exact lt_of_lt_of_le (T7 s ⟨h7.le, hs.2⟩) hm1
  have hmin : ∀ s ∈ Icc ξ S, s ≠ ξ₂ → M ξ₂ < M s := by
    intro s hs hne
    have hs0 : 0 < s := by linarith [hs.1]
    rcases le_or_gt s 7 with h7 | h7
    · have I7 : (7 : ℝ) ∈ Icc (7 : ℝ) S := ⟨le_rfl, hS7⟩
      have a : M 7 ≤ M s := hanti.antitoneOn ⟨hs.1, h7⟩ ⟨by linarith, le_rfl⟩ h7
      have b : M ξ₂ < M 7 := mass_lt ξ0 (φneg ξ₂ ξI) (by norm_num) (φneg 7 I7)
        (Panti ⟨le_rfl, ξ7.le⟩ ⟨ξ7.le, le_rfl⟩ ξ7)
      exact lt_of_lt_of_le b a
    · have sI : s ∈ Icc (7 : ℝ) S := ⟨h7.le, hs.2⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact mass_lt ξ0 (φneg ξ₂ ξI) hs0 (φneg s sI)
          (Panti ⟨h7.le, hlt.le⟩ ⟨ξ7.le, le_rfl⟩ hlt)
      · rcases le_or_gt s 150 with h1 | h1
        · exact mass_lt ξ0 (φneg ξ₂ ξI) hs0 (φneg s sI)
            (Pmono ⟨le_rfl, ξS⟩ ⟨hgt.le, h1⟩ hgt)
        · exact mass_lt ξ0 (φneg ξ₂ ξI) hs0 (φneg s sI)
            (lt_trans Pξlt (P150 s ⟨h1.le, hs.2⟩))
  refine ⟨ξ, ξ₂, hξ1, hξ2, by norm_num at hAξ ⊢; linarith, by norm_num at hBξ ⊢; linarith,
    hmax, hmin, Mlo, Mhi, Clo, Chi⟩

end Work.Math.BEHMain
