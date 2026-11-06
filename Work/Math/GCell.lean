import Mathlib
import Work.Sim.ODETools
import Work.Math.LECell

/-!
# Gelfand problem in the ball: validated cell step

`cell`: one Grönwall step (via `Work.Math.LECell.tube_cell_t`) for the polynomial system of the
isothermal Emden–Chandrasekhar equation in the variables E = e^w and φ = w':
E' = E·φ, φ' = −(2/t)φ − E, on ℝ × ℝ (sup norm), with the state confined to the box
|E| ≤ EH, |φ| ≤ PH, where the field is K-Lipschitz for K ≥ max(1, PH + EH, 2/t₀ + 1) at times
t ≥ t₀ > 0. The defect of the second component is certified in the multiplied-out form
(t₀+σ)p_φ' + 2p_φ + (t₀+σ)p_E (no division). `exp_sol`: E = exp ∘ w satisfies E' = E·φ.
-/

namespace Work.Math.GCell
open Set Work.Sim Work.Math.LECell

/-- The Gelfand field at time t in the variables (E, φ). -/
noncomputable def gF (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * p.2, -(2 / t * p.2) - p.1)

/-- The box |E| ≤ EH, |φ| ≤ PH. -/
def box (EH PH : ℝ) : Set (ℝ × ℝ) := {p | |p.1| ≤ EH ∧ |p.2| ≤ PH}

theorem lip_box {t t0 EH PH K : ℝ} (ht0 : 0 < t0) (ht : t0 ≤ t) (hK1 : 1 ≤ K)
    (hK : PH + EH ≤ K) (hK2 : 2 / t0 + 1 ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (gF t) (box EH PH) := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have hK0 : (0 : ℝ) ≤ K := by linarith
  rw [Real.coe_toNNReal _ hK0]
  simp only [gF, Prod.dist_eq, Real.dist_eq]
  set m := max |p.1 - q.1| |p.2 - q.2|
  have hd1 : |p.1 - q.1| ≤ m := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ m := le_max_right _ _
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  have ht0' : 0 < t := lt_of_lt_of_le ht0 ht
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  refine max_le ?_ ?_
  · have e : p.1 * p.2 - q.1 * q.2 = p.2 * (p.1 - q.1) + q.1 * (p.2 - q.2) := by ring
    rw [e]
    calc |p.2 * (p.1 - q.1) + q.1 * (p.2 - q.2)|
        ≤ |p.2 * (p.1 - q.1)| + |q.1 * (p.2 - q.2)| := abs_add_le _ _
      _ = |p.2| * |p.1 - q.1| + |q.1| * |p.2 - q.2| := by rw [abs_mul, abs_mul]
      _ ≤ PH * m + EH * m := by
          have hPH : 0 ≤ PH := (abs_nonneg _).trans hp2
          have hEH : 0 ≤ EH := (abs_nonneg _).trans hp1
          gcongr
      _ = (PH + EH) * m := by ring
      _ ≤ K * m := mul_le_mul_of_nonneg_right hK hm
  · have e : (-(2 / t * p.2) - p.1) - (-(2 / t * q.2) - q.1) =
        -(2 / t * (p.2 - q.2)) - (p.1 - q.1) := by ring
    rw [e]
    have c2 : |2 / t * (p.2 - q.2)| ≤ 2 / t0 * m := by
      rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) ht0 ht) hd2 (abs_nonneg _)
        (by positivity)
    calc |-(2 / t * (p.2 - q.2)) - (p.1 - q.1)|
        ≤ |2 / t * (p.2 - q.2)| + |p.1 - q.1| := by
          rw [sub_eq_add_neg, ← neg_add, abs_neg]; exact abs_add_le _ _
      _ ≤ 2 / t0 * m + m := by linarith
      _ = (2 / t0 + 1) * m := by ring
      _ ≤ K * m := mul_le_mul_of_nonneg_right hK2 hm

/-- One validated step on the cell [t₀, t₀ + h] ⊆ (0, T] for every solution (E, φ) of
E' = E·φ, φ' = −(2/t)φ − E (derivatives within [0, T]). -/
theorem cell (pe pp : List ℚ) {E φ : ℝ → ℝ} {T t0 h δ ε B EH PH K : ℝ}
    (ht0 : 0 < t0) (hT : t0 + h ≤ T) (hh : 0 < h) (hK1 : 1 ≤ K)
    (hK : PH + EH ≤ K) (hK2 : 2 / t0 + 1 ≤ K) (hKh : K * h < 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hE : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt E (E t * φ t) (Icc 0 T) t)
    (hφ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt φ (-(2 / t * φ t) - E t) (Icc 0 T) t)
    (he1 : ∀ σ ∈ Icc 0 h, -(EH - 1 / 100) ≤ evalQ pe σ)
    (he2 : ∀ σ ∈ Icc 0 h, evalQ pe σ ≤ EH - 1 / 100)
    (hp1 : ∀ σ ∈ Icc 0 h, -(PH - 1 / 100) ≤ evalQ pp σ)
    (hp2 : ∀ σ ∈ Icc 0 h, evalQ pp σ ≤ PH - 1 / 100)
    (hd1 : ∀ σ ∈ Icc 0 h, |dEvalQ pe σ - evalQ pe σ * evalQ pp σ| ≤ ε)
    (hd2 : ∀ σ ∈ Icc 0 h,
      |(t0 + σ) * dEvalQ pp σ + 2 * evalQ pp σ + (t0 + σ) * evalQ pe σ| ≤ ε * t0)
    (h0 : |E t0 - evalQ pe 0| ≤ δ) (h0' : |φ t0 - evalQ pp 0| ≤ δ)
    (hB : δ * (1 / (1 - K * h)) + ε / K * (1 / (1 - K * h) - 1) ≤ B)
    (hBM : B < 1 / 100) :
    ∀ t ∈ Icc t0 (t0 + h), |E t - evalQ pe (t - t0)| ≤ B ∧ |φ t - evalQ pp (t - t0)| ≤ B := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hT0 : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0.le hT
  have hs : ∀ t ∈ Icc t0 (t0 + h), t - t0 ∈ Icc 0 h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set f : ℝ → ℝ × ℝ := fun t => (E t, φ t) with hfdef
  set g : ℝ → ℝ × ℝ := fun t => (evalQ pe (t - t0), evalQ pp (t - t0)) with hg
  have hfd : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt f (gF t (f t)) (Icc 0 T) t :=
    fun t ht => (hE t ht).prodMk (hφ t ht)
  have key := tube_cell_t (F := gF) (K := Real.toNNReal K) (S := box EH PH) (f := f) (g := g)
    (g' := fun t => (dEvalQ pe (t - t0), dEvalQ pp (t - t0))) (a := t0) (b := t0 + h)
    (δ := δ) (ε := ε) (B := B) (B' := 1 / 100)
    (fun t ht => lip_box ht0 ht.1 hK1 hK hK2) (by linarith)
    (fun t ht => ((hfd t ht).continuousWithinAt).mono hT0)
    (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht0], by linarith [ht.2]⟩))
    (((continuous_evalQ pe).comp (continuous_sub_right t0)).prodMk
      ((continuous_evalQ pp).comp (continuous_sub_right t0))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ pe (t - t0)).comp_sub_const t t0).prodMk
      ((hasDerivAt_evalQ pp (t - t0)).comp_sub_const t t0)).hasDerivWithinAt)
    (fun t ht => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      simp only [hg, gF, Prod.dist_eq, Real.dist_eq]
      refine max_le (hd1 _ hσ) ?_
      have h2 := hd2 _ hσ
      have et : t0 + (t - t0) = t := by ring
      rw [et] at h2
      have e : dEvalQ pp (t - t0) - (-(2 / t * evalQ pp (t - t0)) - evalQ pe (t - t0)) =
          (t * dEvalQ pp (t - t0) + 2 * evalQ pp (t - t0) + t * evalQ pe (t - t0)) / t := by
        field_simp
        ring
      rw [e, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
      exact h2.trans (mul_le_mul_of_nonneg_left ht.1 hε))
    (fun t ht z hz => by
      simp only [hg, Prod.dist_eq, Real.dist_eq, max_lt_iff] at hz
      have g1 := he1 _ (hs t ht)
      have g2 := he2 _ (hs t ht)
      have g3 := hp1 _ (hs t ht)
      have g4 := hp2 _ (hs t ht)
      have a1 := abs_lt.1 hz.1
      have a2 := abs_lt.1 hz.2
      show |z.1| ≤ EH ∧ |z.2| ≤ PH
      refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith [a1.1, a1.2, a2.1, a2.2])
    hBM
    (by
      simp only [hfdef, hg, sub_self, Prod.dist_eq, Real.dist_eq]
      exact max_le h0 h0')
    (fun t ht => by
      rw [Real.coe_toNNReal _ hK0.le]
      have := gronwallBound_le_cell (K := K) hδ hε hK0
        (show t - t0 ≤ h by linarith [ht.2]) hh hKh
      exact this.trans hB)
  intro t ht
  have h1 := key t ht
  simp only [hfdef, hg, Prod.dist_eq, Real.dist_eq] at h1
  exact ⟨(le_max_left _ _).trans h1, (le_max_right _ _).trans h1⟩

/-- E = exp ∘ w satisfies E' = E·φ when w' = φ. -/
theorem exp_sol {w φ : ℝ → ℝ} {T t : ℝ} (hw : HasDerivWithinAt w (φ t) (Icc 0 T) t) :
    HasDerivWithinAt (fun s => Real.exp (w s)) (Real.exp (w t) * φ t) (Icc 0 T) t :=
  hw.exp

end Work.Math.GCell
