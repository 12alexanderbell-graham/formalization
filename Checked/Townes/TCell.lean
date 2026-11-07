import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Sim.ODETools
import Checked.Math.LECell
/-! Townes ground state, `TCell`: one validated Grönwall step of the Townes radial system on a slab where its field is Lipschitz, with the defect of the second component in multiplied-out form. Promoted from `Work/Townes/TCell.lean`. -/

namespace Checked.Townes.TCell
open Set Checked.Sim Checked.Math.LECell

noncomputable def tF (ξ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -(1 / ξ * p.2) + p.1 - p.1 ^ 3)

/-- The slab |θ| ≤ TH. -/
def slab (TH : ℝ) : Set (ℝ × ℝ) := {p | |p.1| ≤ TH}

theorem cube_sub_le {a b TH : ℝ} (ha : |a| ≤ TH) (hb : |b| ≤ TH) :
    |a ^ 3 - b ^ 3| ≤ 3 * TH ^ 2 * |a - b| := by
  have e : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
  rw [e, abs_mul, mul_comm]
  have h1 : |a ^ 2 + a * b + b ^ 2| ≤ 3 * TH ^ 2 := by
    have hTH : 0 ≤ TH := (abs_nonneg _).trans ha
    have a2 : a ^ 2 ≤ TH ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
    have b2 : b ^ 2 ≤ TH ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have ab : |a * b| ≤ TH ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul ha hb (abs_nonneg _) hTH
    rw [abs_le] at ab ⊢
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

theorem lip_slab {ξ t0 TH K : ℝ} (ht0 : 0 < t0) (hξ : t0 ≤ ξ) (hK1 : 1 ≤ K)
    (hK : 1 / t0 + 1 + 3 * TH ^ 2 ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (tF ξ) (slab TH) := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have hK0 : (0 : ℝ) ≤ K := by linarith
  rw [Real.coe_toNNReal _ hK0]
  simp only [tF, Prod.dist_eq, Real.dist_eq]
  set m := max |p.1 - q.1| |p.2 - q.2|
  have hd1 : |p.1 - q.1| ≤ m := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ m := le_max_right _ _
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  have hξ0 : 0 < ξ := lt_of_lt_of_le ht0 hξ
  refine max_le (by nlinarith) ?_
  have e : (-(1 / ξ * p.2) + p.1 - p.1 ^ 3) - (-(1 / ξ * q.2) + q.1 - q.1 ^ 3) =
      -(1 / ξ * (p.2 - q.2)) + (p.1 - q.1) - (p.1 ^ 3 - q.1 ^ 3) := by ring
  rw [e]
  have c1 := cube_sub_le (TH := TH) hp hq
  have c2 : |1 / ξ * (p.2 - q.2)| ≤ 1 / t0 * m := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) ht0 hξ) hd2 (abs_nonneg _)
      (by positivity)
  have c3 : 3 * TH ^ 2 * |p.1 - q.1| ≤ 3 * TH ^ 2 * m :=
    mul_le_mul_of_nonneg_left hd1 (by positivity)
  calc |-(1 / ξ * (p.2 - q.2)) + (p.1 - q.1) - (p.1 ^ 3 - q.1 ^ 3)|
      ≤ |1 / ξ * (p.2 - q.2)| + |p.1 - q.1| + |p.1 ^ 3 - q.1 ^ 3| := by
        have := abs_sub (-(1 / ξ * (p.2 - q.2)) + (p.1 - q.1)) (p.1 ^ 3 - q.1 ^ 3)
        have := abs_add_le (-(1 / ξ * (p.2 - q.2))) (p.1 - q.1)
        rw [abs_neg] at this
        linarith
    _ ≤ 1 / t0 * m + m + 3 * TH ^ 2 * m := by linarith
    _ = (1 / t0 + 1 + 3 * TH ^ 2) * m := by ring
    _ ≤ K * m := mul_le_mul_of_nonneg_right hK hm

/-- One validated step on the cell [t₀, t₀ + h] ⊆ (0, T] for every solution (θ, φ) of the
Lane–Emden system (derivatives within [0, T]). -/
theorem cell (pt pp : List ℚ) {θ φ : ℝ → ℝ} {T t0 h δ ε B TH K : ℝ}
    (ht0 : 0 < t0) (hT : t0 + h ≤ T) (hh : 0 < h) (hK1 : 1 ≤ K)
    (hK : 1 / t0 + 1 + 3 * TH ^ 2 ≤ K) (hKh : K * h < 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hθ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt θ (φ t) (Icc 0 T) t)
    (hφ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt φ (-(1 / t * φ t) + θ t - θ t ^ 3) (Icc 0 T) t)
    (ht1 : ∀ σ ∈ Icc 0 h, -(TH - 1 / 100) ≤ evalQ pt σ)
    (ht2 : ∀ σ ∈ Icc 0 h, evalQ pt σ ≤ TH - 1 / 100)
    (hd1 : ∀ σ ∈ Icc 0 h, |dEvalQ pt σ - evalQ pp σ| ≤ ε)
    (hd2 : ∀ σ ∈ Icc 0 h,
      |(t0 + σ) * dEvalQ pp σ + evalQ pp σ - (t0 + σ) * (evalQ pt σ - evalQ pt σ ^ 3)| ≤ ε * t0)
    (h0 : |θ t0 - evalQ pt 0| ≤ δ) (h0' : |φ t0 - evalQ pp 0| ≤ δ)
    (hB : δ * (1 / (1 - K * h)) + ε / K * (1 / (1 - K * h) - 1) ≤ B)
    (hBM : B < 1 / 100) :
    ∀ t ∈ Icc t0 (t0 + h), |θ t - evalQ pt (t - t0)| ≤ B ∧ |φ t - evalQ pp (t - t0)| ≤ B := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hT0 : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0.le hT
  have hs : ∀ t ∈ Icc t0 (t0 + h), t - t0 ∈ Icc 0 h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set f : ℝ → ℝ × ℝ := fun t => (θ t, φ t) with hfdef
  set g : ℝ → ℝ × ℝ := fun t => (evalQ pt (t - t0), evalQ pp (t - t0)) with hg
  have hfd : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt f (tF t (f t)) (Icc 0 T) t :=
    fun t ht => (hθ t ht).prodMk (hφ t ht)
  have key := tube_cell_t (F := tF) (K := Real.toNNReal K) (S := slab TH) (f := f) (g := g)
    (g' := fun t => (dEvalQ pt (t - t0), dEvalQ pp (t - t0))) (a := t0) (b := t0 + h)
    (δ := δ) (ε := ε) (B := B) (B' := 1 / 100)
    (fun t ht => lip_slab ht0 ht.1 hK1 hK) (by linarith)
    (fun t ht => ((hfd t ht).continuousWithinAt).mono hT0)
    (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht0], by linarith [ht.2]⟩))
    (((continuous_evalQ pt).comp (continuous_sub_right t0)).prodMk
      ((continuous_evalQ pp).comp (continuous_sub_right t0))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ pt (t - t0)).comp_sub_const t t0).prodMk
      ((hasDerivAt_evalQ pp (t - t0)).comp_sub_const t t0)).hasDerivWithinAt)
    (fun t ht => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      simp only [hg, tF, Prod.dist_eq, Real.dist_eq]
      refine max_le (hd1 _ hσ) ?_
      have h2 := hd2 _ hσ
      have et : t0 + (t - t0) = t := by ring
      rw [et] at h2
      have e : dEvalQ pp (t - t0) - (-(1 / t * evalQ pp (t - t0)) + evalQ pt (t - t0) -
            evalQ pt (t - t0) ^ 3) =
          (t * dEvalQ pp (t - t0) + evalQ pp (t - t0) -
            t * (evalQ pt (t - t0) - evalQ pt (t - t0) ^ 3)) / t := by
        field_simp
        ring
      rw [e, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
      exact h2.trans (mul_le_mul_of_nonneg_left ht.1 hε))
    (fun t ht z hz => by
      simp only [hg, Prod.dist_eq, Real.dist_eq, max_lt_iff] at hz
      have g1 := ht1 _ (hs t ht)
      have g2 := ht2 _ (hs t ht)
      have a1 := abs_lt.1 hz.1
      show |z.1| ≤ TH
      rw [abs_le]; constructor <;> linarith [a1.1, a1.2])
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

/-- Crude lower bound p(σ) ≥ c₀ − h·Σ|cₖ₊₁|hᵏ on [0, h]. -/
theorem lower_of (p : List ℚ) {σ h : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    ((p.headD 0 : ℚ) : ℝ) - h * evalQ (p.tail.map (fun c => |c|)) h ≤ evalQ p σ := by
  cases p with
  | nil => simp [evalQ]
  | cons c cs => simpa using evalQ_ge c cs h0 h1

/-- Crude upper bound p(σ) ≤ c₀ + h·Σ|cₖ₊₁|hᵏ on [0, h]. -/
theorem upper_of (p : List ℚ) {σ h : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ h) :
    evalQ p σ ≤ ((p.headD 0 : ℚ) : ℝ) + h * evalQ (p.tail.map (fun c => |c|)) h := by
  cases p with
  | nil => simp [evalQ]
  | cons c cs => simpa using evalQ_le c cs h0 h1

end Checked.Townes.TCell
