import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Checked.Math.LENCell

/-! Lane–Emden equation of index three halves: the nonlinearity θ to the power three halves as `g32 θ`, the cube of the square root (equal to Mathlib's real power for every real θ, `rpow32_eq`), its Lipschitz bound on a slab (`g32_lip`), the closeness of `g32 x` to the cube of `y` from a certificate that the square of `y` is close to `x` (`g32_close`), and the validated cell step `cell` (Grönwall, generic tube lemma `Checked.Math.LENCell.tube_cell_t`). Promoted verbatim from `Work/Math/LE32Cell.lean`. -/

namespace Checked.Math.LE32Cell
open Set Checked.Sim Checked.Math.LENCell

/-- θ ^ (3/2) through the square root (zero for θ ≤ 0). -/
noncomputable def g32 (x : ℝ) : ℝ := Real.sqrt x ^ 3

theorem rpow32_eq (x : ℝ) : x ^ ((3 : ℝ) / 2) = g32 x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [g32, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  · rw [g32, Real.sqrt_eq_zero'.2 hx.le, Real.rpow_def_of_neg hx]
    have : Real.cos ((3 : ℝ) / 2 * Real.pi) = 0 := by
      rw [show (3 : ℝ) / 2 * Real.pi = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
        Real.cos_pi_div_two, neg_zero]
    rw [this]
    norm_num

theorem g32_nonneg (x : ℝ) : 0 ≤ g32 x := by
  unfold g32; positivity

theorem sq_sqrt_max (a : ℝ) : Real.sqrt a ^ 2 = max a 0 := by
  rcases le_or_gt 0 a with ha | ha
  · rw [Real.sq_sqrt ha, max_eq_left ha]
  · rw [Real.sqrt_eq_zero'.2 ha.le, max_eq_right ha.le]; norm_num

theorem cube_sub_le {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huS : u ≤ S) (hvS : v ≤ S) :
    |u ^ 3 - v ^ 3| ≤ 3 / 2 * S * |u ^ 2 - v ^ 2| := by
  have e1 : u ^ 3 - v ^ 3 = (u - v) * (u ^ 2 + u * v + v ^ 2) := by ring
  have e2 : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
  have hq : u ^ 2 + u * v + v ^ 2 ≤ 3 / 2 * S * (u + v) := by
    nlinarith [mul_le_mul_of_nonneg_right huS hu, mul_le_mul_of_nonneg_right hvS hv,
      mul_le_mul_of_nonneg_right huS hv, mul_le_mul_of_nonneg_right hvS hu]
  rw [e1, e2, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ u ^ 2 + u * v + v ^ 2),
    abs_of_nonneg (by positivity : 0 ≤ u + v)]
  calc |u - v| * (u ^ 2 + u * v + v ^ 2) ≤ |u - v| * (3 / 2 * S * (u + v)) :=
        mul_le_mul_of_nonneg_left hq (abs_nonneg _)
    _ = 3 / 2 * S * (|u - v| * (u + v)) := by ring

theorem sqrt_le_of {a TH S : ℝ} (ha : |a| ≤ TH) (hS0 : 0 ≤ S) (hTS : TH ≤ S ^ 2) :
    Real.sqrt a ≤ S := by
  calc Real.sqrt a ≤ Real.sqrt (S ^ 2) :=
        Real.sqrt_le_sqrt ((le_abs_self a).trans (ha.trans hTS))
    _ = S := Real.sqrt_sq hS0

/-- Lipschitz bound of θ ^ (3/2) on the slab |θ| ≤ TH ≤ S². -/
theorem g32_lip {a b TH S : ℝ} (ha : |a| ≤ TH) (hb : |b| ≤ TH) (hS0 : 0 ≤ S) (hTS : TH ≤ S ^ 2) :
    |g32 a - g32 b| ≤ 3 / 2 * S * |a - b| := by
  have h1 := cube_sub_le (Real.sqrt_nonneg a) (Real.sqrt_nonneg b) (sqrt_le_of ha hS0 hTS)
    (sqrt_le_of hb hS0 hTS)
  rw [sq_sqrt_max, sq_sqrt_max] at h1
  unfold g32
  exact h1.trans (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs a b 0) (by positivity))

/-- `g32 x` is close to `y ^ 3` when `y ^ 2` is close to `x` and `y` is bounded away from zero. -/
theorem g32_close {x y c P η : ℝ} (hc : 0 < c) (hcy : c ≤ y) (hyP : y ≤ P)
    (hη : |y ^ 2 - x| ≤ η) (hηc : η < c ^ 2) :
    |g32 x - y ^ 3| ≤ η / c * (3 * P ^ 2 + 3 / 2 * η) := by
  have hy0 : 0 ≤ y := hc.le.trans hcy
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hη
  have hyc : c ^ 2 ≤ y ^ 2 := by nlinarith
  have hx : 0 < x := by have := (abs_le.1 hη).2; nlinarith
  set u := Real.sqrt x with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg x
  have hux : u ^ 2 = x := Real.sq_sqrt hx.le
  have hupy : c ≤ u + y := by linarith
  have hd : |u - y| ≤ η / c := by
    rw [le_div_iff₀ hc]
    have e : |u - y| * (u + y) = |y ^ 2 - x| := by
      rw [← hux, show y ^ 2 - u ^ 2 = -((u - y) * (u + y)) by ring, abs_neg, abs_mul,
        abs_of_nonneg (by linarith : 0 ≤ u + y)]
    calc |u - y| * c ≤ |u - y| * (u + y) := mul_le_mul_of_nonneg_left hupy (abs_nonneg _)
      _ = |y ^ 2 - x| := e
      _ ≤ η := hη
  have hyP2 : y ^ 2 ≤ P ^ 2 := by nlinarith
  have hq : u ^ 2 + u * y + y ^ 2 ≤ 3 * P ^ 2 + 3 / 2 * η := by
    have := (abs_le.1 hη).1
    nlinarith [sq_nonneg (u - y)]
  have e1 : u ^ 3 - y ^ 3 = (u - y) * (u ^ 2 + u * y + y ^ 2) := by ring
  unfold g32
  rw [← hu, e1, abs_mul, abs_of_nonneg (by positivity : 0 ≤ u ^ 2 + u * y + y ^ 2)]
  exact mul_le_mul hd hq (by positivity) (by positivity)

/-- The Lane–Emden field of index three halves at time ξ. -/
noncomputable def leG (ξ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.2, -(2 / ξ * p.2) - g32 p.1)

theorem lip_slab32 {ξ t0 TH K S : ℝ} (ht0 : 0 < t0) (hξ : t0 ≤ ξ) (hK1 : 1 ≤ K)
    (hS0 : 0 ≤ S) (hTS : TH ≤ S ^ 2) (hK : 2 / t0 + 3 / 2 * S ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (leG ξ) (slab TH) := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have hK0 : (0 : ℝ) ≤ K := by linarith
  rw [Real.coe_toNNReal _ hK0]
  simp only [leG, Prod.dist_eq, Real.dist_eq]
  set m := max |p.1 - q.1| |p.2 - q.2|
  have hd1 : |p.1 - q.1| ≤ m := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ m := le_max_right _ _
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  have hξ0 : 0 < ξ := lt_of_lt_of_le ht0 hξ
  refine max_le (by nlinarith) ?_
  have e : (-(2 / ξ * p.2) - g32 p.1) - (-(2 / ξ * q.2) - g32 q.1) =
      -(2 / ξ * (p.2 - q.2)) - (g32 p.1 - g32 q.1) := by ring
  rw [e]
  have c1 := g32_lip (TH := TH) hp hq hS0 hTS
  have c2 : |2 / ξ * (p.2 - q.2)| ≤ 2 / t0 * m := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) ht0 hξ) hd2 (abs_nonneg _)
      (by positivity)
  have c3 : 3 / 2 * S * |p.1 - q.1| ≤ 3 / 2 * S * m :=
    mul_le_mul_of_nonneg_left hd1 (by positivity)
  calc |-(2 / ξ * (p.2 - q.2)) - (g32 p.1 - g32 q.1)|
      ≤ |2 / ξ * (p.2 - q.2)| + |g32 p.1 - g32 q.1| := by
        rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
    _ ≤ 2 / t0 * m + 3 / 2 * S * m := by linarith
    _ = (2 / t0 + 3 / 2 * S) * m := by ring
    _ ≤ K * m := mul_le_mul_of_nonneg_right hK hm

/-- One validated step on the cell [t₀, t₀ + h] ⊆ (0, T] for every solution (θ, φ) of the
Lane–Emden system (derivatives within [0, T]). -/
theorem cell (pt pp : List ℚ) {θ φ : ℝ → ℝ} {T t0 h δ ε B TH K S : ℝ}
    (ht0 : 0 < t0) (hT : t0 + h ≤ T) (hh : 0 < h) (hK1 : 1 ≤ K)
    (hS0 : 0 ≤ S) (hTS : TH ≤ S ^ 2) (hK : 2 / t0 + 3 / 2 * S ≤ K) (hKh : K * h < 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hθ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt θ (φ t) (Icc 0 T) t)
    (hφ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt φ (-(2 / t * φ t) - g32 (θ t)) (Icc 0 T) t)
    (ht1 : ∀ σ ∈ Icc 0 h, -(TH - 1 / 100) ≤ evalQ pt σ)
    (ht2 : ∀ σ ∈ Icc 0 h, evalQ pt σ ≤ TH - 1 / 100)
    (hd1 : ∀ σ ∈ Icc 0 h, |dEvalQ pt σ - evalQ pp σ| ≤ ε)
    (hd2 : ∀ σ ∈ Icc 0 h,
      |(t0 + σ) * dEvalQ pp σ + 2 * evalQ pp σ + (t0 + σ) * g32 (evalQ pt σ)| ≤ ε * t0)
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
  have hfd : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt f (leG t (f t)) (Icc 0 T) t :=
    fun t ht => (hθ t ht).prodMk (hφ t ht)
  have key := tube_cell_t (F := leG) (K := Real.toNNReal K) (S := slab TH) (f := f) (g := g)
    (g' := fun t => (dEvalQ pt (t - t0), dEvalQ pp (t - t0))) (a := t0) (b := t0 + h)
    (δ := δ) (ε := ε) (B := B) (B' := 1 / 100)
    (fun t ht => lip_slab32 ht0 ht.1 hK1 hS0 hTS hK) (by linarith)
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
      simp only [hg, leG, Prod.dist_eq, Real.dist_eq]
      refine max_le (hd1 _ hσ) ?_
      have h2 := hd2 _ hσ
      have et : t0 + (t - t0) = t := by ring
      rw [et] at h2
      have e : dEvalQ pp (t - t0) - (-(2 / t * evalQ pp (t - t0)) - g32 (evalQ pt (t - t0))) =
          (t * dEvalQ pp (t - t0) + 2 * evalQ pp (t - t0) + t * g32 (evalQ pt (t - t0))) / t := by
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

end Checked.Math.LE32Cell
