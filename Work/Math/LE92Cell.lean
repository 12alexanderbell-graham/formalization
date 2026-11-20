import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Checked.Math.LENCell

/-! Lane–Emden equation of index nine halves: the nonlinearity θ ^ (9/2) as `g92 θ = √θ ^ 9`
(equal to Mathlib's real power for every real θ, `rpow92_eq`), its Lipschitz bound on a slab
(`g92_lip`), the closeness of `g92 x` to `y ^ 9` from a certificate `y ^ 2 ≈ x` (`g92_close`), and
the validated cell step `cell` for θ' = φ, φ' = −(two/ξ)φ − g92 θ in the WEIGHTED norm
max(|Δθ|, w · |Δφ|) with a positive weight `w` (Grönwall for the field of (θ, w φ), generic tube lemma
`Checked.Math.LENCell.tube_cell_t`). With w = 1 it is the cell of the earlier indices; a weight
above one removes the floor one on the Lipschitz constant that the unweighted max norm imposes
(from θ' = φ), so the enclosure no longer grows like e^ξ on the long range to the first zero near
31.8. Run 2026-11-20T0428Z (from the index seven halves module of run 2026-11-19T2228Z). -/

namespace Work.Math.LE92Cell
open Set Checked.Sim Checked.Math.LENCell

/-- θ ^ (9/2) through the square root (zero for θ ≤ 0). -/
noncomputable def g92 (x : ℝ) : ℝ := Real.sqrt x ^ 9

theorem rpow92_eq (x : ℝ) : x ^ ((9 : ℝ) / 2) = g92 x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [g92, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  · rw [g92, Real.sqrt_eq_zero'.2 hx.le, Real.rpow_def_of_neg hx]
    have : Real.cos ((9 : ℝ) / 2 * Real.pi) = 0 := by
      rw [show (9 : ℝ) / 2 * Real.pi = Real.pi / 2 + 2 * Real.pi + 2 * Real.pi by ring,
        Real.cos_add_two_pi, Real.cos_add_two_pi, Real.cos_pi_div_two]
    rw [this]
    norm_num

theorem g92_nonneg (x : ℝ) : 0 ≤ g92 x := by
  unfold g92; positivity

theorem sq_sqrt_max (a : ℝ) : Real.sqrt a ^ 2 = max a 0 := by
  rcases le_or_gt 0 a with ha | ha
  · rw [Real.sq_sqrt ha, max_eq_left ha]
  · rw [Real.sqrt_eq_zero'.2 ha.le, max_eq_right ha.le]; norm_num

/-- Products of powers of two numbers in [0, S] whose exponents add to `n`. -/
theorem pow_mul_pow_le {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huS : u ≤ S) (hvS : v ≤ S)
    (a b n : ℕ) (hab : a + b = n) : u ^ a * v ^ b ≤ S ^ n := by
  calc u ^ a * v ^ b ≤ S ^ a * S ^ b :=
        mul_le_mul (pow_le_pow_left₀ hu huS a) (pow_le_pow_left₀ hv hvS b) (by positivity)
          (pow_nonneg (hu.trans huS) a)
    _ = S ^ n := by rw [← pow_add, hab]

/-- The sum of the nine products u ^ (8 − i) v ^ i. -/
def nsum (u v : ℝ) : ℝ :=
  u ^ 8 + u ^ 7 * v + u ^ 6 * v ^ 2 + u ^ 5 * v ^ 3 + u ^ 4 * v ^ 4 + u ^ 3 * v ^ 5 +
    u ^ 2 * v ^ 6 + u * v ^ 7 + v ^ 8

theorem nsum_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ nsum u v := by
  unfold nsum; positivity

theorem nine_sub (u v : ℝ) : u ^ 9 - v ^ 9 = (u - v) * nsum u v := by
  unfold nsum; ring

theorem nsum_le {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huS : u ≤ S) (hvS : v ≤ S) :
    nsum u v ≤ 9 / 2 * S ^ 7 * (u + v) := by
  have m := pow_mul_pow_le hu hv huS hvS
  have a0 : u ^ 8 ≤ u * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 7 0 7 rfl) hu
    linarith [show u * (u ^ 7 * v ^ 0) = u ^ 8 by ring]
  have a1 : u ^ 7 * v ≤ u * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 6 1 7 rfl) hu
    linarith [show u * (u ^ 6 * v ^ 1) = u ^ 7 * v by ring]
  have a2 : u ^ 6 * v ^ 2 ≤ u * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 5 2 7 rfl) hu
    linarith [show u * (u ^ 5 * v ^ 2) = u ^ 6 * v ^ 2 by ring]
  have a3 : u ^ 5 * v ^ 3 ≤ u * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 4 3 7 rfl) hu
    linarith [show u * (u ^ 4 * v ^ 3) = u ^ 5 * v ^ 3 by ring]
  have a4u : u ^ 4 * v ^ 4 ≤ u * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 3 4 7 rfl) hu
    linarith [show u * (u ^ 3 * v ^ 4) = u ^ 4 * v ^ 4 by ring]
  have a4v : u ^ 4 * v ^ 4 ≤ v * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 4 3 7 rfl) hv
    linarith [show v * (u ^ 4 * v ^ 3) = u ^ 4 * v ^ 4 by ring]
  have a5 : u ^ 3 * v ^ 5 ≤ v * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 3 4 7 rfl) hv
    linarith [show v * (u ^ 3 * v ^ 4) = u ^ 3 * v ^ 5 by ring]
  have a6 : u ^ 2 * v ^ 6 ≤ v * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 2 5 7 rfl) hv
    linarith [show v * (u ^ 2 * v ^ 5) = u ^ 2 * v ^ 6 by ring]
  have a7 : u * v ^ 7 ≤ v * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 1 6 7 rfl) hv
    linarith [show v * (u ^ 1 * v ^ 6) = u * v ^ 7 by ring]
  have a8 : v ^ 8 ≤ v * S ^ 7 := by
    have := mul_le_mul_of_nonneg_left (m 0 7 7 rfl) hv
    linarith [show v * (u ^ 0 * v ^ 7) = v ^ 8 by ring]
  unfold nsum
  nlinarith [a0, a1, a2, a3, a4u, a4v, a5, a6, a7, a8]

theorem non_sub_le {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huS : u ≤ S) (hvS : v ≤ S) :
    |u ^ 9 - v ^ 9| ≤ 9 / 2 * S ^ 7 * |u ^ 2 - v ^ 2| := by
  have e2 : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
  rw [nine_sub, e2, abs_mul, abs_mul, abs_of_nonneg (nsum_nonneg hu hv),
    abs_of_nonneg (by positivity : 0 ≤ u + v)]
  calc |u - v| * nsum u v ≤ |u - v| * (9 / 2 * S ^ 7 * (u + v)) :=
        mul_le_mul_of_nonneg_left (nsum_le hu hv huS hvS) (abs_nonneg _)
    _ = 9 / 2 * S ^ 7 * (|u - v| * (u + v)) := by ring

theorem sqrt_le_of {a TH S : ℝ} (ha : |a| ≤ TH) (hS0 : 0 ≤ S) (hTS : TH ≤ S ^ 2) :
    Real.sqrt a ≤ S := by
  calc Real.sqrt a ≤ Real.sqrt (S ^ 2) :=
        Real.sqrt_le_sqrt ((le_abs_self a).trans (ha.trans hTS))
    _ = S := Real.sqrt_sq hS0

/-- Lipschitz bound of θ ^ (9/2) on the slab |θ| ≤ TH ≤ S². -/
theorem g92_lip {a b TH S : ℝ} (ha : |a| ≤ TH) (hb : |b| ≤ TH) (hS0 : 0 ≤ S) (hTS : TH ≤ S ^ 2) :
    |g92 a - g92 b| ≤ 9 / 2 * S ^ 7 * |a - b| := by
  have h1 := non_sub_le (Real.sqrt_nonneg a) (Real.sqrt_nonneg b) (sqrt_le_of ha hS0 hTS)
    (sqrt_le_of hb hS0 hTS)
  rw [sq_sqrt_max, sq_sqrt_max] at h1
  unfold g92
  exact h1.trans (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs a b 0) (by positivity))

/-- `g92 x` is close to `y ^ 9` when `y ^ 2` is close to `x` and `y` is bounded away from zero. -/
theorem g92_close {x y c P η : ℝ} (hc : 0 < c) (hcy : c ≤ y) (hyP : y ≤ P)
    (hη : |y ^ 2 - x| ≤ η) (hηc : η < c ^ 2) :
    |g92 x - y ^ 9| ≤ η / c * (9 * (P ^ 2 + η) ^ 4) := by
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
  set M := P ^ 2 + η with hM
  have hyP2 : y ^ 2 ≤ P ^ 2 := by nlinarith
  have hyM : y ^ 2 ≤ M := by linarith
  have huM : u ^ 2 ≤ M := by have := (abs_le.1 hη).1; nlinarith
  have hM0 : 0 ≤ M := by positivity
  have huS : u ≤ Real.sqrt M := Real.le_sqrt_of_sq_le huM
  have hyS : y ≤ Real.sqrt M := Real.le_sqrt_of_sq_le hyM
  have hS8 : Real.sqrt M ^ 8 = M ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, Real.sq_sqrt hM0]
  have m : ∀ a b : ℕ, a + b = 8 → u ^ a * y ^ b ≤ M ^ 4 := fun a b hab =>
    hS8 ▸ pow_mul_pow_le hu0 hy0 huS hyS a b 8 hab
  have q0 := m 8 0 rfl
  have q1 := m 7 1 rfl
  have q2 := m 6 2 rfl
  have q3 := m 5 3 rfl
  have q4 := m 4 4 rfl
  have q5 := m 3 5 rfl
  have q6 := m 2 6 rfl
  have q7 := m 1 7 rfl
  have q8 := m 0 8 rfl
  simp only [pow_zero, pow_one, mul_one, one_mul] at q0 q1 q7 q8
  have hq : nsum u y ≤ 9 * M ^ 4 := by unfold nsum; linarith
  unfold g92
  rw [← hu, nine_sub, abs_mul, abs_of_nonneg (nsum_nonneg hu0 hy0)]
  exact mul_le_mul hd hq (nsum_nonneg hu0 hy0) (by positivity)

/-- The Lane–Emden field of index nine halves at time ξ for (θ, w φ). -/
noncomputable def leGw (w ξ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2 / w, -(2 / ξ * p.2) - w * g92 p.1)

theorem lip_slab92 {w ξ t0 TH K S : ℝ} (hw : 0 < w) (ht0 : 0 < t0) (hξ : t0 ≤ ξ)
    (hK1 : 1 ≤ w * K) (hS0 : 0 ≤ S) (hTS : TH ≤ S ^ 2) (hK : 2 / t0 + w * (9 / 2 * S ^ 7) ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (leGw w ξ) (slab TH) := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have hK0 : (0 : ℝ) ≤ K := by
    have : 0 ≤ 2 / t0 + w * (9 / 2 * S ^ 7) := by positivity
    linarith
  rw [Real.coe_toNNReal _ hK0]
  simp only [leGw, Prod.dist_eq, Real.dist_eq]
  set m := max |p.1 - q.1| |p.2 - q.2|
  have hd1 : |p.1 - q.1| ≤ m := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ m := le_max_right _ _
  have hm : 0 ≤ m := (abs_nonneg _).trans hd1
  have hξ0 : 0 < ξ := lt_of_lt_of_le ht0 hξ
  refine max_le ?_ ?_
  · rw [← sub_div, abs_div, abs_of_pos hw, div_le_iff₀ hw]
    calc |p.2 - q.2| ≤ m := hd2
      _ = 1 * m := (one_mul m).symm
      _ ≤ (w * K) * m := mul_le_mul_of_nonneg_right hK1 hm
      _ = K * m * w := by ring
  · have e : (-(2 / ξ * p.2) - w * g92 p.1) - (-(2 / ξ * q.2) - w * g92 q.1) =
        -(2 / ξ * (p.2 - q.2)) - w * (g92 p.1 - g92 q.1) := by ring
    rw [e]
    have c1 := g92_lip (TH := TH) hp hq hS0 hTS
    have c2 : |2 / ξ * (p.2 - q.2)| ≤ 2 / t0 * m := by
      rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) ht0 hξ) hd2 (abs_nonneg _)
        (by positivity)
    have c3 : |w * (g92 p.1 - g92 q.1)| ≤ w * (9 / 2 * S ^ 7) * m := by
      rw [abs_mul, abs_of_pos hw, mul_assoc]
      exact mul_le_mul_of_nonneg_left (c1.trans (mul_le_mul_of_nonneg_left hd1 (by positivity)))
        hw.le
    calc |-(2 / ξ * (p.2 - q.2)) - w * (g92 p.1 - g92 q.1)|
        ≤ |2 / ξ * (p.2 - q.2)| + |w * (g92 p.1 - g92 q.1)| := by
          rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
      _ ≤ 2 / t0 * m + w * (9 / 2 * S ^ 7) * m := by linarith
      _ = (2 / t0 + w * (9 / 2 * S ^ 7)) * m := by ring
      _ ≤ K * m := mul_le_mul_of_nonneg_right hK hm

/-- One validated step on the cell [t₀, t₀ + h] ⊆ (0, T] for every solution (θ, φ) of the
Lane–Emden system (derivatives within [0, T]), in the weighted norm max(|Δθ|, w |Δφ|). -/
theorem cell (pt pp : List ℚ) {θ φ : ℝ → ℝ} {w T t0 h δ ε B TH K S : ℝ} (hw : 0 < w)
    (ht0 : 0 < t0) (hT : t0 + h ≤ T) (hh : 0 < h) (hK1 : 1 ≤ w * K)
    (hS0 : 0 ≤ S) (hTS : TH ≤ S ^ 2) (hK : 2 / t0 + w * (9 / 2 * S ^ 7) ≤ K) (hKh : K * h < 1)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hθ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt θ (φ t) (Icc 0 T) t)
    (hφ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt φ (-(2 / t * φ t) - g92 (θ t)) (Icc 0 T) t)
    (ht1 : ∀ σ ∈ Icc 0 h, -(TH - 1 / 100) ≤ evalQ pt σ)
    (ht2 : ∀ σ ∈ Icc 0 h, evalQ pt σ ≤ TH - 1 / 100)
    (hd1 : ∀ σ ∈ Icc 0 h, |dEvalQ pt σ - evalQ pp σ| ≤ ε)
    (hd2 : ∀ σ ∈ Icc 0 h,
      w * |(t0 + σ) * dEvalQ pp σ + 2 * evalQ pp σ + (t0 + σ) * g92 (evalQ pt σ)| ≤ ε * t0)
    (h0 : |θ t0 - evalQ pt 0| ≤ δ) (h0' : w * |φ t0 - evalQ pp 0| ≤ δ)
    (hB : δ * (1 / (1 - K * h)) + ε / K * (1 / (1 - K * h) - 1) ≤ B)
    (hBM : B < 1 / 100) :
    ∀ t ∈ Icc t0 (t0 + h), |θ t - evalQ pt (t - t0)| ≤ B ∧ w * |φ t - evalQ pp (t - t0)| ≤ B := by
  have hK0 : (0 : ℝ) < K := by
    have : 0 < 2 / t0 + w * (9 / 2 * S ^ 7) := by positivity
    linarith
  have hT0 : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0.le hT
  have hs : ∀ t ∈ Icc t0 (t0 + h), t - t0 ∈ Icc 0 h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have habs : ∀ a : ℝ, |w * a| = w * |a| := fun a => by rw [abs_mul, abs_of_pos hw]
  set f : ℝ → ℝ × ℝ := fun t => (θ t, w * φ t) with hfdef
  set g : ℝ → ℝ × ℝ := fun t => (evalQ pt (t - t0), w * evalQ pp (t - t0)) with hg
  have hfd : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt f (leGw w t (f t)) (Icc 0 T) t := by
    intro t ht
    have e : leGw w t (f t) = (φ t, w * (-(2 / t * φ t) - g92 (θ t))) := by
      simp only [leGw, hfdef]
      ext
      · field_simp
      · ring
    rw [e]
    exact (hθ t ht).prodMk ((hφ t ht).const_mul w)
  have key := tube_cell_t (F := leGw w) (K := Real.toNNReal K) (S := slab TH) (f := f) (g := g)
    (g' := fun t => (dEvalQ pt (t - t0), w * dEvalQ pp (t - t0))) (a := t0) (b := t0 + h)
    (δ := δ) (ε := ε) (B := B) (B' := 1 / 100)
    (fun t ht => lip_slab92 hw ht0 ht.1 hK1 hS0 hTS hK) (by linarith)
    (fun t ht => ((hfd t ht).continuousWithinAt).mono hT0)
    (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht0], by linarith [ht.2]⟩))
    (((continuous_evalQ pt).comp (continuous_sub_right t0)).prodMk
      (continuous_const.mul ((continuous_evalQ pp).comp (continuous_sub_right t0)))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ pt (t - t0)).comp_sub_const t t0).prodMk
      (((hasDerivAt_evalQ pp (t - t0)).comp_sub_const t t0).const_mul w)).hasDerivWithinAt)
    (fun t ht => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      simp only [hg, leGw, Prod.dist_eq, Real.dist_eq]
      refine max_le ?_ ?_
      · have e1 : w * evalQ pp (t - t0) / w = evalQ pp (t - t0) := by field_simp
        rw [e1]; exact hd1 _ hσ
      · have h2 := hd2 _ hσ
        have et : t0 + (t - t0) = t := by ring
        rw [et] at h2
        have e : w * dEvalQ pp (t - t0) -
            (-(2 / t * (w * evalQ pp (t - t0))) - w * g92 (evalQ pt (t - t0))) =
            w * ((t * dEvalQ pp (t - t0) + 2 * evalQ pp (t - t0) +
              t * g92 (evalQ pt (t - t0))) / t) := by
          field_simp
          ring
        rw [e, habs, abs_div, abs_of_pos htpos, ← mul_div_assoc, div_le_iff₀ htpos]
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
      refine max_le h0 ?_
      rw [← mul_sub, habs]; exact h0')
    (fun t ht => by
      rw [Real.coe_toNNReal _ hK0.le]
      have := gronwallBound_le_cell (K := K) hδ hε hK0
        (show t - t0 ≤ h by linarith [ht.2]) hh hKh
      exact this.trans hB)
  intro t ht
  have h1 := key t ht
  simp only [hfdef, hg, Prod.dist_eq, Real.dist_eq] at h1
  refine ⟨(le_max_left _ _).trans h1, ?_⟩
  have := (le_max_right _ _).trans h1
  rwa [← mul_sub, habs] at this

end Work.Math.LE92Cell
