import Mathlib

/-!
# van der Waals coexistence at T = 0.7 T_c in reduced variables (run 2026-10-31T1428Z)

Reduced volume `x = v/b`, reduced pressure `π = p/P_c`. At `T = 0.7 T_c` the vdW isotherm is
`g x = (28/5)/(x−1) − 27/x²` and `ψ π x = (28/5) log(x−1) + 27/x − π x` is a primitive of
`g − π` on `x > 1` (minus the molar Gibbs energy up to constants). A Maxwell coexistence state is
`1 < x₁ < x₂` with `g x₁ = g x₂ = π` and `ψ π x₁ = ψ π x₂`.

Main result: `reduced_window`: every such state has `0.200455 ≤ π ≤ 0.200465`.
Route (referee report `runs/2026-10-31T1428Z/referee_coexistence.md`, item 7, adapted):
Rolle gives a third zero of `g − π` and two critical points of `g`, which are roots of
`q x = 14x³ − 135x² + 270x − 135`; these are localized in [1.49, 5.15] and [5.25, 23], so
`x₁` lies on the first decreasing branch and `x₂` on the last; comparison with rational
brackets of the roots at `π = 0.200455` and `0.200465` (certificate
`runs/2026-10-31T1428Z/scripts/cert.py`) and one logarithm bound per side close the window.
-/

namespace Work.Chemistry.CoexistenceReduced

open Real Set

/-- Reduced vdW isotherm at `T = 0.7 T_c`. -/
noncomputable def g (x : ℝ) : ℝ := 28 / 5 / (x - 1) - 27 / x ^ 2

/-- Primitive of `g − π` on `x > 1`. -/
noncomputable def ψ (p x : ℝ) : ℝ := 28 / 5 * Real.log (x - 1) + 27 / x - p * x

/-- Numerator of `g'`: `g' x = −2 q x / (5 x³ (x−1)²)`. -/
def q (x : ℝ) : ℝ := 14 * x ^ 3 - 135 * x ^ 2 + 270 * x - 135

lemma hasDerivAt_g {x : ℝ} (hx : 1 < x) :
    HasDerivAt g (-2 * q x / (5 * x ^ 3 * (x - 1) ^ 2)) x := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h0 : x ≠ 0 := by linarith
  have hA : HasDerivAt (fun y => 28 / 5 / (y - 1)) (-(28 / 5) / (x - 1) ^ 2) x := by
    have := ((hasDerivAt_id x).sub_const 1).inv h1
    have := this.const_mul (28 / 5)
    convert this using 1
    · ext y; simp [div_eq_mul_inv]
    · simp; ring
  have hB : HasDerivAt (fun y => 27 / y ^ 2) (-(54) / x ^ 3) x := by
    have := ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 h0)).const_mul 27
    convert this using 1
    · ext y; simp [div_eq_mul_inv]
    · field_simp; ring
  have := hA.sub hB
  convert this using 1
  · ext y; simp [g]
  · unfold q; field_simp; ring

lemma hasDerivAt_ψ (p : ℝ) {x : ℝ} (hx : 1 < x) : HasDerivAt (ψ p) (g x - p) x := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h0 : x ≠ 0 := by linarith
  have hL := ((hasDerivAt_id x).sub_const 1).log h1
  have hB : HasDerivAt (fun y => 27 / y) (-(27) / x ^ 2) x := by
    have := ((hasDerivAt_id x).inv h0).const_mul 27
    convert this using 1
    · ext y; simp [div_eq_mul_inv]
    · simp; field_simp
  have := ((hL.const_mul (28 / 5)).add hB).sub ((hasDerivAt_id x).const_mul p)
  convert this using 1
  · ext y; simp [ψ]
  · simp [g]; field_simp; ring

lemma continuousOn_g {s t : ℝ} (hs : 1 < s) : ContinuousOn g (Icc s t) := fun x hx =>
  (hasDerivAt_g (by linarith [hx.1] : 1 < x)).continuousAt.continuousWithinAt

lemma continuousOn_ψ (p : ℝ) {s t : ℝ} (hs : 1 < s) : ContinuousOn (ψ p) (Icc s t) := fun x hx =>
  (hasDerivAt_ψ p (by linarith [hx.1] : 1 < x)).continuousAt.continuousWithinAt

/-- Monotonicity of `ψ π` from the sign of `g − π`. -/
lemma ψ_mono {p s t : ℝ} (hs : 1 < s) (h : ∀ x ∈ Icc s t, p ≤ g x) : MonotoneOn (ψ p) (Icc s t) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t) (continuousOn_ψ p hs)
    (fun x hx => (hasDerivAt_ψ p (by linarith [(interior_subset hx : x ∈ Icc s t).1])).hasDerivWithinAt)
    (fun x hx => by linarith [h x (interior_subset hx)])

lemma ψ_anti {p s t : ℝ} (hs : 1 < s) (h : ∀ x ∈ Icc s t, g x ≤ p) : AntitoneOn (ψ p) (Icc s t) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t) (continuousOn_ψ p hs)
    (fun x hx => (hasDerivAt_ψ p (by linarith [(interior_subset hx : x ∈ Icc s t).1])).hasDerivWithinAt)
    (fun x hx => by linarith [h x (interior_subset hx)])

/-- `g` is antitone where `q ≥ 0`. -/
lemma g_anti {s t : ℝ} (hs : 1 < s) (h : ∀ x ∈ Icc s t, 0 ≤ q x) : AntitoneOn g (Icc s t) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t) (continuousOn_g hs)
    (fun x hx => (hasDerivAt_g (by linarith [(interior_subset hx : x ∈ Icc s t).1])).hasDerivWithinAt)
    (fun x hx => by
      have hx' : x ∈ Icc s t := interior_subset hx
      have h1 : 1 < x := by linarith [hx'.1]
      have := h x hx'
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · positivity)

/-! ## Roots of `q` (critical points of the isotherm) -/

lemma q_pos_low {x : ℝ} (h1 : 1 < x) (h2 : x ≤ 149 / 100) : 0 < q x := by
  unfold q; nlinarith [mul_pos (by linarith : (0:ℝ) < x - 1) (by linarith : (0:ℝ) < x - 1),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x - 1) (by linarith : (0:ℝ) ≤ x - 1))
      (by linarith : (0:ℝ) ≤ x - 1)]

lemma q_neg_gap {x : ℝ} (h1 : 515 / 100 ≤ x) (h2 : x ≤ 525 / 100) : q x < 0 := by
  unfold q; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 515 / 100) (by linarith : (0:ℝ) ≤ 525 / 100 - x)]

lemma q_pos_high {x : ℝ} (h1 : 23 ≤ x) : 0 < q x := by
  unfold q; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 23) (by linarith : (0:ℝ) ≤ x),
    mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x - 23) (by linarith : (0:ℝ) ≤ x)) (by linarith : (0:ℝ) ≤ x)]

/-- Divided difference of `q`. -/
def S (x y : ℝ) : ℝ := 14 * (x ^ 2 + x * y + y ^ 2) - 135 * (x + y) + 270

lemma q_sub (x y : ℝ) : q x - q y = (x - y) * S x y := by unfold q S; ring

lemma S_neg {x y : ℝ} (hx1 : 149 / 100 ≤ x) (hx2 : x ≤ 515 / 100) (hy1 : 149 / 100 ≤ y)
    (hy2 : y ≤ 515 / 100) : S x y < 0 := by
  unfold S
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 149 / 100) (by linarith : (0:ℝ) ≤ 515 / 100 - x),
    mul_nonneg (by linarith : (0:ℝ) ≤ y - 149 / 100) (by linarith : (0:ℝ) ≤ 515 / 100 - y),
    mul_nonneg (by linarith : (0:ℝ) ≤ x - 149 / 100) (by linarith : (0:ℝ) ≤ 515 / 100 - y),
    mul_nonneg (by linarith : (0:ℝ) ≤ y - 149 / 100) (by linarith : (0:ℝ) ≤ 515 / 100 - x)]

lemma S_pos {x y : ℝ} (hx : 525 / 100 ≤ x) (hy : 525 / 100 ≤ y) : 0 < S x y := by
  unfold S
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 525 / 100) (by linarith : (0:ℝ) ≤ y - 525 / 100),
    sq_nonneg (x - 525 / 100), sq_nonneg (y - 525 / 100)]

/-- Two roots `1 < η₁ < η₂` of `q` lie in `[1.49, 5.15]` and `[5.25, 23]`. -/
lemma roots_loc {η₁ η₂ : ℝ} (h1 : 1 < η₁) (h12 : η₁ < η₂) (hq1 : q η₁ = 0) (hq2 : q η₂ = 0) :
    149 / 100 ≤ η₁ ∧ η₁ ≤ 515 / 100 ∧ 525 / 100 ≤ η₂ ∧ η₂ < 23 := by
  have loc : ∀ η, 1 < η → q η = 0 → (149 / 100 ≤ η ∧ η ≤ 515 / 100) ∨ (525 / 100 ≤ η ∧ η < 23) := by
    intro η h hq
    by_cases a : η ≤ 149 / 100
    · linarith [q_pos_low h a]
    by_cases b : η ≤ 515 / 100
    · left; constructor <;> linarith
    by_cases c : η < 525 / 100
    · linarith [q_neg_gap (by linarith : 515 / 100 ≤ η) c.le]
    by_cases d : η < 23
    · right; constructor <;> linarith
    · linarith [q_pos_high (by linarith : 23 ≤ η)]
  have hS : S η₂ η₁ = 0 := by
    have := q_sub η₂ η₁
    rw [hq1, hq2, sub_zero] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · linarith
    · exact h
  rcases loc η₁ h1 hq1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases loc η₂ (by linarith) hq2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · linarith [S_neg b1 b2 a1 a2]
  · exact ⟨a1, a2, b1, b2⟩
  · linarith
  · linarith [S_pos b1 a1]

/-- `q ≥ 0` on `(1, η₁]`. -/
lemma q_nonneg_left {η₁ x : ℝ} (hη : 149 / 100 ≤ η₁) (hη' : η₁ ≤ 515 / 100) (hq : q η₁ = 0)
    (h1 : 1 < x) (hx : x ≤ η₁) : 0 ≤ q x := by
  by_cases a : x ≤ 149 / 100
  · exact (q_pos_low h1 a).le
  · have := q_sub x η₁
    rw [hq, sub_zero] at this
    rw [this]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (S_neg (by linarith) (by linarith) hη hη').le

/-- `q ≥ 0` on `[η₂, ∞)`. -/
lemma q_nonneg_right {η₂ x : ℝ} (hη : 525 / 100 ≤ η₂) (hq : q η₂ = 0) (hx : η₂ ≤ x) : 0 ≤ q x := by
  have := q_sub x η₂
  rw [hq, sub_zero] at this
  rw [this]
  exact mul_nonneg (by linarith) (S_pos (by linarith) hη).le

/-! ## Shape of a coexistence state (Rolle) -/

lemma critical_points {x₁ x₂ p : ℝ} (h1 : 1 < x₁) (h12 : x₁ < x₂) (hg1 : g x₁ = p) (hg2 : g x₂ = p)
    (hψ : ψ p x₁ = ψ p x₂) :
    ∃ η₁ η₂, x₁ < η₁ ∧ η₁ < η₂ ∧ η₂ < x₂ ∧ q η₁ = 0 ∧ q η₂ = 0 := by
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero h12 (continuousOn_ψ p h1) hψ
    (fun x hx => hasDerivAt_ψ p (by linarith [hx.1]))
  have hgξ : g ξ = p := by linarith
  have qz : ∀ η, 1 < η → -2 * q η / (5 * η ^ 3 * (η - 1) ^ 2) = 0 → q η = 0 := by
    intro η h hz
    rcases div_eq_zero_iff.1 hz with h' | h'
    · linarith
    · exfalso
      have : 0 < 5 * η ^ 3 * (η - 1) ^ 2 := by
        have : 0 < η - 1 := by linarith
        positivity
      linarith
  obtain ⟨η₁, hη₁, hz₁⟩ := exists_hasDerivAt_eq_zero hξ.1 (continuousOn_g h1) (by rw [hg1, hgξ])
    (fun x hx => hasDerivAt_g (by linarith [hx.1]))
  obtain ⟨η₂, hη₂, hz₂⟩ := exists_hasDerivAt_eq_zero hξ.2 (continuousOn_g (by linarith [hξ.1]))
    (by rw [hg2, hgξ]) (fun x hx => hasDerivAt_g (by linarith [hx.1, hξ.1]))
  exact ⟨η₁, η₂, hη₁.1, by linarith [hη₁.2, hη₂.1], hη₂.2,
    qz η₁ (by linarith [hη₁.1]) hz₁, qz η₂ (by linarith [hη₂.1, hξ.1]) hz₂⟩

/-! ## Numerical certificate (rational brackets; `runs/2026-10-31T1428Z/scripts/cert.py`) -/

lemma log_series (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    |(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + Real.log (1 - x)| ≤ x ^ (n + 1) / (1 - x) := by
  have := Real.abs_log_sub_add_sum_range_le (by rw [abs_of_nonneg h0]; exact h1) n
  rwa [abs_of_nonneg h0] at this

lemma log_Qlo : 4.022918 < Real.log (2343391 / 100000 - 1) - Real.log (70079 / 50000 - 1) := by
  rw [← Real.log_div (by norm_num) (by norm_num)]
  have e : (2343391 / 100000 - 1) / (70079 / 50000 - 1) = (2:ℝ) ^ 6 * (1 - 108907 / 856704) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series (108907 / 856704) (by norm_num) (by norm_num) 7
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have := Real.log_two_gt_d9
  norm_num
  linarith [h.1, h.2]

lemma log_Qhi : Real.log (146453 / 6250 - 1) - Real.log (1401579 / 1000000 - 1) < 4.022865 := by
  rw [← Real.log_div (by norm_num) (by norm_num)]
  have e : (146453 / 6250 - 1) / (1401579 / 1000000 - 1) = (2:ℝ) ^ 6 * (1 - 102143 / 803158) := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  have h := log_series (102143 / 803158) (by norm_num) (by norm_num) 7
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have := Real.log_two_lt_d9
  norm_num
  linarith [h.1, h.2]

lemma num_lo : 40091 / 200000 < g (1401579 / 1000000) ∧ g (70079 / 50000) < 40091 / 200000 ∧
    40091 / 200000 < g (2343391 / 100000) := by
  unfold g; norm_num

lemma num_hi : g (1401579 / 1000000) < 40093 / 200000 ∧ 40093 / 200000 < g (2343247 / 100000) ∧
    g (146453 / 6250) < 40093 / 200000 := by
  unfold g; norm_num

lemma K_lo : 0 < ψ (40091 / 200000) (2343391 / 100000) - ψ (40091 / 200000) (70079 / 50000)
    - (70079 / 50000 - 1401579 / 1000000) * (40091 / 200000 - g (70079 / 50000)) := by
  have h := log_Qlo
  unfold ψ g
  norm_num at h ⊢
  linarith

lemma K_hi : ψ (40093 / 200000) (146453 / 6250) - ψ (40093 / 200000) (1401579 / 1000000)
    + (146453 / 6250 - 2343247 / 100000) * (40093 / 200000 - g (146453 / 6250)) < 0 := by
  have h := log_Qhi
  unfold ψ g
  norm_num at h ⊢
  linarith

lemma ψ_shift (p p' x : ℝ) : ψ p x = ψ p' x + (p' - p) * x := by unfold ψ; ring

/-- **Window.** Every Maxwell coexistence state of the reduced vdW isotherm at `T = 0.7 T_c`
has reduced pressure in `[0.200455, 0.200465]`. -/
theorem reduced_window {x₁ x₂ p : ℝ} (h1 : 1 < x₁) (h12 : x₁ < x₂) (hg1 : g x₁ = p)
    (hg2 : g x₂ = p) (hψ : ψ p x₁ = ψ p x₂) : 40091 / 200000 ≤ p ∧ p ≤ 40093 / 200000 := by
  obtain ⟨η₁, η₂, hx1, h12', hx2, hq1, hq2⟩ := critical_points h1 h12 hg1 hg2 hψ
  obtain ⟨l1, l2, l3, l4⟩ := roots_loc (by linarith) h12' hq1 hq2
  have antiL : ∀ s t, 1 < s → t ≤ η₁ → AntitoneOn g (Icc s t) := fun s t hs ht =>
    g_anti hs (fun x hx => q_nonneg_left l1 l2 hq1 (by linarith [hx.1]) (by linarith [hx.2]))
  have antiR : ∀ s t, η₂ ≤ s → AntitoneOn g (Icc s t) := fun s t hs =>
    g_anti (by linarith) (fun x hx => q_nonneg_right l3 hq2 (by linarith [hx.1]))
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨ga1, gb1, ga3⟩ := num_lo
    have hxa1 : (1401579 / 1000000 : ℝ) ≤ x₁ := by
      by_contra h
      push Not at h
      have := antiL x₁ (1401579 / 1000000) h1 (by linarith) ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
      linarith
    have hxa3 : (2343391 / 100000 : ℝ) ≤ x₂ := by
      by_contra h
      push Not at h
      have := antiR x₂ (2343391 / 100000) hx2.le ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
      linarith
    have hA3 : ψ p (2343391 / 100000) ≤ ψ p x₂ :=
      ψ_mono (by norm_num) (fun y hy => by
        have := antiR (2343391 / 100000) x₂ (by linarith) hy ⟨hxa3, le_rfl⟩ hy.2
        linarith) ⟨le_rfl, hxa3⟩ ⟨hxa3, le_rfl⟩ hxa3
    have hB : ψ (40091 / 200000) x₁ ≤ ψ (40091 / 200000) (70079 / 50000)
        + (70079 / 50000 - 1401579 / 1000000) * (40091 / 200000 - g (70079 / 50000)) := by
      rcases le_or_gt x₁ (70079 / 50000) with h | h
      · have m := ψ_mono (p := g (70079 / 50000)) h1 (fun y hy =>
          antiL x₁ (70079 / 50000) h1 (by linarith) hy ⟨h, le_rfl⟩ hy.2) ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
        have e1 := ψ_shift (40091 / 200000) (g (70079 / 50000)) x₁
        have e2 := ψ_shift (40091 / 200000) (g (70079 / 50000)) (70079 / 50000)
        have := mul_le_mul_of_nonneg_left (by linarith : (70079 / 50000 : ℝ) - x₁ ≤ 70079 / 50000 - 1401579 / 1000000)
          (by linarith : (0:ℝ) ≤ 40091 / 200000 - g (70079 / 50000))
        nlinarith
      · have m := ψ_anti (p := 40091 / 200000) (by norm_num) (fun y hy => by
          have := antiL (70079 / 50000) x₁ (by norm_num) hx1.le ⟨le_rfl, h.le⟩ hy hy.1
          linarith) ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
        have : 0 ≤ (70079 / 50000 - 1401579 / 1000000 : ℝ) * (40091 / 200000 - g (70079 / 50000)) :=
          mul_nonneg (by norm_num) (by linarith)
        linarith
    have e1 := ψ_shift p (40091 / 200000) x₁
    have e2 := ψ_shift p (40091 / 200000) (2343391 / 100000)
    have hpos := mul_pos (sub_pos.2 hlt) (by linarith : (0:ℝ) < 2343391 / 100000 - x₁)
    have := K_lo
    nlinarith
  · by_contra hgt
    push Not at hgt
    obtain ⟨gb1, ga3, gb3⟩ := num_hi
    have hxb1 : x₁ ≤ 1401579 / 1000000 := by
      by_contra h
      push Not at h
      have := antiL (1401579 / 1000000) x₁ (by norm_num) hx1.le ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
      linarith
    have hxb3 : x₂ ≤ 146453 / 6250 := by
      by_contra h
      push Not at h
      have := antiR (146453 / 6250) x₂ (by linarith) ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
      linarith
    have hL : ψ p (1401579 / 1000000) ≤ ψ p x₁ :=
      ψ_anti h1 (fun y hy => by
        have := antiL x₁ (1401579 / 1000000) h1 (by linarith) ⟨le_rfl, hxb1⟩ hy hy.1
        linarith) ⟨le_rfl, hxb1⟩ ⟨hxb1, le_rfl⟩ hxb1
    have hR : ψ (40093 / 200000) x₂ ≤ ψ (40093 / 200000) (146453 / 6250)
        + (146453 / 6250 - 2343247 / 100000) * (40093 / 200000 - g (146453 / 6250)) := by
      have core : ∀ z, 2343247 / 100000 ≤ z → z ≤ 146453 / 6250 → η₂ ≤ z →
          ψ (40093 / 200000) z ≤ ψ (40093 / 200000) (146453 / 6250)
            + (146453 / 6250 - 2343247 / 100000) * (40093 / 200000 - g (146453 / 6250)) := by
        intro z hz1 hz2 hz3
        have m := ψ_mono (p := g (146453 / 6250)) (by linarith) (fun y hy =>
          antiR z (146453 / 6250) hz3 hy ⟨hz2, le_rfl⟩ hy.2) ⟨le_rfl, hz2⟩ ⟨hz2, le_rfl⟩ hz2
        have e1 := ψ_shift (40093 / 200000) (g (146453 / 6250)) z
        have e2 := ψ_shift (40093 / 200000) (g (146453 / 6250)) (146453 / 6250)
        have := mul_le_mul_of_nonneg_left (by linarith : (146453 / 6250 : ℝ) - z ≤ 146453 / 6250 - 2343247 / 100000)
          (by linarith : (0:ℝ) ≤ 40093 / 200000 - g (146453 / 6250))
        nlinarith
      rcases le_or_gt (2343247 / 100000) x₂ with h | h
      · exact core x₂ h hxb3 hx2.le
      · have m := ψ_mono (p := 40093 / 200000) (by linarith) (fun y hy => by
          have := antiR x₂ (2343247 / 100000) hx2.le hy ⟨h.le, le_rfl⟩ hy.2
          linarith) ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
        linarith [core (2343247 / 100000) le_rfl (by norm_num) (by linarith)]
    have e1 := ψ_shift p (40093 / 200000) x₂
    have e2 := ψ_shift p (40093 / 200000) (1401579 / 1000000)
    have hpos := mul_pos (sub_pos.2 hgt) (by linarith : (0:ℝ) < x₂ - 1401579 / 1000000)
    have := K_hi
    nlinarith

end Work.Chemistry.CoexistenceReduced
