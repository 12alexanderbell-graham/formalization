import Work.Quantum.FluxSeries
import Work.Quantum.GeomBound
import Work.Quantum.Wronskian
/-!
# H₂⁺ route step 1: the angular assembly (run 2026-11-26T2228Z)

Route of `runs/2026-11-26T1628Z/README.md`, step 1. The angular equation at its singular end, s = 1 − η
(η = 1 ↔ s = 0, η = 0 ↔ s = 1), is d/ds [s(2 − s) M′] + (k(1 − s)² − A) M = 0, i.e. `FluxSeries` with
w = (0, 2, −1), v = (k − A, −2k, k). The solution regular at s = 0 with M(0) = 1 is ∑ bₙ sⁿ, with
b₀ = 1, b₁ = (A − k)/2, 8 b₂ = (2 − k + A) b₁ + 2k and
2(n + 3)² bₙ₊₃ = ((n + 2)(n + 3) − k + A) bₙ₊₂ + 2k bₙ₊₁ − k bₙ (`ab`, `ab_rec`).

No numerics in this file. On the box |k| ≤ 3, |A − k| ≤ 3:
* `ab_le_pow`: |bₙ| ≤ (3/2)ⁿ (induction from the recurrence);
* `ab_geom`: |bₙ| ≤ (9/4)⁹ (2/3)ⁿ for every n (`GeomBound.geom_bound` from n = 6 on), uniform on the box, so
  the series and its derivative converge on (−5/4, 5/4) ∋ [0, 1] (`angular_ode`);
* `g_continuousOn`: g(k, A) = dM/ds at s = 1 (= −dM/dη at η = 0) is jointly continuous on the box
  (`continuousOn_tsum` with the dominating series C (n + 1) qⁿ⁺¹).
* `g_root_unique`: two roots A₁ < A₂ of g(k, ·) are impossible where M_{k,A₁}, M_{k,A₂} > 0 on (0, 1)
  (`Wronskian.wronskian_pos`, V₁ − V₂ = A₂ − A₁).
* `unique_root_continuous` (generic): a function continuous on [k₁, k₂] × [a, b], negative at a, positive at b and
  with at most one root in [a, b] for each k, has its root in (a, b) depending continuously on k.
* `angular_root`: the assembly. Given (from the certificate, route step 4) M_{k,A} > 0 on (0, 1) on the box
  [k₁, k₂] × [a, b] and g(k, a) < 0 < g(k, b) for every k, there is a continuous A(k) ∈ (a, b), the only root of
  g(k, ·) in [a, b], and M_{k,A(k)} solves the angular equation on (−5/4, 5/4) with M′(s = 1) = 0.
-/

namespace Work.Quantum.AngularAssembly
open Set Filter Topology
open Work.Quantum.PSeries Work.Quantum.FluxSeries

/-- Coefficients of the angular solution regular at s = 0 (η = 1), normalised by b₀ = 1. -/
noncomputable def ab (k A : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => (A - k) / 2
  | 2 => ((2 - k + A) * ((A - k) / 2) + 2 * k) / 8
  | n + 3 => ((((n : ℝ) + 2) * ((n : ℝ) + 3) - k + A) * ab k A (n + 2) + 2 * k * ab k A (n + 1)
      - k * ab k A n) / (2 * ((n : ℝ) + 3) ^ 2)

theorem ab_succ3 (k A : ℝ) (n : ℕ) : ab k A (n + 3) = ((((n : ℝ) + 2) * ((n : ℝ) + 3) - k + A) * ab k A (n + 2)
    + 2 * k * ab k A (n + 1) - k * ab k A n) / (2 * ((n : ℝ) + 3) ^ 2) := by
  rw [ab]

theorem ab_rec (k A : ℝ) : Rec 0 2 (-1) (k - A) (-2 * k) k (ab k A) where
  r0 := by simp only [ab]; ring
  r1 := by simp only [ab]; ring
  r n := by
    have h : (2 * ((n : ℝ) + 3) ^ 2) ≠ 0 := by positivity
    have e := ab_succ3 k A n
    rw [eq_div_iff h] at e
    have e2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    linear_combination e

/-- The box of the bounds. -/
def Box (k A : ℝ) : Prop := |k| ≤ 3 ∧ |A - k| ≤ 3

theorem ab_le_pow {k A : ℝ} (hb : Box k A) : ∀ n, |ab k A n| ≤ (3 / 2 : ℝ) ^ n := by
  obtain ⟨hk, hAk⟩ := hb
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [ab]
    | 1, _ =>
      simp only [ab, pow_one, abs_div]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    | 2, _ =>
      simp only [ab]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8), div_le_iff₀ (by norm_num)]
      have h1 : |(2 - k + A) * ((A - k) / 2)| ≤ 5 * (3 / 2) := by
        rw [abs_mul]
        have : |2 - k + A| ≤ 5 := by
          have := abs_add_le (2 : ℝ) (A - k)
          rw [show (2 : ℝ) - k + A = 2 + (A - k) by ring]
          calc |2 + (A - k)| ≤ |(2 : ℝ)| + |A - k| := abs_add_le _ _
            _ ≤ 5 := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
        have h2 : |(A - k) / 2| ≤ 3 / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
        calc |2 - k + A| * |(A - k) / 2| ≤ 5 * (3 / 2) := by
              apply mul_le_mul this h2 (abs_nonneg _) (by norm_num)
          _ = 5 * (3 / 2) := rfl
      have h3 : |2 * k| ≤ 6 := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      calc |(2 - k + A) * ((A - k) / 2) + 2 * k| ≤ |(2 - k + A) * ((A - k) / 2)| + |2 * k| := abs_add_le _ _
        _ ≤ (3 / 2) ^ 2 * 8 := by norm_num at h1 h3 ⊢; linarith
    | m + 3, ih =>
      have i2 := ih (m + 2) (by omega)
      have i1 := ih (m + 1) (by omega)
      have i0 := ih m (by omega)
      have hD : (0 : ℝ) < 2 * ((m : ℝ) + 3) ^ 2 := by positivity
      rw [ab_succ3, abs_div, abs_of_pos hD, div_le_iff₀ hD]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      set P : ℝ := (3 / 2) ^ m with hP
      have hP0 : 0 ≤ P := by positivity
      have hP1 : (3 / 2 : ℝ) ^ (m + 1) = 3 / 2 * P := by rw [pow_succ]; ring
      have hP2 : (3 / 2 : ℝ) ^ (m + 2) = 9 / 4 * P := by rw [pow_succ, pow_succ]; ring
      have hP3 : (3 / 2 : ℝ) ^ (m + 3) = 27 / 8 * P := by rw [pow_succ, pow_succ, pow_succ]; ring
      rw [hP1] at i1; rw [hP2] at i2; rw [hP3]
      have hc : |((m : ℝ) + 2) * ((m : ℝ) + 3) - k + A| ≤ ((m : ℝ) + 2) * ((m : ℝ) + 3) + 3 := by
        rw [show ((m : ℝ) + 2) * ((m : ℝ) + 3) - k + A = ((m : ℝ) + 2) * ((m : ℝ) + 3) + (A - k) by ring]
        calc _ ≤ |((m : ℝ) + 2) * ((m : ℝ) + 3)| + |A - k| := abs_add_le _ _
          _ ≤ _ := by rw [abs_of_nonneg (by positivity)]; linarith
      have t1 : |(((m : ℝ) + 2) * ((m : ℝ) + 3) - k + A) * ab k A (m + 2)|
          ≤ (((m : ℝ) + 2) * ((m : ℝ) + 3) + 3) * (9 / 4 * P) := by
        rw [abs_mul]; exact mul_le_mul hc i2 (abs_nonneg _) (by positivity)
      have t2 : |2 * k * ab k A (m + 1)| ≤ 6 * (3 / 2 * P) := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul (by linarith) i1 (abs_nonneg _) (by norm_num)
      have t3 : |k * ab k A m| ≤ 3 * P := by
        rw [abs_mul]; exact mul_le_mul hk i0 (abs_nonneg _) (by norm_num)
      calc |(((m : ℝ) + 2) * ((m : ℝ) + 3) - k + A) * ab k A (m + 2) + 2 * k * ab k A (m + 1)
              - k * ab k A m|
            ≤ |(((m : ℝ) + 2) * ((m : ℝ) + 3) - k + A) * ab k A (m + 2)| + |2 * k * ab k A (m + 1)|
              + |k * ab k A m| := by
              refine (abs_sub _ _).trans ?_
              gcongr
              exact abs_add_le _ _
        _ ≤ (((m : ℝ) + 2) * ((m : ℝ) + 3) + 3) * (9 / 4 * P) + 6 * (3 / 2 * P) + 3 * P := by linarith
        _ ≤ 27 / 8 * P * (2 * ((m : ℝ) + 3) ^ 2) := by
          have key : 9 / 4 * (((m : ℝ) + 2) * ((m : ℝ) + 3) + 3) + 12 ≤ 27 / 4 * ((m : ℝ) + 3) ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right key hP0
          nlinarith

/-- The constant of the uniform geometric bound. -/
noncomputable def CB : ℝ := (9 / 4) ^ 9

theorem ab_geom {k A : ℝ} (hb : Box k A) : ∀ n, |ab k A n| ≤ CB * (2 / 3 : ℝ) ^ n := by
  obtain ⟨hk, hAk⟩ := hb
  refine GeomBound.geom_bound (N := 6) (α := 103 / 200) (β := 3 / 100) (γ := 3 / 200) (δ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun n hn => ?_) (by norm_num)
    (fun j hj => ?_)
  · -- the recurrence, one step on
    have hD : (0 : ℝ) < 2 * (((n + 1 : ℕ) : ℝ) + 3) ^ 2 := by positivity
    have e := ab_succ3 k A (n + 1)
    rw [show n + 1 + 3 = n + 4 by ring, show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at e
    rw [e, abs_div, abs_of_pos hD, div_le_iff₀ hD]
    push_cast
    have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
    have hc : |((n : ℝ) + 1 + 2) * ((n : ℝ) + 1 + 3) - k + A| ≤ ((n : ℝ) + 3) * ((n : ℝ) + 4) + 3 := by
      rw [show ((n : ℝ) + 1 + 2) * ((n : ℝ) + 1 + 3) - k + A = ((n : ℝ) + 3) * ((n : ℝ) + 4) + (A - k) by ring]
      calc _ ≤ |((n : ℝ) + 3) * ((n : ℝ) + 4)| + |A - k| := abs_add_le _ _
        _ ≤ _ := by rw [abs_of_nonneg (by positivity)]; linarith
    have a3 := abs_nonneg (ab k A (n + 3))
    have a2 := abs_nonneg (ab k A (n + 2))
    have a1 := abs_nonneg (ab k A (n + 1))
    have t1 : |(((n : ℝ) + 1 + 2) * ((n : ℝ) + 1 + 3) - k + A) * ab k A (n + 3)|
        ≤ (((n : ℝ) + 3) * ((n : ℝ) + 4) + 3) * |ab k A (n + 3)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hc a3
    have t2 : |2 * k * ab k A (n + 2)| ≤ 6 * |ab k A (n + 2)| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_right (by linarith) a2
    have t3 : |k * ab k A (n + 1)| ≤ 3 * |ab k A (n + 1)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hk a1
    have hsum : |(((n : ℝ) + 1 + 2) * ((n : ℝ) + 1 + 3) - k + A) * ab k A (n + 3) + 2 * k * ab k A (n + 2)
          - k * ab k A (n + 1)| ≤ (((n : ℝ) + 3) * ((n : ℝ) + 4) + 3) * |ab k A (n + 3)|
          + 6 * |ab k A (n + 2)| + 3 * |ab k A (n + 1)| := by
      refine (abs_sub _ _).trans ?_
      have := abs_add_le ((((n : ℝ) + 1 + 2) * ((n : ℝ) + 1 + 3) - k + A) * ab k A (n + 3))
        (2 * k * ab k A (n + 2))
      linarith
    refine hsum.trans ?_
    have hsq : (100 : ℝ) ≤ ((n : ℝ) + 4) ^ 2 := by nlinarith
    have e1 : ((n : ℝ) + 3) * ((n : ℝ) + 4) + 3 ≤ 103 / 200 * (2 * ((n : ℝ) + 1 + 3) ^ 2) := by nlinarith
    have e2 : (6 : ℝ) ≤ 3 / 100 * (2 * ((n : ℝ) + 1 + 3) ^ 2) := by nlinarith
    have e3 : (3 : ℝ) ≤ 3 / 200 * (2 * ((n : ℝ) + 1 + 3) ^ 2) := by nlinarith
    have := mul_le_mul_of_nonneg_right e1 a3
    have := mul_le_mul_of_nonneg_right e2 a2
    have := mul_le_mul_of_nonneg_right e3 a1
    nlinarith
  · -- the start: (3/2)ʲ = (9/4)ʲ (2/3)ʲ ≤ (9/4)⁹ (2/3)ʲ for j ≤ 9
    refine (ab_le_pow ⟨hk, hAk⟩ j).trans ?_
    have : (3 / 2 : ℝ) ^ j = (9 / 4) ^ j * (2 / 3) ^ j := by rw [← mul_pow]; norm_num
    rw [this, CB]
    gcongr
    · norm_num

theorem CB_nonneg : 0 ≤ CB := by unfold CB; positivity

/-- The angular solution M(s) = ∑ bₙ sⁿ and its derivative dM/ds = ∑ (n + 1) bₙ₊₁ sⁿ. -/
noncomputable def M (k A s : ℝ) : ℝ := ∑' n, ab k A n * s ^ n
noncomputable def Ms (k A s : ℝ) : ℝ := ∑' n, d1 (ab k A) n * s ^ n

/-- g(k, A) = dM/ds at s = 1, i.e. −dM/dη at η = 0. -/
noncomputable def g (k A : ℝ) : ℝ := Ms k A 1

theorem angular_ode {k A : ℝ} (hb : Box k A) {s : ℝ} (hs : s ∈ Ioo (-(5 / 4 : ℝ)) (5 / 4)) :
    HasDerivAt (M k A) (Ms k A s) s ∧
    HasDerivAt (fun y => (0 + 2 * y + (-1) * y ^ 2) * Ms k A y)
      (-(((k - A) + (-2 * k) * s + k * s ^ 2) * M k A s)) s :=
  flux_hasDerivAt (ab_rec k A) (ab_geom hb) (by norm_num) (by norm_num) (by norm_num) hs

theorem ab_continuous (n : ℕ) : Continuous (fun p : ℝ × ℝ => ab p.1 p.2 n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp only [ab]; exact continuous_const
    | 1, _ => simp only [ab]; fun_prop
    | 2, _ => simp only [ab]; fun_prop
    | m + 3, ih =>
      have i2 := ih (m + 2) (by omega)
      have i1 := ih (m + 1) (by omega)
      have i0 := ih m (by omega)
      simp only [ab_succ3]
      fun_prop

theorem g_continuousOn : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) {p | Box p.1 p.2} := by
  have hu : Summable (fun n : ℕ => CB * (((n : ℝ) + 1) * (2 / 3 : ℝ) ^ (n + 1))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (2 / 3 : ℝ) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
    have h2 := (summable_nat_add_iff 1).mpr h1
    refine (h2.mul_left CB).congr (fun n => ?_)
    push_cast
    ring
  refine continuousOn_tsum (u := fun n : ℕ => CB * (((n : ℝ) + 1) * (2 / 3 : ℝ) ^ (n + 1)))
    (fun n => ?_) hu (fun n p hp => ?_)
  · exact (((continuous_const.mul (ab_continuous (n + 1))).mul continuous_const)).continuousOn
  · simp only [d1, one_pow, mul_one, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    have := ab_geom hp (n + 1)
    calc ((n : ℝ) + 1) * |ab p.1 p.2 (n + 1)| ≤ ((n : ℝ) + 1) * (CB * (2 / 3) ^ (n + 1)) := by gcongr
      _ = _ := by ring

/-- At most one root of g(k, ·) between two values of A where both solutions are positive on (0, 1). -/
theorem g_root_unique {k A₁ A₂ : ℝ} (hb₁ : Box k A₁) (hb₂ : Box k A₂) (hlt : A₁ < A₂)
    (hp₁ : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < M k A₁ s) (hp₂ : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < M k A₂ s) :
    ¬ (g k A₁ = 0 ∧ g k A₂ = 0) := by
  rintro ⟨h₁, h₂⟩
  have hin : ∀ s ∈ Icc (0 : ℝ) 1, s ∈ Ioo (-(5 / 4 : ℝ)) (5 / 4) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hW := Wronskian.wronskian_pos (w := fun y => 0 + 2 * y + (-1) * y ^ 2)
    (V₁ := fun s => (k - A₁) + (-2 * k) * s + k * s ^ 2) (V₂ := fun s => (k - A₂) + (-2 * k) * s + k * s ^ 2)
    (M₁ := M k A₁) (M₂ := M k A₂) (D₁ := Ms k A₁) (D₂ := Ms k A₂)
    (fun s hs => (angular_ode hb₁ (hin s hs)).1) (fun s hs => (angular_ode hb₂ (hin s hs)).1)
    (fun s hs => (angular_ode hb₁ (hin s hs)).2) (fun s hs => (angular_ode hb₂ (hin s hs)).2)
    (by norm_num) (fun s hs => by
      have := mul_pos (hp₁ s hs) (hp₂ s hs)
      have e : ((k - A₁) + (-2 * k) * s + k * s ^ 2 - ((k - A₂) + (-2 * k) * s + k * s ^ 2)) * M k A₁ s
          * M k A₂ s = (A₂ - A₁) * (M k A₁ s * M k A₂ s) := by ring
      rw [e]; exact mul_pos (by linarith) this)
  unfold g at h₁ h₂
  rw [h₁, h₂] at hW
  simp at hW

/-- Generic: the unique root of a function continuous on a box, negative on the bottom edge and positive on the
top edge, depends continuously on the parameter. -/
theorem unique_root_continuous {G : ℝ → ℝ → ℝ} {k₁ k₂ a b : ℝ} (hab : a ≤ b)
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Icc k₁ k₂ ×ˢ Icc a b))
    (hlo : ∀ k ∈ Icc k₁ k₂, G k a < 0) (hhi : ∀ k ∈ Icc k₁ k₂, 0 < G k b)
    (huniq : ∀ k ∈ Icc k₁ k₂, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, G k x = 0 → G k y = 0 → x = y) :
    ∃ R : ℝ → ℝ, (∀ k ∈ Icc k₁ k₂, R k ∈ Ioo a b ∧ G k (R k) = 0) ∧ ContinuousOn R (Icc k₁ k₂) := by
  -- slices
  have hx : ∀ k ∈ Icc k₁ k₂, ContinuousOn (fun x => G k x) (Icc a b) := fun k hk =>
    hG.comp (continuousOn_const.prodMk continuousOn_id) (fun x hx => ⟨hk, hx⟩)
  have hk : ∀ x ∈ Icc a b, ContinuousOn (fun k => G k x) (Icc k₁ k₂) := fun x hx =>
    hG.comp (continuousOn_id.prodMk continuousOn_const) (fun k hk => ⟨hk, hx⟩)
  -- a root by the intermediate value theorem, on any [a, c] where G changes sign
  have ivt : ∀ k ∈ Icc k₁ k₂, ∀ c ∈ Icc a b, 0 ≤ G k c → ∃ y ∈ Icc a c, G k y = 0 := by
    intro k hk' c hc h0
    have hsub : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hc.2
    have := intermediate_value_Icc hc.1 ((hx k hk').mono hsub) ⟨(hlo k hk').le, h0⟩
    obtain ⟨y, hy, hy0⟩ := this
    exact ⟨y, hy, hy0⟩
  have hex : ∀ k ∈ Icc k₁ k₂, ∃ r, r ∈ Icc a b ∧ G k r = 0 := by
    intro k hk'
    obtain ⟨y, hy, hy0⟩ := ivt k hk' b ⟨hab, le_rfl⟩ (hhi k hk').le
    exact ⟨y, hy, hy0⟩
  classical
  let R : ℝ → ℝ := fun k => if h : k ∈ Icc k₁ k₂ then Classical.choose (hex k h) else a
  have hR : ∀ k ∈ Icc k₁ k₂, R k ∈ Icc a b ∧ G k (R k) = 0 := by
    intro k hk'
    simp only [R, hk', ↓reduceDIte]
    exact Classical.choose_spec (hex k hk')
  have hRo : ∀ k ∈ Icc k₁ k₂, R k ∈ Ioo a b := by
    intro k hk'
    obtain ⟨⟨h1, h2⟩, h0⟩ := hR k hk'
    refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩
    · intro e; have := hlo k hk'; rw [e] at this; linarith
    · intro e; have := hhi k hk'; rw [← e] at this; linarith
  -- sign below and above the root
  have below : ∀ k ∈ Icc k₁ k₂, ∀ x ∈ Icc a b, x < R k → G k x < 0 := by
    intro k hk' x hx' hlt
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy, hy0⟩ := ivt k hk' x hx' hcon
    have := huniq k hk' y ⟨hy.1, hy.2.trans hx'.2⟩ (R k) (hR k hk').1 hy0 (hR k hk').2
    linarith [hy.2]
  have above : ∀ k ∈ Icc k₁ k₂, ∀ x ∈ Icc a b, R k < x → 0 < G k x := by
    intro k hk' x hx' hlt
    by_contra hcon
    push Not at hcon
    rcases hcon.lt_or_eq with hneg | hzero
    · -- G k x < 0 and G k b > 0: a root in [x, b]
      have hsub : Icc x b ⊆ Icc a b := Icc_subset_Icc hx'.1 le_rfl
      obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hx'.2 ((hx k hk').mono hsub) ⟨hneg.le, (hhi k hk').le⟩
      have := huniq k hk' y (hsub hy) (R k) (hR k hk').1 hy0 (hR k hk').2
      linarith [hy.1]
    · have := huniq k hk' x hx' (R k) (hR k hk').1 hzero (hR k hk').2
      linarith
  refine ⟨R, fun k hk' => ⟨hRo k hk', (hR k hk').2⟩, fun k₀ hk₀ => ?_⟩
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  set xm := max a (R k₀ - ε / 2) with hxm
  set xp := min b (R k₀ + ε / 2) with hxp
  have hR0 := hRo k₀ hk₀
  have hxm_mem : xm ∈ Icc a b := ⟨le_max_left _ _, max_le hab (by linarith [hR0.2])⟩
  have hxp_mem : xp ∈ Icc a b := ⟨le_min hab (by linarith [hR0.1]), min_le_left _ _⟩
  have hxm_lt : xm < R k₀ := max_lt hR0.1 (by linarith)
  have hxp_gt : R k₀ < xp := lt_min hR0.2 (by linarith)
  have hneg := below k₀ hk₀ xm hxm_mem hxm_lt
  have hpos := above k₀ hk₀ xp hxp_mem hxp_gt
  have e1 : ∀ᶠ k in 𝓝[Icc k₁ k₂] k₀, G k xm < 0 :=
    (hk xm hxm_mem k₀ hk₀).eventually (gt_mem_nhds hneg)
  have e2 : ∀ᶠ k in 𝓝[Icc k₁ k₂] k₀, 0 < G k xp :=
    (hk xp hxp_mem k₀ hk₀).eventually (lt_mem_nhds hpos)
  filter_upwards [e1, e2, self_mem_nhdsWithin] with k hk1 hk2 hkmem
  have l : xm < R k := by
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with h | h
    · have := above k hkmem xm hxm_mem h; linarith
    · have := (hR k hkmem).2; rw [h] at this; linarith
  have u : R k < xp := by
    by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with h | h
    · have := below k hkmem xp hxp_mem h; linarith
    · have := (hR k hkmem).2; rw [← h] at this; linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : R k₀ - ε / 2 ≤ xm := le_max_right _ _
    linarith
  · have : xp ≤ R k₀ + ε / 2 := min_le_right _ _
    linarith

/-- **Route step 1, the angular assembly.** On a box [k₁, k₂] × [a, b] inside 0 ≤ k, A ≤ 3, given the two facts
the certificate supplies (route step 4) — the angular solution is positive on (0, 1) (i.e. on 0 < η < 1) for every
(k, A) in the box, and g(k, a) < 0 < g(k, b) for every k — there is A(k), continuous on [k₁, k₂], in (a, b), the
only root of g(k, ·) in [a, b], and M_{k,A(k)} solves the angular equation on (−5/4, 5/4) with M(0) = 1 and
dM/ds = 0 at s = 1 (η = 0). -/
theorem angular_root {k₁ k₂ a b : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : k₂ ≤ 3) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (hpos : ∀ k ∈ Icc k₁ k₂, ∀ A ∈ Icc a b, ∀ s ∈ Ioo (0 : ℝ) 1, 0 < M k A s)
    (hlo : ∀ k ∈ Icc k₁ k₂, g k a < 0) (hhi : ∀ k ∈ Icc k₁ k₂, 0 < g k b) :
    ∃ R : ℝ → ℝ, ContinuousOn R (Icc k₁ k₂) ∧ ∀ k ∈ Icc k₁ k₂, R k ∈ Ioo a b ∧ g k (R k) = 0 ∧
      (∀ A ∈ Icc a b, g k A = 0 → A = R k) ∧ M k (R k) 0 = 1 ∧
      ∀ s ∈ Ioo (-(5 / 4 : ℝ)) (5 / 4), HasDerivAt (M k (R k)) (Ms k (R k) s) s ∧
        HasDerivAt (fun y => (0 + 2 * y + (-1) * y ^ 2) * Ms k (R k) y)
          (-(((k - R k) + (-2 * k) * s + k * s ^ 2) * M k (R k) s)) s := by
  have hbox : ∀ k ∈ Icc k₁ k₂, ∀ A ∈ Icc a b, Box k A := by
    intro k hk A hA
    refine ⟨abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩,
      abs_le.mpr ⟨by linarith [hk.2, hA.1], by linarith [hk.1, hA.2]⟩⟩
  have hG : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc k₁ k₂ ×ˢ Icc a b) :=
    g_continuousOn.mono (fun p hp => hbox p.1 hp.1 p.2 hp.2)
  have huniq : ∀ k ∈ Icc k₁ k₂, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, g k x = 0 → g k y = 0 → x = y := by
    intro k hk x hx y hy h1 h2
    rcases lt_trichotomy x y with h | h | h
    · exact absurd ⟨h1, h2⟩ (g_root_unique (hbox k hk x hx) (hbox k hk y hy) h (hpos k hk x hx) (hpos k hk y hy))
    · exact h
    · exact absurd ⟨h2, h1⟩ (g_root_unique (hbox k hk y hy) (hbox k hk x hx) h (hpos k hk y hy) (hpos k hk x hx))
  obtain ⟨R, hR, hRc⟩ := unique_root_continuous hab hG hlo hhi huniq
  refine ⟨R, hRc, fun k hk => ⟨(hR k hk).1, (hR k hk).2, fun A hA h0 => ?_, ?_, fun s hs => ?_⟩⟩
  · exact huniq k hk A hA (R k) (Ioo_subset_Icc_self (hR k hk).1) h0 (hR k hk).2
  · unfold M
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    simp [ab]
  · exact angular_ode (hbox k hk (R k) (Ioo_subset_Icc_self (hR k hk).1)) hs

end Work.Quantum.AngularAssembly
