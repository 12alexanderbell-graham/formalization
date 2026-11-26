import Work.Quantum.FluxSeries
import Work.Quantum.GeomBound
/-!
# Frobenius solutions at a regular singular end, with parameters (run 2026-11-26T2228Z)

H₂⁺ route (`runs/2026-11-26T1628Z/README.md`, section Route), the pieces at the singular ends: the equation
((2s + w₂ s²) M′)′ + (v₀ + v₁ s + v₂ s²) M = 0 (`FluxSeries` with w₀ = 0, w₁ = 2) has the solution regular at s = 0
with M(0) = 1, ∑ cₙ sⁿ with c₀ = 1, c₁ = −v₀/2, 8c₂ = −(2w₂ + v₀)c₁ − v₁ and
2(n + 3)² cₙ₊₃ = −(w₂(n + 2)(n + 3) + v₀) cₙ₊₂ − v₁ cₙ₊₁ − v₂ cₙ (`fc`, `fc_rec`).
* angular end (s = 1 − η): w₂ = −1, v = (k − A, −2k, k);
* radial end (u = ξ − 1): w₂ = 1, v = (4 − k + A, 4 − 2k, −k).

No numerics. Under |w₂| ≤ 1 and |vᵢ| ≤ 8 (`Small`; for 0 ≤ k, A ≤ 3 both ends qualify):
* `fc_le_pow`: |cₙ| ≤ 8ⁿ; `fc_geom`: |cₙ| ≤ 12¹⁹ (2/3)ⁿ (`GeomBound.geom_bound` from n = 16 on), uniform;
* `fc_ode`: the series solves the equation on (−5/4, 5/4);
* `fc_continuous`, `sol_continuousOn`, `dsol_continuousOn`: for parameters depending continuously on a point x of
  any topological space, cₙ, M(x, s) and M′(x, s) (|s| ≤ 5/4 fixed) are continuous in x where `Small` holds.
-/

namespace Work.Quantum.FrobParam
open Set Filter Topology
open Work.Quantum.PSeries Work.Quantum.FluxSeries

/-- Coefficients of the solution regular at s = 0, c₀ = 1. -/
noncomputable def fc (w₂ v₀ v₁ v₂ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -v₀ / 2
  | 2 => (-(2 * w₂ + v₀) * (-v₀ / 2) - v₁) / 8
  | n + 3 => (-(w₂ * ((n : ℝ) + 2) * ((n : ℝ) + 3) + v₀) * fc w₂ v₀ v₁ v₂ (n + 2)
      - v₁ * fc w₂ v₀ v₁ v₂ (n + 1) - v₂ * fc w₂ v₀ v₁ v₂ n) / (2 * ((n : ℝ) + 3) ^ 2)

variable {w₂ v₀ v₁ v₂ : ℝ}

theorem fc_succ3 (w₂ v₀ v₁ v₂ : ℝ) (n : ℕ) : fc w₂ v₀ v₁ v₂ (n + 3) =
    (-(w₂ * ((n : ℝ) + 2) * ((n : ℝ) + 3) + v₀) * fc w₂ v₀ v₁ v₂ (n + 2)
      - v₁ * fc w₂ v₀ v₁ v₂ (n + 1) - v₂ * fc w₂ v₀ v₁ v₂ n) / (2 * ((n : ℝ) + 3) ^ 2) := by
  rw [fc]

theorem fc_rec (w₂ v₀ v₁ v₂ : ℝ) : Rec 0 2 w₂ v₀ v₁ v₂ (fc w₂ v₀ v₁ v₂) where
  r0 := by simp only [fc]; ring
  r1 := by simp only [fc]; ring
  r n := by
    have h : (2 * ((n : ℝ) + 3) ^ 2) ≠ 0 := by positivity
    have e := fc_succ3 w₂ v₀ v₁ v₂ n
    rw [eq_div_iff h] at e
    linear_combination e

/-- The parameter range of the uniform bounds. -/
def Small (w₂ v₀ v₁ v₂ : ℝ) : Prop := |w₂| ≤ 1 ∧ |v₀| ≤ 8 ∧ |v₁| ≤ 8 ∧ |v₂| ≤ 8

/-- One step of the recurrence in absolute values. -/
theorem fc_step (hs : Small w₂ v₀ v₁ v₂) (n : ℕ) :
    |fc w₂ v₀ v₁ v₂ (n + 3)| * (2 * ((n : ℝ) + 3) ^ 2) ≤
      (((n : ℝ) + 2) * ((n : ℝ) + 3) + 8) * |fc w₂ v₀ v₁ v₂ (n + 2)| + 8 * |fc w₂ v₀ v₁ v₂ (n + 1)|
        + 8 * |fc w₂ v₀ v₁ v₂ n| := by
  obtain ⟨hw, h0, h1, h2⟩ := hs
  have hD : (0 : ℝ) < 2 * ((n : ℝ) + 3) ^ 2 := by positivity
  rw [fc_succ3, abs_div, abs_of_pos hD, div_mul_cancel₀ _ hD.ne']
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : |-(w₂ * ((n : ℝ) + 2) * ((n : ℝ) + 3) + v₀)| ≤ ((n : ℝ) + 2) * ((n : ℝ) + 3) + 8 := by
    rw [abs_neg]
    calc _ ≤ |w₂ * ((n : ℝ) + 2) * ((n : ℝ) + 3)| + |v₀| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 3)]
        have : |w₂| * ((n : ℝ) + 2) * ((n : ℝ) + 3) ≤ 1 * ((n : ℝ) + 2) * ((n : ℝ) + 3) := by gcongr
        linarith
  set a := fc w₂ v₀ v₁ v₂ (n + 2)
  set b := fc w₂ v₀ v₁ v₂ (n + 1)
  set c := fc w₂ v₀ v₁ v₂ n
  have t1 : |-(w₂ * ((n : ℝ) + 2) * ((n : ℝ) + 3) + v₀) * a| ≤ (((n : ℝ) + 2) * ((n : ℝ) + 3) + 8) * |a| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have t2 : |v₁ * b| ≤ 8 * |b| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have t3 : |v₂ * c| ≤ 8 * |c| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have := abs_sub (-(w₂ * ((n : ℝ) + 2) * ((n : ℝ) + 3) + v₀) * a - v₁ * b) (v₂ * c)
  have := abs_sub (-(w₂ * ((n : ℝ) + 2) * ((n : ℝ) + 3) + v₀) * a) (v₁ * b)
  linarith

theorem fc_le_pow (hs : Small w₂ v₀ v₁ v₂) : ∀ n, |fc w₂ v₀ v₁ v₂ n| ≤ (8 : ℝ) ^ n := by
  have hs' := hs
  obtain ⟨hw, h0, h1, h2⟩ := hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [fc]
    | 1, _ =>
      simp only [fc, pow_one, abs_div, abs_neg]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg v₀]
    | 2, _ =>
      simp only [fc]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8), div_le_iff₀ (by norm_num)]
      have e1 : |2 * w₂ + v₀| ≤ 10 := by
        calc _ ≤ |2 * w₂| + |v₀| := abs_add_le _ _
          _ ≤ 10 := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      have e2 : |-v₀ / 2| ≤ 4 := by
        rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      have e3 : |-(2 * w₂ + v₀) * (-v₀ / 2)| ≤ 10 * 4 := by
        rw [abs_mul, abs_neg]; exact mul_le_mul e1 e2 (abs_nonneg _) (by norm_num)
      have := abs_sub (-(2 * w₂ + v₀) * (-v₀ / 2)) v₁
      rw [show (8 : ℝ) ^ 2 * 8 = 512 by norm_num]
      linarith
    | m + 3, ih =>
      have i2 := ih (m + 2) (by omega)
      have i1 := ih (m + 1) (by omega)
      have i0 := ih m (by omega)
      have st := fc_step hs' m
      have hD : (0 : ℝ) < 2 * ((m : ℝ) + 3) ^ 2 := by positivity
      set P : ℝ := (8 : ℝ) ^ m with hP
      have hP0 : 0 ≤ P := by positivity
      have hP1 : (8 : ℝ) ^ (m + 1) = 8 * P := by rw [pow_succ]; ring
      have hP2 : (8 : ℝ) ^ (m + 2) = 64 * P := by rw [pow_succ, pow_succ]; ring
      have hP3 : (8 : ℝ) ^ (m + 3) = 512 * P := by rw [pow_succ, pow_succ, pow_succ]; ring
      rw [hP1] at i1; rw [hP2] at i2; rw [hP3]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have key : (((m : ℝ) + 2) * ((m : ℝ) + 3) + 8) * 64 + 8 * 8 + 8 ≤ 512 * (2 * ((m : ℝ) + 3) ^ 2) := by
        nlinarith
      have b1 : (((m : ℝ) + 2) * ((m : ℝ) + 3) + 8) * |fc w₂ v₀ v₁ v₂ (m + 2)| ≤
          (((m : ℝ) + 2) * ((m : ℝ) + 3) + 8) * (64 * P) := by gcongr
      have : |fc w₂ v₀ v₁ v₂ (m + 3)| * (2 * ((m : ℝ) + 3) ^ 2) ≤ 512 * P * (2 * ((m : ℝ) + 3) ^ 2) := by
        have := mul_le_mul_of_nonneg_right key hP0
        nlinarith
      exact le_of_mul_le_mul_right this hD

/-- The constant of the uniform geometric bound. -/
noncomputable def CF : ℝ := 12 ^ 19

theorem CF_nonneg : 0 ≤ CF := by unfold CF; positivity

theorem fc_geom (hs : Small w₂ v₀ v₁ v₂) : ∀ n, |fc w₂ v₀ v₁ v₂ n| ≤ CF * (2 / 3 : ℝ) ^ n := by
  refine GeomBound.geom_bound (N := 16) (α := 51 / 100) (β := 1 / 100) (γ := 1 / 100) (δ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun n hn => ?_) (by norm_num)
    (fun j hj => ?_)
  · have st := fc_step hs (n + 1)
    rw [show n + 1 + 3 = n + 4 by ring, show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at st
    push_cast at st
    have hD : (0 : ℝ) < 2 * ((n : ℝ) + 1 + 3) ^ 2 := by positivity
    have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
    have a3 := abs_nonneg (fc w₂ v₀ v₁ v₂ (n + 3))
    have a2 := abs_nonneg (fc w₂ v₀ v₁ v₂ (n + 2))
    have a1 := abs_nonneg (fc w₂ v₀ v₁ v₂ (n + 1))
    have e1 : ((n : ℝ) + 1 + 2) * ((n : ℝ) + 1 + 3) + 8 ≤ 51 / 100 * (2 * ((n : ℝ) + 1 + 3) ^ 2) := by nlinarith
    have e2 : (8 : ℝ) ≤ 1 / 100 * (2 * ((n : ℝ) + 1 + 3) ^ 2) := by nlinarith
    have m1 := mul_le_mul_of_nonneg_right e1 a3
    have m2 := mul_le_mul_of_nonneg_right e2 a2
    have m3 := mul_le_mul_of_nonneg_right e2 a1
    have : |fc w₂ v₀ v₁ v₂ (n + 4)| * (2 * ((n : ℝ) + 1 + 3) ^ 2) ≤
        (51 / 100 * |fc w₂ v₀ v₁ v₂ (n + 3)| + 1 / 100 * |fc w₂ v₀ v₁ v₂ (n + 2)|
          + 1 / 100 * |fc w₂ v₀ v₁ v₂ (n + 1)| + 0 * |fc w₂ v₀ v₁ v₂ n|) * (2 * ((n : ℝ) + 1 + 3) ^ 2) := by
      nlinarith
    exact le_of_mul_le_mul_right this hD
  · refine (fc_le_pow hs j).trans ?_
    have : (8 : ℝ) ^ j = 12 ^ j * (2 / 3) ^ j := by rw [← mul_pow]; norm_num
    rw [this, CF]
    gcongr
    · norm_num

/-- The solution and its derivative as power series. -/
noncomputable def sol (w₂ v₀ v₁ v₂ s : ℝ) : ℝ := ∑' n, fc w₂ v₀ v₁ v₂ n * s ^ n
noncomputable def dsol (w₂ v₀ v₁ v₂ s : ℝ) : ℝ := ∑' n, d1 (fc w₂ v₀ v₁ v₂) n * s ^ n

theorem fc_ode (hs : Small w₂ v₀ v₁ v₂) {s : ℝ} (hs' : s ∈ Ioo (-(5 / 4 : ℝ)) (5 / 4)) :
    HasDerivAt (sol w₂ v₀ v₁ v₂) (dsol w₂ v₀ v₁ v₂ s) s ∧
    HasDerivAt (fun y => (0 + 2 * y + w₂ * y ^ 2) * dsol w₂ v₀ v₁ v₂ y)
      (-((v₀ + v₁ * s + v₂ * s ^ 2) * sol w₂ v₀ v₁ v₂ s)) s :=
  flux_hasDerivAt (fc_rec w₂ v₀ v₁ v₂) (fc_geom hs) (by norm_num) (by norm_num) (by norm_num) hs'

theorem sol_zero (w₂ v₀ v₁ v₂ : ℝ) : sol w₂ v₀ v₁ v₂ 0 = 1 := by
  unfold sol
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp [fc]

section Continuity
variable {X : Type*} [TopologicalSpace X] {W V0 V1 V2 : X → ℝ}

theorem fc_continuous (hW : Continuous W) (h0 : Continuous V0) (h1 : Continuous V1) (h2 : Continuous V2)
    (n : ℕ) : Continuous (fun x => fc (W x) (V0 x) (V1 x) (V2 x) n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp only [fc]; exact continuous_const
    | 1, _ => simp only [fc]; fun_prop
    | 2, _ => simp only [fc]; fun_prop
    | m + 3, ih =>
      have i2 := ih (m + 2) (by omega)
      have i1 := ih (m + 1) (by omega)
      have i0 := ih m (by omega)
      simp only [fc_succ3]
      fun_prop

theorem sol_continuousOn (hW : Continuous W) (h0 : Continuous V0) (h1 : Continuous V1) (h2 : Continuous V2)
    {S : Set X} (hS : ∀ x ∈ S, Small (W x) (V0 x) (V1 x) (V2 x)) {s : ℝ} (hs : |s| ≤ 5 / 4) :
    ContinuousOn (fun x => sol (W x) (V0 x) (V1 x) (V2 x) s) S := by
  have hu : Summable (fun n : ℕ => CF * (5 / 6 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left CF
  refine continuousOn_tsum (u := fun n : ℕ => CF * (5 / 6 : ℝ) ^ n)
    (fun n => ((fc_continuous hW h0 h1 h2 n).mul continuous_const).continuousOn) hu (fun n x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have hb := fc_geom (hS x hx) n
  have hC := CF_nonneg
  calc |fc (W x) (V0 x) (V1 x) (V2 x) n| * |s| ^ n ≤ CF * (2 / 3) ^ n * (5 / 4) ^ n := by
        gcongr
    _ = CF * (5 / 6) ^ n := by rw [mul_assoc, ← mul_pow]; norm_num

theorem dsol_continuousOn (hW : Continuous W) (h0 : Continuous V0) (h1 : Continuous V1) (h2 : Continuous V2)
    {S : Set X} (hS : ∀ x ∈ S, Small (W x) (V0 x) (V1 x) (V2 x)) {s : ℝ} (hs : |s| ≤ 5 / 4) :
    ContinuousOn (fun x => dsol (W x) (V0 x) (V1 x) (V2 x) s) S := by
  have hu : Summable (fun n : ℕ => CF * (2 / 3) * (((n : ℝ) + 1) * (5 / 6 : ℝ) ^ n)) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (5 / 6 : ℝ) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
    have h2 : Summable (fun n : ℕ => (5 / 6 : ℝ) ^ n) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine ((h1.add h2).mul_left (CF * (2 / 3))).congr (fun n => ?_)
    simp only [pow_one]
    ring
  refine continuousOn_tsum (u := fun n : ℕ => CF * (2 / 3) * (((n : ℝ) + 1) * (5 / 6 : ℝ) ^ n))
    (fun n => ?_) hu (fun n x hx => ?_)
  · simp only [d1]
    exact ((continuous_const.mul (fc_continuous hW h0 h1 h2 (n + 1))).mul continuous_const).continuousOn
  · simp only [d1, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1), abs_pow]
    have hb := fc_geom (hS x hx) (n + 1)
    have hC := CF_nonneg
    calc ((n : ℝ) + 1) * |fc (W x) (V0 x) (V1 x) (V2 x) (n + 1)| * |s| ^ n
          ≤ ((n : ℝ) + 1) * (CF * (2 / 3) ^ (n + 1)) * (5 / 4) ^ n := by gcongr
      _ = CF * (2 / 3) * (((n : ℝ) + 1) * (5 / 6 : ℝ) ^ n) := by
        rw [pow_succ, show (5 / 6 : ℝ) = 2 / 3 * (5 / 4) by norm_num, mul_pow]; ring

end Continuity

end Work.Quantum.FrobParam
