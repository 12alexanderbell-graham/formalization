import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Trust.ExpFlow
import Checked.Math.GCellQ

open Set

/-! Gelfand problem, `GContract`: contracting homology cells in log radius. In log radius the homology system is u′ = u (three − u − v), v′ = v (u − one); its right side is quadratic, so the difference of the field at two points is the Jacobian at their midpoint applied to their difference (`field_diff`). For the quadratic norm `Q` (the solution of the Lyapunov equation at the equilibrium) the form (P e) · J(m) e is affine in the midpoint m, so a bound by μ Q(e) on a box of midpoints follows from rational checks at its four corners (`box_bound`, `cornerOK`); with Grönwall's inequality this gives one cell (`ccell_q`) and a chain of cells decided as one Boolean (`chain_q`). Promoted from `Work/Math/GContract.lean` (run 2026-11-20T1628Z) by run 2026-11-21T0428Z. -/

namespace Checked.Math.GContract

noncomputable section

/-- First component of the homology field in log radius. -/
def F1 (u v : ℝ) : ℝ := u * (3 - u - v)
/-- Second component of the homology field in log radius. -/
def F2 (u v : ℝ) : ℝ := v * (u - 1)

/-- The field difference is the Jacobian at the midpoint applied to the difference (the field is quadratic). -/
theorem field_diff (u₁ v₁ u₂ v₂ : ℝ) :
    F1 u₁ v₁ - F1 u₂ v₂ =
        (3 - 2 * ((u₁ + u₂) / 2) - (v₁ + v₂) / 2) * (u₁ - u₂) - (u₁ + u₂) / 2 * (v₁ - v₂) ∧
    F2 u₁ v₁ - F2 u₂ v₂ = (v₁ + v₂) / 2 * (u₁ - u₂) + ((u₁ + u₂) / 2 - 1) * (v₁ - v₂) := by
  constructor <;> simp only [F1, F2] <;> ring

/-- The quadratic norm (squared) of the contracting cells. -/
def Q (e₁ e₂ : ℝ) : ℝ := 3 / 2 * e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2

/-- The form (P e) · J(a, b) e, with J(a, b) = [[3 − 2a − b, −a], [b, a − 1]] the Jacobian at (a, b). -/
def qf (a b e₁ e₂ : ℝ) : ℝ :=
  (3 / 2 * e₁ + 1 / 2 * e₂) * ((3 - 2 * a - b) * e₁ - a * e₂) +
    (1 / 2 * e₁ + e₂) * (b * e₁ + (a - 1) * e₂)

theorem Q_nonneg (e₁ e₂ : ℝ) : 0 ≤ Q e₁ e₂ := by
  unfold Q; nlinarith [sq_nonneg (e₁ + e₂), sq_nonneg e₁]

theorem Q_ge (e₁ e₂ : ℝ) : (e₁ ^ 2 + e₂ ^ 2) / 2 ≤ Q e₁ e₂ := by
  unfold Q; nlinarith [sq_nonneg (e₁ + e₂), sq_nonneg e₁]

/-- A symmetric two-by-two form with nonnegative diagonal and determinant is nonnegative. -/
theorem form_nonneg {p q r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hd : q ^ 2 ≤ p * r) (x y : ℝ) :
    0 ≤ p * x ^ 2 + 2 * q * x * y + r * y ^ 2 := by
  rcases hp.lt_or_eq with hp | hp
  · have h : p * (p * x ^ 2 + 2 * q * x * y + r * y ^ 2) = (p * x + q * y) ^ 2 + (p * r - q ^ 2) * y ^ 2 := by
      ring
    have h2 : 0 ≤ (p * x + q * y) ^ 2 + (p * r - q ^ 2) * y ^ 2 := by
      have := sq_nonneg y; have := sq_nonneg (p * x + q * y); nlinarith
    nlinarith
  · subst hp
    have hq : q = 0 := by nlinarith [sq_nonneg q]
    subst hq; nlinarith [sq_nonneg y]

/-- Entries of the symmetric matrix μP − sym(P J(a, b)). -/
def m11 (μ a b : ℝ) : ℝ := 3 / 2 * μ - (9 - 6 * a - 2 * b) / 2
def m12 (μ a b : ℝ) : ℝ := μ / 2 - (2 - 4 * a + b) / 4
def m22 (μ a b : ℝ) : ℝ := μ - (a - 2) / 2

theorem form_eq (μ a b e₁ e₂ : ℝ) :
    μ * Q e₁ e₂ - qf a b e₁ e₂ =
      m11 μ a b * e₁ ^ 2 + 2 * m12 μ a b * e₁ * e₂ + m22 μ a b * e₂ ^ 2 := by
  unfold Q qf m11 m12 m22; ring

/-- The corner check at one point: nonnegative diagonal and determinant of μP − sym(P J(a, b)). -/
def cornerOK (μ a b : ℝ) : Prop :=
  0 ≤ m11 μ a b ∧ 0 ≤ m22 μ a b ∧ m12 μ a b ^ 2 ≤ m11 μ a b * m22 μ a b

theorem corner_bound {μ a b : ℝ} (h : cornerOK μ a b) (e₁ e₂ : ℝ) : qf a b e₁ e₂ ≤ μ * Q e₁ e₂ := by
  have := form_nonneg h.1 h.2.1 h.2.2 e₁ e₂
  rw [← form_eq] at this; linarith

/-- An affine function of two variables that is nonpositive at the four corners of a box is nonpositive on it. -/
theorem affine_box {α β γ x₀ x₁ y₀ y₁ x y : ℝ} (hx : x₀ ≤ x ∧ x ≤ x₁) (hy : y₀ ≤ y ∧ y ≤ y₁)
    (h00 : α + β * x₀ + γ * y₀ ≤ 0) (h01 : α + β * x₀ + γ * y₁ ≤ 0)
    (h10 : α + β * x₁ + γ * y₀ ≤ 0) (h11 : α + β * x₁ + γ * y₁ ≤ 0) :
    α + β * x + γ * y ≤ 0 := by
  rcases le_total 0 β with hb | hb <;> rcases le_total 0 γ with hc | hc
  · nlinarith [mul_le_mul_of_nonneg_left hx.2 hb, mul_le_mul_of_nonneg_left hy.2 hc]
  · nlinarith [mul_le_mul_of_nonneg_left hx.2 hb, mul_le_mul_of_nonpos_left hy.1 hc]
  · nlinarith [mul_le_mul_of_nonpos_left hx.1 hb, mul_le_mul_of_nonneg_left hy.2 hc]
  · nlinarith [mul_le_mul_of_nonpos_left hx.1 hb, mul_le_mul_of_nonpos_left hy.1 hc]

/-- The form at a point of a box is bounded by μ Q when the corner check holds at the four corners. -/
theorem box_bound {μ a₀ a₁ b₀ b₁ a b : ℝ} (ha : a₀ ≤ a ∧ a ≤ a₁) (hb : b₀ ≤ b ∧ b ≤ b₁)
    (h00 : cornerOK μ a₀ b₀) (h01 : cornerOK μ a₀ b₁) (h10 : cornerOK μ a₁ b₀) (h11 : cornerOK μ a₁ b₁)
    (e₁ e₂ : ℝ) : qf a b e₁ e₂ ≤ μ * Q e₁ e₂ := by
  -- qf a b e - μ Q e is affine in (a, b)
  have aff : ∀ s t : ℝ, qf s t e₁ e₂ - μ * Q e₁ e₂ =
      (qf 0 0 e₁ e₂ - μ * Q e₁ e₂) + (qf 1 0 e₁ e₂ - qf 0 0 e₁ e₂) * s +
        (qf 0 1 e₁ e₂ - qf 0 0 e₁ e₂) * t := by
    intro s t; unfold qf; ring
  have k := fun s t (h : cornerOK μ s t) => (corner_bound h e₁ e₂)
  have := affine_box (α := qf 0 0 e₁ e₂ - μ * Q e₁ e₂) (β := qf 1 0 e₁ e₂ - qf 0 0 e₁ e₂)
    (γ := qf 0 1 e₁ e₂ - qf 0 0 e₁ e₂) ha hb
    (by rw [← aff]; linarith [k _ _ h00]) (by rw [← aff]; linarith [k _ _ h01])
    (by rw [← aff]; linarith [k _ _ h10]) (by rw [← aff]; linarith [k _ _ h11])
  rw [← aff] at this; linarith

/-- The rational corner check, decided by the kernel on a cell's box. -/
def cornerQ (μ a b : ℚ) : Prop :=
  0 ≤ 3 / 2 * μ - (9 - 6 * a - 2 * b) / 2 ∧ 0 ≤ μ - (a - 2) / 2 ∧
    (μ / 2 - (2 - 4 * a + b) / 4) ^ 2 ≤ (3 / 2 * μ - (9 - 6 * a - 2 * b) / 2) * (μ - (a - 2) / 2)

end

instance (μ a b : ℚ) : Decidable (cornerQ μ a b) := by unfold cornerQ; infer_instance

theorem cornerQ_real {μ a b : ℚ} (h : cornerQ μ a b) : cornerOK (μ : ℝ) (a : ℝ) (b : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := h
  have c1 := (Rat.cast_le (K := ℝ)).2 h1
  have c2 := (Rat.cast_le (K := ℝ)).2 h2
  have c3 := (Rat.cast_le (K := ℝ)).2 h3
  push_cast at c1 c2 c3
  refine ⟨?_, ?_, ?_⟩
  · unfold m11; linarith
  · unfold m22; linarith
  · unfold m11 m12 m22; linarith

/-- Check at the equilibrium (1, 2) with μ = −27/100 (the optimum there is (−5 + √5)/10 ≈ −0.2764). -/
example : cornerQ (-27 / 100) 1 2 := by decide +kernel

/-- A box around the equilibrium with the corner check at μ = −1/5. -/
example : cornerQ (-1 / 5) (99 / 100) (198 / 100) ∧ cornerQ (-1 / 5) (99 / 100) (202 / 100) ∧
    cornerQ (-1 / 5) (101 / 100) (198 / 100) ∧ cornerQ (-1 / 5) (101 / 100) (202 / 100) := by decide +kernel

/-- Cauchy–Schwarz for the form Q: twice the cross term is at most κ Q(e) + Q(d) / κ. -/
theorem cross_le {κ : ℝ} (hκ : 0 < κ) (e₁ e₂ d₁ d₂ : ℝ) :
    2 * ((3 / 2 * e₁ + 1 / 2 * e₂) * d₁ + (1 / 2 * e₁ + e₂) * d₂) ≤ κ * Q e₁ e₂ + Q d₁ d₂ / κ := by
  have h := Q_nonneg (κ * e₁ - d₁) (κ * e₂ - d₂)
  have hq : Q (κ * e₁ - d₁) (κ * e₂ - d₂) =
      κ ^ 2 * Q e₁ e₂ - 2 * κ * ((3 / 2 * e₁ + 1 / 2 * e₂) * d₁ + (1 / 2 * e₁ + e₂) * d₂) + Q d₁ d₂ := by
    unfold Q; ring
  rw [hq] at h
  have h2 := div_nonneg h hκ.le
  have e : (κ ^ 2 * Q e₁ e₂ - 2 * κ * ((3 / 2 * e₁ + 1 / 2 * e₂) * d₁ + (1 / 2 * e₁ + e₂) * d₂) + Q d₁ d₂) / κ =
      κ * Q e₁ e₂ - 2 * ((3 / 2 * e₁ + 1 / 2 * e₂) * d₁ + (1 / 2 * e₁ + e₂) * d₂) + Q d₁ d₂ / κ := by
    field_simp
  rw [e] at h2
  linarith

theorem Q_le_of_abs {η d₁ d₂ : ℝ} (h₁ : |d₁| ≤ η) (h₂ : |d₂| ≤ η) : Q d₁ d₂ ≤ 4 * η ^ 2 := by
  have a1 := abs_nonneg d₁
  have s1 : d₁ ^ 2 ≤ η ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ a1 h₁ 2
  have s2 : d₂ ^ 2 ≤ η ^ 2 := by rw [← sq_abs d₂]; exact pow_le_pow_left₀ (abs_nonneg _) h₂ 2
  have s3 : d₁ * d₂ ≤ η ^ 2 := by
    have : |d₁ * d₂| ≤ η * η := by rw [abs_mul]; exact mul_le_mul h₁ h₂ (abs_nonneg _) (a1.trans h₁)
    nlinarith [le_abs_self (d₁ * d₂)]
  unfold Q; nlinarith

/-- One contracting cell in log radius: a solution (u, v) of the homology field and an approximation (p, q)
whose defect is at most η in each component, with every midpoint in a box whose four corners pass the corner
check for μ, stay within the Grönwall bound with constant 2μ + κ in the quadratic norm Q. -/
theorem contract {a b μ κ η a₀ a₁ b₀ b₁ : ℝ} (hκ : 0 < κ) {u v p q p' q' : ℝ → ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (F1 (u t) (v t)) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (F2 (u t) (v t)) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (p' t) (Icc a b) t)
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (q' t) (Icc a b) t)
    (hdp : ∀ t ∈ Ico a b, |p' t - F1 (p t) (q t)| ≤ η)
    (hdq : ∀ t ∈ Ico a b, |q' t - F2 (p t) (q t)| ≤ η)
    (hbox : ∀ t ∈ Ico a b, (a₀ ≤ (u t + p t) / 2 ∧ (u t + p t) / 2 ≤ a₁) ∧
      (b₀ ≤ (v t + q t) / 2 ∧ (v t + q t) / 2 ≤ b₁))
    (h00 : cornerOK μ a₀ b₀) (h01 : cornerOK μ a₀ b₁) (h10 : cornerOK μ a₁ b₀) (h11 : cornerOK μ a₁ b₁) :
    ∀ t ∈ Icc a b, Q (u t - p t) (v t - q t) ≤
      gronwallBound (Q (u a - p a) (v a - q a)) (2 * μ + κ) (4 * η ^ 2 / κ) (t - a) := by
  set f : ℝ → ℝ := fun t => Q (u t - p t) (v t - q t) with hf
  set f' : ℝ → ℝ := fun t =>
    2 * ((3 / 2 * (u t - p t) + 1 / 2 * (v t - q t)) * (F1 (u t) (v t) - p' t) +
      (1 / 2 * (u t - p t) + (v t - q t)) * (F2 (u t) (v t) - q' t)) with hf'
  have hder : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t := by
    intro t ht
    have e1 := (hu t ht).sub (hp t ht)
    have e2 := (hv t ht).sub (hq t ht)
    have := ((((e1.pow 2).const_mul (3 / 2 : ℝ)).add (e1.mul e2)).add (e2.pow 2))
    convert this using 1
    · funext y; simp only [hf, Q, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    · rw [hf']; simp only [Pi.sub_apply]; push_cast; ring
  have hcont : ContinuousOn f (Icc a b) := fun t ht => (hder t ht).continuousWithinAt
  have hslope : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in nhdsWithin x (Ioi x), (z - x)⁻¹ * (f z - f x) < r := by
    intro x hx r hr
    have h1 : HasDerivWithinAt f (f' x) (Ici x) x :=
      (hder x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1))
    exact h1.liminf_right_slope_le hr
  have hbound : ∀ x ∈ Ico a b, f' x ≤ (2 * μ + κ) * f x + 4 * η ^ 2 / κ := by
    intro x hx
    obtain ⟨fd1, fd2⟩ := field_diff (u x) (v x) (p x) (q x)
    obtain ⟨ha, hb⟩ := hbox x hx
    have hqf := box_bound ha hb h00 h01 h10 h11 (u x - p x) (v x - q x)
    set d₁ := p' x - F1 (p x) (q x)
    set d₂ := q' x - F2 (p x) (q x)
    have hcr := cross_le hκ (u x - p x) (v x - q x) (-d₁) (-d₂)
    have hQd : Q (-d₁) (-d₂) ≤ 4 * η ^ 2 := Q_le_of_abs (by rw [abs_neg]; exact hdp x hx)
      (by rw [abs_neg]; exact hdq x hx)
    have hdiv : Q (-d₁) (-d₂) / κ ≤ 4 * η ^ 2 / κ := div_le_div_of_nonneg_right hQd hκ.le
    have key : f' x = 2 * qf ((u x + p x) / 2) ((v x + q x) / 2) (u x - p x) (v x - q x) +
        2 * ((3 / 2 * (u x - p x) + 1 / 2 * (v x - q x)) * (-d₁) +
          (1 / 2 * (u x - p x) + (v x - q x)) * (-d₂)) := by
      have r1 : F1 (u x) (v x) - p' x = (F1 (u x) (v x) - F1 (p x) (q x)) - d₁ := by simp only [d₁]; ring
      have r2 : F2 (u x) (v x) - q' x = (F2 (u x) (v x) - F2 (p x) (q x)) - d₂ := by simp only [d₂]; ring
      simp only [hf']
      rw [r1, r2, fd1, fd2]
      simp only [qf]; ring
    rw [key]
    simp only [hf]
    nlinarith
  intro t ht
  exact le_gronwallBound_of_liminf_deriv_right_le hcont hslope le_rfl hbound t ht

/-- A point within ρ of an inner box point moves the midpoint by at most ρ when Q of the error is below 2ρ². -/
theorem mid_in {ρ x y lo hi : ℝ} (hρ : 0 < ρ) (hy : lo + ρ ≤ y ∧ y ≤ hi - ρ) (e₂ : ℝ)
    (hQ : Q (x - y) e₂ ≤ 2 * ρ ^ 2) : lo ≤ (x + y) / 2 ∧ (x + y) / 2 ≤ hi := by
  have h1 := Q_ge (x - y) e₂
  have h2 : (x - y) ^ 2 ≤ (2 * ρ) ^ 2 := by nlinarith [sq_nonneg e₂]
  have h3 : |x - y| ≤ 2 * ρ := abs_le_of_sq_le_sq' h2 (by linarith) |> fun h => abs_le.2 h
  have := abs_le.1 h3
  constructor <;> linarith [hy.1, hy.2, this.1, this.2]

theorem mid_in' {ρ x y lo hi : ℝ} (hρ : 0 < ρ) (hy : lo + ρ ≤ y ∧ y ≤ hi - ρ) (e₁ : ℝ)
    (hQ : Q e₁ (x - y) ≤ 2 * ρ ^ 2) : lo ≤ (x + y) / 2 ∧ (x + y) / 2 ≤ hi := by
  have h1 := Q_ge e₁ (x - y)
  have h2 : (x - y) ^ 2 ≤ (2 * ρ) ^ 2 := by nlinarith [sq_nonneg e₁]
  have h3 : |x - y| ≤ 2 * ρ := abs_le_of_sq_le_sq' h2 (by linarith) |> fun h => abs_le.2 h
  have := abs_le.1 h3
  constructor <;> linarith [hy.1, hy.2, this.1, this.2]

/-- The contracting cell with its a-priori box: if the approximation stays at distance ρ inside the box and the
Grönwall bound stays below 2ρ², the solution's midpoints never leave the box and the bound holds on the cell. -/
theorem contract_boot {a b μ κ η ρ a₀ a₁ b₀ b₁ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) {u v p q p' q' : ℝ → ℝ}
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (F1 (u t) (v t)) (Icc a b) t)
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (F2 (u t) (v t)) (Icc a b) t)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (p' t) (Icc a b) t)
    (hq : ∀ t ∈ Icc a b, HasDerivWithinAt q (q' t) (Icc a b) t)
    (hdp : ∀ t ∈ Ico a b, |p' t - F1 (p t) (q t)| ≤ η)
    (hdq : ∀ t ∈ Ico a b, |q' t - F2 (p t) (q t)| ≤ η)
    (hpin : ∀ t ∈ Icc a b, (a₀ + ρ ≤ p t ∧ p t ≤ a₁ - ρ) ∧ (b₀ + ρ ≤ q t ∧ q t ≤ b₁ - ρ))
    (hG : ∀ t ∈ Icc a b,
      gronwallBound (Q (u a - p a) (v a - q a)) (2 * μ + κ) (4 * η ^ 2 / κ) (t - a) < 2 * ρ ^ 2)
    (h00 : cornerOK μ a₀ b₀) (h01 : cornerOK μ a₀ b₁) (h10 : cornerOK μ a₁ b₀) (h11 : cornerOK μ a₁ b₁) :
    ∀ t ∈ Icc a b, Q (u t - p t) (v t - q t) ≤
      gronwallBound (Q (u a - p a) (v a - q a)) (2 * μ + κ) (4 * η ^ 2 / κ) (t - a) := by
  have hab : ∀ c ∈ Icc a b, Icc a c ⊆ Icc a b := fun c hc => Icc_subset_Icc_right hc.2
  -- the bound on a sub-cell [a, c] once the midpoints stay in the box before c
  have sub : ∀ c ∈ Icc a b, (∀ s ∈ Ico a c, Q (u s - p s) (v s - q s) ≤ 2 * ρ ^ 2) →
      ∀ t ∈ Icc a c, Q (u t - p t) (v t - q t) ≤
        gronwallBound (Q (u a - p a) (v a - q a)) (2 * μ + κ) (4 * η ^ 2 / κ) (t - a) := by
    intro c hc hs
    refine contract (a₀ := a₀) (a₁ := a₁) (b₀ := b₀) (b₁ := b₁) hκ
      (fun t ht => (hu t (hab c hc ht)).mono (hab c hc)) (fun t ht => (hv t (hab c hc ht)).mono (hab c hc))
      (fun t ht => (hp t (hab c hc ht)).mono (hab c hc)) (fun t ht => (hq t (hab c hc ht)).mono (hab c hc))
      (fun t ht => hdp t ⟨ht.1, lt_of_lt_of_le ht.2 hc.2⟩)
      (fun t ht => hdq t ⟨ht.1, lt_of_lt_of_le ht.2 hc.2⟩) ?_ h00 h01 h10 h11
    intro t ht
    have htb : t ∈ Icc a b := ⟨ht.1, (le_of_lt ht.2).trans hc.2⟩
    exact ⟨mid_in hρ (hpin t htb).1 _ (hs t ht), mid_in' hρ (hpin t htb).2 _ (hs t ht)⟩
  have hcont : ContinuousOn (fun t => 2 * ρ ^ 2 - Q (u t - p t) (v t - q t)) (Icc a b) := by
    intro t ht
    have e1 := ((hu t ht).continuousWithinAt.sub (hp t ht).continuousWithinAt)
    have e2 := ((hv t ht).continuousWithinAt.sub (hq t ht).continuousWithinAt)
    exact continuousWithinAt_const.sub
      ((((e1.pow 2).const_smul (3 / 2 : ℝ)).add (e1.mul e2)).add (e2.pow 2) |>.congr
        (fun y _ => by simp [Q, smul_eq_mul]) (by simp [Q, smul_eq_mul]))
  have hpos : ∀ t ∈ Icc a b, 0 < 2 * ρ ^ 2 - Q (u t - p t) (v t - q t) := by
    by_cases hab' : a ≤ b
    · refine Checked.Trust.ExpFlow.cont_ind hcont ?_ ?_
      · have := hG a ⟨le_rfl, hab'⟩; rw [sub_self, gronwallBound_x0] at this; linarith
      · intro t ht hs
        have := sub t ⟨ht.1.le, ht.2⟩ (fun s hs' => by linarith [hs s hs']) t ⟨ht.1.le, le_rfl⟩
        linarith [hG t ⟨ht.1.le, ht.2⟩]
    · intro t ht; exact absurd (ht.1.trans ht.2) hab'
  intro t ht
  exact sub b ⟨ht.1.trans ht.2, le_rfl⟩ (fun s hs => by linarith [hpos s ⟨hs.1, hs.2.le⟩]) t ht

/-- With a negative constant the Grönwall bound stays below the larger of its start and ε / (−K). -/
theorem gb_le_max {δ K ε x : ℝ} (hK : K < 0) (hx : 0 ≤ x) :
    gronwallBound δ K ε x ≤ max δ (ε / -K) := by
  rw [gronwallBound_of_K_ne_0 hK.ne]
  beta_reduce
  have hE0 : 0 < Real.exp (K * x) := Real.exp_pos _
  have hE1 : Real.exp (K * x) ≤ 1 := Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hK.le hx)
  have e : δ * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1) =
      δ * Real.exp (K * x) + ε / -K * (1 - Real.exp (K * x)) := by
    rw [div_neg]; ring
  rw [e]
  have m1 := le_max_left δ (ε / -K)
  have m2 := le_max_right δ (ε / -K)
  nlinarith [mul_le_mul_of_nonneg_left m1 hE0.le, mul_le_mul_of_nonneg_left m2 (sub_nonneg.2 hE1)]

/-- The end value of the Grönwall bound with a negative constant, by e^{Kx} ≤ 1 / (1 − Kx). -/
theorem gb_end {δ K ε x : ℝ} (hK : K < 0) (hx : 0 ≤ x) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ δ / (1 - K * x) + ε / -K := by
  rw [gronwallBound_of_K_ne_0 hK.ne]
  beta_reduce
  have hKx : K * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK.le hx
  have hd : 0 < 1 - K * x := by linarith
  have hE0 : 0 < Real.exp (K * x) := Real.exp_pos _
  have hE : Real.exp (K * x) * (1 - K * x) ≤ 1 := by
    have h1 := Real.add_one_le_exp (-(K * x))
    have h2 : Real.exp (K * x) * Real.exp (-(K * x)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hE' : Real.exp (K * x) ≤ 1 / (1 - K * x) := by rw [le_div_iff₀ hd]; linarith
  have hc : 0 ≤ ε / -K := div_nonneg hε (by linarith)
  have e : ε / K * (Real.exp (K * x) - 1) = ε / -K * (1 - Real.exp (K * x)) := by rw [div_neg]; ring
  rw [e, div_eq_mul_one_div δ]
  nlinarith [mul_le_mul_of_nonneg_left hE' hδ, mul_nonneg hc hE0.le]

section CCell
open Checked.Sim Checked.Sim.QPoly Checked.Math.GCellQ

/-- A contracting cell in log radius: length `h`, start bound `δ` and end bound `B` of Q of the error, defect
bound `η`, constants `μ` (corner check) and `κ` (Cauchy–Schwarz split), inner margin `ρ`, box
`[a₀, a₁] × [b₀, b₁]` of midpoints, Taylor polynomials `pu`, `pv` in the offset from the cell's start. -/
structure CCell where
  h : ℚ
  δ : ℚ
  B : ℚ
  η : ℚ
  μ : ℚ
  κ : ℚ
  ρ : ℚ
  a₀ : ℚ
  a₁ : ℚ
  b₀ : ℚ
  b₁ : ℚ
  pu : List ℚ
  pv : List ℚ

/-- pu′ − pu (3 − pu − pv), computed. -/
def cdu (c : CCell) : List ℚ := qsub (qderiv c.pu) (qmul c.pu (qsub (qsub [3] c.pu) c.pv))
/-- pv′ − pv (pu − 1), computed. -/
def cdv (c : CCell) : List ℚ := qsub (qderiv c.pv) (qmul c.pv (qsub c.pu [1]))

/-- Every condition of a contracting cell, one proposition over the rationals. -/
def CCProp (c : CCell) : Prop :=
  0 < c.h ∧ 0 < c.κ ∧ 0 < c.ρ ∧ 0 ≤ c.δ ∧ 0 ≤ c.η ∧ 2 * c.μ + c.κ < 0 ∧
  qabs (cdu c) c.h ≤ c.η ∧ qabs (cdv c) c.h ≤ c.η ∧
  c.a₀ + c.ρ ≤ lo c.pu c.h ∧ hi c.pu c.h ≤ c.a₁ - c.ρ ∧
  c.b₀ + c.ρ ≤ lo c.pv c.h ∧ hi c.pv c.h ≤ c.b₁ - c.ρ ∧
  c.δ < 2 * c.ρ ^ 2 ∧ 4 * c.η ^ 2 / c.κ / -(2 * c.μ + c.κ) < 2 * c.ρ ^ 2 ∧
  c.δ / (1 - (2 * c.μ + c.κ) * c.h) + 4 * c.η ^ 2 / c.κ / -(2 * c.μ + c.κ) ≤ c.B ∧
  cornerQ c.μ c.a₀ c.b₀ ∧ cornerQ c.μ c.a₀ c.b₁ ∧ cornerQ c.μ c.a₁ c.b₀ ∧ cornerQ c.μ c.a₁ c.b₁

instance (c : CCell) : Decidable (CCProp c) := by unfold CCProp; infer_instance

/-- One contracting cell from its Boolean check: every solution of the homology field in log radius whose
error against the cell's polynomials has Q at most `δ` at the start has Q of the error at most `B` at the end
(and below 2ρ² on the whole cell). -/
theorem ccell_q (c : CCell) (hok : decide (CCProp c) = true) {τ₀ : ℝ} {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc τ₀ (τ₀ + c.h), HasDerivWithinAt u (F1 (u t) (v t)) (Icc τ₀ (τ₀ + c.h)) t)
    (hv : ∀ t ∈ Icc τ₀ (τ₀ + c.h), HasDerivWithinAt v (F2 (u t) (v t)) (Icc τ₀ (τ₀ + c.h)) t)
    (h0 : Q (u τ₀ - evalQ c.pu 0) (v τ₀ - evalQ c.pv 0) ≤ c.δ) :
    Q (u (τ₀ + c.h) - evalQ c.pu c.h) (v (τ₀ + c.h) - evalQ c.pv c.h) ≤ c.B := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18⟩ :
    CCProp c := of_decide_eq_true hok
  have r : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => by exact_mod_cast h
  have rl : ∀ {a b : ℚ}, a < b → (a : ℝ) < (b : ℝ) := fun h => by exact_mod_cast h
  have hh := rl k0; have hκ := rl k1; have hρ := rl k2; have hδ := r k3; have hη := r k4
  have hK := rl k5; have r6 := r k6; have r7 := r k7; have r8 := r k8; have r9 := r k9
  have r10 := r k10; have r11 := r k11; have r12 := rl k12; have r13 := rl k13; have r14 := r k14
  push_cast at hh hκ hρ hδ hη hK r12 r13 r14
  set p : ℝ → ℝ := fun t => evalQ c.pu (t - τ₀) with hp
  set q : ℝ → ℝ := fun t => evalQ c.pv (t - τ₀) with hq
  have hs : ∀ t ∈ Icc τ₀ (τ₀ + c.h), (0 : ℝ) ≤ t - τ₀ ∧ t - τ₀ ≤ c.h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have dp : ∀ t ∈ Icc τ₀ (τ₀ + c.h),
      HasDerivWithinAt p (evalQ (qderiv c.pu) (t - τ₀)) (Icc τ₀ (τ₀ + c.h)) t := by
    intro t _
    have := (hasDerivAt_evalQ c.pu (t - τ₀)).comp t ((hasDerivAt_id t).sub_const τ₀)
    rw [dEvalQ_eq, mul_one] at this; exact this.hasDerivWithinAt
  have dq : ∀ t ∈ Icc τ₀ (τ₀ + c.h),
      HasDerivWithinAt q (evalQ (qderiv c.pv) (t - τ₀)) (Icc τ₀ (τ₀ + c.h)) t := by
    intro t _
    have := (hasDerivAt_evalQ c.pv (t - τ₀)).comp t ((hasDerivAt_id t).sub_const τ₀)
    rw [dEvalQ_eq, mul_one] at this; exact this.hasDerivWithinAt
  have ddu : ∀ t ∈ Ico τ₀ (τ₀ + c.h), |evalQ (qderiv c.pu) (t - τ₀) - F1 (p t) (q t)| ≤ c.η := by
    intro t ht
    have e : evalQ (qderiv c.pu) (t - τ₀) - F1 (p t) (q t) = evalQ (cdu c) (t - τ₀) := by
      simp only [cdu, evalQ_qsub, evalQ_qmul, F1, hp, hq]; simp [evalQ]
    rw [e]
    have hs' := hs t (Ico_subset_Icc_self ht)
    exact (abs_le_qabs _ hs'.1 hs'.2).trans r6
  have ddv : ∀ t ∈ Ico τ₀ (τ₀ + c.h), |evalQ (qderiv c.pv) (t - τ₀) - F2 (p t) (q t)| ≤ c.η := by
    intro t ht
    have e : evalQ (qderiv c.pv) (t - τ₀) - F2 (p t) (q t) = evalQ (cdv c) (t - τ₀) := by
      simp only [cdv, evalQ_qsub, evalQ_qmul, F2, hp, hq]; simp [evalQ]
    rw [e]
    have hs' := hs t (Ico_subset_Icc_self ht)
    exact (abs_le_qabs _ hs'.1 hs'.2).trans r7
  have hpin : ∀ t ∈ Icc τ₀ (τ₀ + c.h), ((c.a₀ : ℝ) + c.ρ ≤ p t ∧ p t ≤ (c.a₁ : ℝ) - c.ρ) ∧
      ((c.b₀ : ℝ) + c.ρ ≤ q t ∧ q t ≤ (c.b₁ : ℝ) - c.ρ) := by
    intro t ht
    obtain ⟨s0, s1⟩ := hs t ht
    have l1 := lo_le c.pu s0 s1; have u1 := le_hi c.pu s0 s1
    have l2 := lo_le c.pv s0 s1; have u2 := le_hi c.pv s0 s1
    push_cast at r8 r9 r10 r11
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  set K : ℝ := 2 * c.μ + c.κ
  set C : ℝ := 4 * (c.η : ℝ) ^ 2 / c.κ
  have hδ0 : Q (u τ₀ - p τ₀) (v τ₀ - q τ₀) ≤ c.δ := by simpa [hp, hq] using h0
  have hQ0 := Q_nonneg (u τ₀ - p τ₀) (v τ₀ - q τ₀)
  have hC : 0 ≤ C := by positivity
  have hG : ∀ t ∈ Icc τ₀ (τ₀ + c.h),
      gronwallBound (Q (u τ₀ - p τ₀) (v τ₀ - q τ₀)) K C (t - τ₀) < 2 * (c.ρ : ℝ) ^ 2 := by
    intro t ht
    have := gb_le_max (δ := Q (u τ₀ - p τ₀) (v τ₀ - q τ₀)) (ε := C) hK (hs t ht).1
    refine lt_of_le_of_lt this (max_lt (by linarith) ?_)
    simpa [C, K] using r13
  have main := contract_boot (a₀ := c.a₀) (a₁ := c.a₁) (b₀ := c.b₀) (b₁ := c.b₁) (μ := c.μ) hκ hρ hu hv dp dq
    ddu ddv hpin hG (cornerQ_real k15) (cornerQ_real k16) (cornerQ_real k17) (cornerQ_real k18)
    (τ₀ + c.h) ⟨by linarith, le_rfl⟩
  have hend := gb_end (δ := Q (u τ₀ - p τ₀) (v τ₀ - q τ₀)) (ε := C) hK (by linarith : (0 : ℝ) ≤ τ₀ + c.h - τ₀)
    hQ0 hC
  have hd : 0 < 1 - K * (τ₀ + c.h - τ₀) := by
    have : K * (τ₀ + c.h - τ₀) < 0 := mul_neg_of_neg_of_pos hK (by linarith)
    linarith
  have hmono : Q (u τ₀ - p τ₀) (v τ₀ - q τ₀) / (1 - K * (τ₀ + c.h - τ₀)) ≤
      (c.δ : ℝ) / (1 - K * (τ₀ + c.h - τ₀)) := div_le_div_of_nonneg_right hδ0 hd.le
  have e2 : τ₀ + c.h - τ₀ = (c.h : ℝ) := by ring
  rw [e2] at hmono
  have fin : (c.δ : ℝ) / (1 - K * c.h) + C / -K ≤ c.B := by simpa [C, K] using r14
  have main' : Q (u (τ₀ + c.h) - p (τ₀ + c.h)) (v (τ₀ + c.h) - q (τ₀ + c.h)) ≤
      gronwallBound (Q (u τ₀ - p τ₀) (v τ₀ - q τ₀)) K C c.h := by
    rw [e2] at main; exact main
  have : Q (u (τ₀ + c.h) - p (τ₀ + c.h)) (v (τ₀ + c.h) - q (τ₀ + c.h)) ≤ c.B := by
    rw [e2] at hend; linarith
  simpa [hp, hq] using this

/-- A cell on the equilibrium solution (constant polynomials, defect zero): Q of the error shrinks from 10⁻⁶ to
below 97 · 10⁻⁸ over a log-radius length of one tenth. -/
example : decide (CCProp ⟨1 / 10, 1 / 1000000, 97 / 100000000, 0, -1 / 5, 1 / 100, 1 / 200,
    99 / 100, 101 / 100, 198 / 100, 202 / 100, [1], [2]⟩) = true := by decide +kernel

end CCell

/-- Linking two cells: Q of a sum is at most (1 + θ) Q of the first part plus (1 + 1/θ) Q of the second
(the rounding of the next cell's start). -/
theorem Q_add_le {θ : ℝ} (hθ : 0 < θ) (a₁ a₂ b₁ b₂ : ℝ) :
    Q (a₁ + b₁) (a₂ + b₂) ≤ (1 + θ) * Q a₁ a₂ + (1 + 1 / θ) * Q b₁ b₂ := by
  have h := cross_le hθ a₁ a₂ b₁ b₂
  have e : Q (a₁ + b₁) (a₂ + b₂) =
      Q a₁ a₂ + 2 * ((3 / 2 * a₁ + 1 / 2 * a₂) * b₁ + (1 / 2 * a₁ + a₂) * b₂) + Q b₁ b₂ := by
    unfold Q; ring
  rw [e]
  have : Q b₁ b₂ / θ = 1 / θ * Q b₁ b₂ := by ring
  nlinarith

section Chain
open Checked.Sim Checked.Sim.QPoly

/-- Q over the rationals. -/
def Qq (e₁ e₂ : ℚ) : ℚ := 3 / 2 * e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2

/-- The link from cell `c` to the next cell `d` (θ = 1/1000): `d`'s start bound covers `c`'s end bound and the
rounding of `d`'s start values against `c`'s polynomials at its end. -/
def LinkProp (c d : CCell) : Prop :=
  (1 + 1 / 1000) * c.B + (1 + 1000) * Qq (d.pu.headD 0 - qeval c.pu c.h) (d.pv.headD 0 - qeval c.pv c.h) ≤ d.δ

instance (c d : CCell) : Decidable (LinkProp c d) := by unfold LinkProp; infer_instance

/-- Total log-radius length of a list of cells. -/
def totalH : List CCell → ℚ
  | [] => 0
  | c :: cs => c.h + totalH cs

/-- A chain of contracting cells, checked as one Boolean: every cell and every link. -/
def chainOK : List CCell → Bool
  | [] => true
  | [c] => decide (CCProp c)
  | c :: d :: cs => decide (CCProp c) && decide (LinkProp c d) && chainOK (d :: cs)

/-- The last cell of a nonempty chain. -/
def lastC : List CCell → CCell → CCell
  | [], c => c
  | d :: cs, _ => lastC cs d

theorem evalQ_headD (p : List ℚ) : evalQ p 0 = ((p.headD 0 : ℚ) : ℝ) := by
  cases p <;> simp [evalQ]

theorem Qq_cast (a b : ℚ) : ((Qq a b : ℚ) : ℝ) = Q a b := by unfold Qq Q; push_cast; ring

theorem totalH_nonneg : ∀ cs : List CCell, chainOK cs = true → 0 ≤ totalH cs
  | [], _ => by simp [totalH]
  | [c], h => by
      have := (of_decide_eq_true (by simpa [chainOK] using h) : CCProp c).1
      simp [totalH]; linarith
  | c :: d :: cs, h => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
      have := totalH_nonneg (d :: cs) h.2
      have := h.1.1.1
      show (0 : ℚ) ≤ c.h + totalH (d :: cs); linarith

/-- A chain of contracting cells: every solution of the homology field in log radius on the chain's range
whose error against the first cell has Q at most its `δ` has Q of the error at most the last cell's `B` at the
end of the chain. -/
theorem chain_q : ∀ (cs : List CCell) (c : CCell), chainOK (c :: cs) = true → ∀ {τ₀ : ℝ} {u v : ℝ → ℝ},
    (∀ t ∈ Icc τ₀ (τ₀ + totalH (c :: cs)),
      HasDerivWithinAt u (F1 (u t) (v t)) (Icc τ₀ (τ₀ + totalH (c :: cs))) t) →
    (∀ t ∈ Icc τ₀ (τ₀ + totalH (c :: cs)),
      HasDerivWithinAt v (F2 (u t) (v t)) (Icc τ₀ (τ₀ + totalH (c :: cs))) t) →
    Q (u τ₀ - evalQ c.pu 0) (v τ₀ - evalQ c.pv 0) ≤ c.δ →
    Q (u (τ₀ + totalH (c :: cs)) - evalQ (lastC cs c).pu (lastC cs c).h)
      (v (τ₀ + totalH (c :: cs)) - evalQ (lastC cs c).pv (lastC cs c).h) ≤ (lastC cs c).B
  | [], c, hok, τ₀, u, v, hu, hv, h0 => by
      have e : ((totalH [c] : ℚ) : ℝ) = (c.h : ℝ) := by simp [totalH]
      rw [e] at hu hv ⊢
      exact ccell_q c (by simpa [chainOK] using hok) hu hv h0
  | d :: ds, c, hok, τ₀, u, v, hu, hv, h0 => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hc, hl⟩, hrest⟩ := hok
      unfold LinkProp at hl
      have hT : ((totalH (c :: d :: ds) : ℚ) : ℝ) = (c.h : ℝ) + ((totalH (d :: ds) : ℚ) : ℝ) := by
        simp only [totalH]; push_cast; ring
      have hnn : (0 : ℝ) ≤ ((totalH (d :: ds) : ℚ) : ℝ) := by exact_mod_cast totalH_nonneg _ hrest
      have hh : (0 : ℝ) < c.h := by exact_mod_cast hc.1
      rw [hT] at hu hv ⊢
      have sub1 : Icc τ₀ (τ₀ + (c.h : ℝ)) ⊆ Icc τ₀ (τ₀ + ((c.h : ℝ) + totalH (d :: ds))) :=
        Icc_subset_Icc_right (by linarith)
      have sub2 : Icc (τ₀ + c.h) (τ₀ + c.h + ((totalH (d :: ds) : ℚ) : ℝ)) ⊆
          Icc τ₀ (τ₀ + ((c.h : ℝ) + totalH (d :: ds))) :=
        Icc_subset_Icc (by linarith) (by linarith)
      have end1 := ccell_q c (by simpa using hc) (τ₀ := τ₀)
        (fun t ht => (hu t (sub1 ht)).mono sub1) (fun t ht => (hv t (sub1 ht)).mono sub1) h0
      have link : Q (u (τ₀ + c.h) - evalQ d.pu 0) (v (τ₀ + c.h) - evalQ d.pv 0) ≤ d.δ := by
        have hq := Q_add_le (θ := 1 / 1000) (by norm_num)
          (u (τ₀ + c.h) - evalQ c.pu c.h) (v (τ₀ + c.h) - evalQ c.pv c.h)
          (evalQ c.pu c.h - evalQ d.pu 0) (evalQ c.pv c.h - evalQ d.pv 0)
        have hL : ((1 + 1 / 1000 : ℚ) : ℝ) * c.B +
            ((1 + 1000 : ℚ) : ℝ) * ((Qq (d.pu.headD 0 - qeval c.pu c.h) (d.pv.headD 0 - qeval c.pv c.h) : ℚ) : ℝ)
            ≤ d.δ := by exact_mod_cast hl
        rw [Qq_cast] at hL
        have hr : Q (evalQ c.pu c.h - evalQ d.pu 0) (evalQ c.pv c.h - evalQ d.pv 0) =
            Q (((d.pu.headD 0 - qeval c.pu c.h : ℚ) : ℝ)) (((d.pv.headD 0 - qeval c.pv c.h : ℚ) : ℝ)) := by
          rw [evalQ_headD, evalQ_headD]; push_cast; rw [qeval_cast, qeval_cast]; unfold Q; ring
        have e1 : u (τ₀ + c.h) - evalQ c.pu c.h + (evalQ c.pu c.h - evalQ d.pu 0) =
            u (τ₀ + c.h) - evalQ d.pu 0 := by ring
        have e2 : v (τ₀ + c.h) - evalQ c.pv c.h + (evalQ c.pv c.h - evalQ d.pv 0) =
            v (τ₀ + c.h) - evalQ d.pv 0 := by ring
        rw [e1, e2, hr] at hq
        have hQr := Q_nonneg (((d.pu.headD 0 - qeval c.pu c.h : ℚ) : ℝ)) (((d.pv.headD 0 - qeval c.pv c.h : ℚ) : ℝ))
        push_cast at hL hq
        nlinarith
      have ih := chain_q ds d (by simpa using hrest) (τ₀ := τ₀ + c.h)
        (fun t ht => (hu t (sub2 ht)).mono sub2) (fun t ht => (hv t (sub2 ht)).mono sub2) link
      have e3 : τ₀ + c.h + ((totalH (d :: ds) : ℚ) : ℝ) = τ₀ + ((c.h : ℝ) + totalH (d :: ds)) := by ring
      rw [e3] at ih
      simpa [lastC] using ih

end Chain

end Checked.Math.GContract
