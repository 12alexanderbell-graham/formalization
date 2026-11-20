import Mathlib

open Set

/-! Gelfand problem, `GContract` (run 2026-11-20T1628Z; first pieces of the contracting homology cell planned in
section Next of `runs/2026-11-20T1628Z/README.md`). In log radius the homology system is
u' = u (3 − u − v), v' = v (u − 1). Its right side is quadratic, so the difference of the field at two points is
the Jacobian at their midpoint applied to their difference (`field_diff`). For the quadratic norm
Q(e) = (3/2) e₁² + e₁ e₂ + e₂² (the solution of the Lyapunov equation at the equilibrium (1, 2)), the form
e ↦ (P e) · J(m) e is affine in the midpoint m, so a bound by μ Q(e) on a box of midpoints follows from four
rational checks at its corners (`box_bound`, `cornersOK`), each a nonnegative diagonal and determinant of a
symmetric two-by-two matrix. -/

namespace Work.Math.GContract

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

end Work.Math.GContract
