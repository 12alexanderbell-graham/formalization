import Checked.Math.BEHCell

/-! Bonnor–Ebert sphere, `BEOCell`: one-sided (logarithmic-norm) validated cells for the isothermal equation in the homology variables. The cells of `BEHCell` bound the growth of the error with a Lipschitz constant, so their enclosure grows like a power of the radius although the true error contracts (the homology field spirals into its focus). Here the error is measured in a weighted norm taken from the real Jordan basis of the linearised field at the focus, in which the field has a negative one-sided bound on each cell; that bound is certified at the four corners of a box holding the cell polynomials and every point of the error ball (the field is quadratic, so its difference quotient is the Jacobian at the midpoint, which is affine in the midpoint). The enclosure then contracts instead of growing. Generic step `os_cell` (time-dependent field), cell check `CellProp` decided by the kernel, chains `chainTo`. Promoted from `Work/Math/BEOCell.lean`. -/

namespace Checked.Math.BEOCell
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.LECell
open Checked.Math.GCellQ (lo hi lo_le le_hi abs_link icc_glue)
open Checked.Math.BEHCell (Inv)

/-- The weighted squared norm 7 e₁² + (e₁ + 2 e₂)². -/
def Nw (e1 e2 : ℝ) : ℝ := 7 * e1 ^ 2 + (e1 + 2 * e2) ^ 2

/-- Its inner product. -/
def IP (a1 a2 e1 e2 : ℝ) : ℝ := 7 * a1 * e1 + (a1 + 2 * a2) * (e1 + 2 * e2)

theorem Nw_nonneg (e1 e2 : ℝ) : 0 ≤ Nw e1 e2 := by unfold Nw; positivity

theorem cs (a1 a2 e1 e2 : ℝ) : IP a1 a2 e1 e2 ^ 2 ≤ Nw a1 a2 * Nw e1 e2 := by
  unfold IP Nw
  nlinarith [sq_nonneg (a1 * (e1 + 2 * e2) - e1 * (a1 + 2 * a2))]

/-- Minkowski in the weighted norm. -/
theorem mink {a1 a2 b1 b2 p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : Nw a1 a2 ≤ p ^ 2)
    (hb : Nw b1 b2 ≤ q ^ 2) : Nw (a1 + b1) (a2 + b2) ≤ (p + q) ^ 2 := by
  have h := cs a1 a2 b1 b2
  have hab : IP a1 a2 b1 b2 ≤ p * q := by
    have h2 : IP a1 a2 b1 b2 ^ 2 ≤ (p * q) ^ 2 := by
      calc _ ≤ Nw a1 a2 * Nw b1 b2 := h
        _ ≤ p ^ 2 * q ^ 2 := mul_le_mul ha hb (Nw_nonneg _ _) (sq_nonneg _)
        _ = (p * q) ^ 2 := by ring
    exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
  have e : Nw (a1 + b1) (a2 + b2) = Nw a1 a2 + Nw b1 b2 + 2 * IP a1 a2 b1 b2 := by
    unfold Nw IP; ring
  rw [e]; nlinarith

/-- Coordinates from the weighted norm: |e₁| ≤ (2/5)·r and |e₂| ≤ (7/10)·r. -/
theorem coords {e1 e2 r : ℝ} (hr : 0 ≤ r) (h : Nw e1 e2 ≤ r ^ 2) :
    |e1| ≤ 2 / 5 * r ∧ |e2| ≤ 7 / 10 * r := by
  unfold Nw at h
  have h7 : e1 ^ 2 ≤ (2 / 5 * r) ^ 2 := by nlinarith [sq_nonneg (e1 + 2 * e2), sq_nonneg r]
  have h8 : (e1 + 2 * e2) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg e1]
  have a := abs_le_of_sq_le_sq' h7 (by positivity)
  have b := abs_le_of_sq_le_sq' h8 hr
  refine ⟨abs_le.2 a, ?_⟩
  rw [abs_le]; constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- From a box enclosure to the weighted norm. -/
theorem of_box {e1 e2 r : ℝ} (h1 : |e1| ≤ r) (h2 : |e2| ≤ r) : Nw e1 e2 ≤ (4 * r) ^ 2 := by
  unfold Nw
  have a := abs_le.1 h1; have b := abs_le.1 h2
  nlinarith [sq_abs e1, sq_abs e2, abs_nonneg e1, abs_nonneg e2]

/-- exp x ≤ 1/(1 − x) for x ≤ 0. -/
theorem exp_le_inv' {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  rw [le_div_iff₀ h1]
  have h2 := Real.add_one_le_exp (-x)
  have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x]

/-- Generic one-sided cell step with a time-dependent field, in the weighted norm `Nw`, for a
contracting bound μ ≤ 0. -/
theorem os_cell {F1 F2 : ℝ → ℝ → ℝ → ℝ} {f1 f2 g1 g2 G1 G2 : ℝ → ℝ} {a b μ ε δ B : ℝ}
    (hμ : μ ≤ 0) (hε : 0 < ε) (hδ : 0 < δ)
    (hf1 : ContinuousOn f1 (Icc a b)) (hf2 : ContinuousOn f2 (Icc a b))
    (hg1 : ContinuousOn g1 (Icc a b)) (hg2 : ContinuousOn g2 (Icc a b))
    (hf1' : ∀ t ∈ Ico a b, HasDerivWithinAt f1 (F1 t (f1 t) (f2 t)) (Ici t) t)
    (hf2' : ∀ t ∈ Ico a b, HasDerivWithinAt f2 (F2 t (f1 t) (f2 t)) (Ici t) t)
    (hg1' : ∀ t ∈ Ico a b, HasDerivWithinAt g1 (G1 t) (Ici t) t)
    (hg2' : ∀ t ∈ Ico a b, HasDerivWithinAt g2 (G2 t) (Ici t) t)
    (hdef : ∀ t ∈ Ico a b, Nw (G1 t - F1 t (g1 t) (g2 t)) (G2 t - F2 t (g1 t) (g2 t)) < ε ^ 2)
    (hos : ∀ t ∈ Ico a b, ∀ y1 y2 : ℝ, Nw (y1 - g1 t) (y2 - g2 t) ≤ B ^ 2 →
      IP (F1 t y1 y2 - F1 t (g1 t) (g2 t)) (F2 t y1 y2 - F2 t (g1 t) (g2 t)) (y1 - g1 t) (y2 - g2 t)
        ≤ μ * Nw (y1 - g1 t) (y2 - g2 t))
    (h0 : Nw (f1 a - g1 a) (f2 a - g2 a) ≤ δ ^ 2)
    (hB : δ + ε * (b - a) ≤ B) :
    ∀ t ∈ Icc a b, Nw (f1 t - g1 t) (f2 t - g2 t)
      ≤ (δ * Real.exp (μ * (t - a)) + ε * (t - a)) ^ 2 := by
  set R : ℝ → ℝ := fun t => δ * Real.exp (μ * (t - a)) + ε * (t - a) with hRdef
  set φ : ℝ → ℝ := fun t => Nw (f1 t - g1 t) (f2 t - g2 t) with hφdef
  have hRd : ∀ t, HasDerivAt R (μ * (δ * Real.exp (μ * (t - a))) + ε) t := by
    intro t
    have h2 : HasDerivAt (fun t => Real.exp (μ * (t - a))) (Real.exp (μ * (t - a)) * μ) t := by
      have := (((hasDerivAt_id t).sub_const a).const_mul μ).exp
      simpa using this
    have h1 : HasDerivAt (fun t => ε * (t - a)) ε t := by
      have := ((hasDerivAt_id t).sub_const a).const_mul ε
      simpa using this
    have := (h2.const_mul δ).add h1
    convert this using 1
    ring
  have hR2d : ∀ t, HasDerivAt (fun t => R t ^ 2)
      (2 * R t * (μ * (δ * Real.exp (μ * (t - a))) + ε)) t := by
    intro t
    have := (hRd t).pow 2
    convert this using 1
    norm_num
  have hRcont : Continuous R := by
    simp only [hRdef]; fun_prop
  have hRge : ∀ t, a ≤ t → δ * Real.exp (μ * (t - a)) ≤ R t := by
    intro t ht
    simp only [hRdef]
    nlinarith
  have hRpos : ∀ t, a ≤ t → 0 < R t := fun t ht =>
    lt_of_lt_of_le (mul_pos hδ (Real.exp_pos _)) (hRge t ht)
  have hRle : ∀ t, t ≤ b → a ≤ t → R t ≤ B := by
    intro t htb hta
    refine le_trans ?_ hB
    simp only [hRdef]
    have he : Real.exp (μ * (t - a)) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hμ (by linarith))
    have h1 : δ * Real.exp (μ * (t - a)) ≤ δ := by nlinarith
    have h2 : ε * (t - a) ≤ ε * (b - a) := by nlinarith
    linarith
  have key := image_le_of_deriv_right_lt_deriv_boundary' (f := φ)
    (f' := fun t => 2 * IP (F1 t (f1 t) (f2 t) - G1 t) (F2 t (f1 t) (f2 t) - G2 t)
      (f1 t - g1 t) (f2 t - g2 t))
    (B := fun t => R t ^ 2)
    (B' := fun t => 2 * R t * (μ * (δ * Real.exp (μ * (t - a))) + ε))
    (by simp only [hφdef, Nw]; fun_prop)
    (by
      intro t ht
      have e1 := ((hf1' t ht).sub (hg1' t ht)).pow 2
      have e3 := (((hf1' t ht).sub (hg1' t ht)).add (((hf2' t ht).sub (hg2' t ht)).const_mul 2)).pow 2
      have := (e1.const_mul 7).add e3
      convert this using 1
      · funext s; simp only [hφdef, Nw, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
      · simp only [IP, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]; norm_num; ring)
    (by
      simp only [hφdef, hRdef, sub_self, mul_zero, add_zero, Real.exp_zero, mul_one]
      exact h0)
    (hRcont.pow 2).continuousOn
    (fun t _ => (hR2d t).hasDerivWithinAt)
    (by
      intro t ht heq
      simp only [hφdef] at heq
      set e1 := f1 t - g1 t
      set e2 := f2 t - g2 t
      set D1 := G1 t - F1 t (g1 t) (g2 t)
      set D2 := G2 t - F2 t (g1 t) (g2 t)
      have hRt := hRge t ht.1
      have hRp : 0 < R t := hRpos t ht.1
      have hRB : R t ≤ B := hRle t ht.2.le ht.1
      have hball : Nw (f1 t - g1 t) (f2 t - g2 t) ≤ B ^ 2 := by
        rw [heq]
        exact pow_le_pow_left₀ hRp.le hRB 2
      have hos' := hos t ht (f1 t) (f2 t) hball
      have hD := hdef t ht
      have hcs : IP D1 D2 e1 e2 ^ 2 < (R t * ε) ^ 2 := by
        have h1 := cs D1 D2 e1 e2
        have hX : Nw e1 e2 = R t ^ 2 := heq
        have hR2 : 0 < R t ^ 2 := by positivity
        have : Nw D1 D2 * R t ^ 2 < ε ^ 2 * R t ^ 2 := mul_lt_mul_of_pos_right hD hR2
        rw [hX] at h1
        rw [mul_pow]
        linarith
      have hab' := abs_lt_of_sq_lt_sq hcs (by positivity)
      have hsplit : 2 * IP (F1 t (f1 t) (f2 t) - G1 t) (F2 t (f1 t) (f2 t) - G2 t) e1 e2
          = 2 * IP (F1 t (f1 t) (f2 t) - F1 t (g1 t) (g2 t)) (F2 t (f1 t) (f2 t) - F2 t (g1 t) (g2 t))
              e1 e2 - 2 * IP D1 D2 e1 e2 := by
        simp only [D1, D2, IP]; ring
      rw [hsplit]
      have hμle : μ * R t ≤ μ * (δ * Real.exp (μ * (t - a))) :=
        mul_le_mul_of_nonpos_left hRt hμ
      have hμR2 : μ * R t ^ 2 ≤ R t * (μ * (δ * Real.exp (μ * (t - a)))) := by
        have := mul_le_mul_of_nonneg_left hμle hRp.le
        nlinarith
      have hμR : μ * Nw e1 e2 = μ * R t ^ 2 := by rw [heq]
      have habs := (abs_lt.1 hab').1
      linarith)
  intro t ht
  exact key ht

/-! ## The Bonnor–Ebert homology field -/

theorem psd {a b c x y : ℝ} (ha : 0 < a) (hd : b ^ 2 ≤ 4 * a * c) : 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  have e : 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2) = (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by
    ring
  have h1 : 0 ≤ (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by
    have := sq_nonneg (2 * a * x + b * y); have := sq_nonneg y
    nlinarith
  rw [← e] at h1
  by_contra hc; push Not at hc
  nlinarith

/-- μ N(e) − ⟨J(m) e, e⟩_N as a quadratic form in e with coefficients affine in m. -/
def qf (m1 m2 μ e1 e2 : ℝ) : ℝ :=
  (16 * m1 + 6 * m2 + 8 * μ - 24) * e1 ^ 2 + (10 * m1 - 2 * m2 + 4 * μ - 4) * e1 * e2 +
    (-2 * m1 + 4 * μ + 4) * e2 ^ 2

/-- The corner condition, over ℚ. -/
def CornerOK (m1 m2 μ : ℚ) : Prop :=
  0 < 16 * m1 + 6 * m2 + 8 * μ - 24 ∧
  (10 * m1 - 2 * m2 + 4 * μ - 4) ^ 2 ≤ 4 * (16 * m1 + 6 * m2 + 8 * μ - 24) * (-2 * m1 + 4 * μ + 4)

instance (m1 m2 μ : ℚ) : Decidable (CornerOK m1 m2 μ) := by unfold CornerOK; infer_instance

theorem corner {m1 m2 μ : ℚ} (h : CornerOK m1 m2 μ) (e1 e2 : ℝ) : 0 ≤ qf m1 m2 μ e1 e2 := by
  obtain ⟨h1, h2⟩ := h
  have r1 : (0 : ℝ) < ((16 * m1 + 6 * m2 + 8 * μ - 24 : ℚ) : ℝ) := by exact_mod_cast h1
  have r2 : (((10 * m1 - 2 * m2 + 4 * μ - 4) ^ 2 : ℚ) : ℝ) ≤
      ((4 * (16 * m1 + 6 * m2 + 8 * μ - 24) * (-2 * m1 + 4 * μ + 4) : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at r1 r2
  unfold qf
  exact psd r1 r2

/-- The quadratic form is nonnegative on a box once it is at the four corners (affine in m). -/
theorem box_qf {UL UH VL VH μ m1 m2 e1 e2 : ℝ} (h1 : UL ≤ m1) (h2 : m1 ≤ UH) (h3 : VL ≤ m2)
    (h4 : m2 ≤ VH) (c1 : 0 ≤ qf UL VL μ e1 e2) (c2 : 0 ≤ qf UL VH μ e1 e2)
    (c3 : 0 ≤ qf UH VL μ e1 e2) (c4 : 0 ≤ qf UH VH μ e1 e2) : 0 ≤ qf m1 m2 μ e1 e2 := by
  have e : ∀ x y, qf x y μ e1 e2 = qf 0 0 μ e1 e2 + x * (16 * e1 ^ 2 + 10 * e1 * e2 - 2 * e2 ^ 2) +
      y * (6 * e1 ^ 2 - 2 * e1 * e2) := by intro x y; unfold qf; ring
  rw [e] at c1 c2 c3 c4 ⊢
  set β := 16 * e1 ^ 2 + 10 * e1 * e2 - 2 * e2 ^ 2
  set γ := 6 * e1 ^ 2 - 2 * e1 * e2
  rcases le_total 0 β with hb | hb <;> rcases le_total 0 γ with hc | hc
  · nlinarith [mul_le_mul_of_nonneg_left h1 hb, mul_le_mul_of_nonneg_left h3 hc]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hb, mul_le_mul_of_nonpos_left h4 hc]
  · nlinarith [mul_le_mul_of_nonpos_left h2 hb, mul_le_mul_of_nonneg_left h3 hc]
  · nlinarith [mul_le_mul_of_nonpos_left h2 hb, mul_le_mul_of_nonpos_left h4 hc]

/-- The homology field components at radius t. -/
noncomputable def F1 (t u v : ℝ) : ℝ := u * (3 - u - v) / t
noncomputable def F2 (t u v : ℝ) : ℝ := v * (u - 1) / t

/-- The one-sided bound of the homology field on a box (corners certified). -/
theorem os_box {t t1 μ UL UH VL VH g1 g2 y1 y2 : ℝ} {μq ULq UHq VLq VHq : ℚ}
    (hμe : (μq : ℝ) = μ) (hUL : (ULq : ℝ) = UL) (hUH : (UHq : ℝ) = UH) (hVL : (VLq : ℝ) = VL)
    (hVH : (VHq : ℝ) = VH)
    (ht : 0 < t) (ht1 : t ≤ t1) (hμ : μ ≤ 0)
    (k1 : CornerOK ULq VLq μq) (k2 : CornerOK ULq VHq μq) (k3 : CornerOK UHq VLq μq)
    (k4 : CornerOK UHq VHq μq)
    (m1 : UL ≤ g1 + (y1 - g1) / 2) (m2 : g1 + (y1 - g1) / 2 ≤ UH)
    (m3 : VL ≤ g2 + (y2 - g2) / 2) (m4 : g2 + (y2 - g2) / 2 ≤ VH) :
    IP (F1 t y1 y2 - F1 t g1 g2) (F2 t y1 y2 - F2 t g1 g2) (y1 - g1) (y2 - g2) ≤
      μ / t1 * Nw (y1 - g1) (y2 - g2) := by
  have hq := box_qf (μ := μ) (e1 := y1 - g1) (e2 := y2 - g2) m1 m2 m3 m4
    (by subst hμe hUL hVL; exact corner k1 _ _) (by subst hμe hUL hVH; exact corner k2 _ _)
    (by subst hμe hUH hVL; exact corner k3 _ _) (by subst hμe hUH hVH; exact corner k4 _ _)
  have e : IP (F1 t y1 y2 - F1 t g1 g2) (F2 t y1 y2 - F2 t g1 g2) (y1 - g1) (y2 - g2) =
      (μ * Nw (y1 - g1) (y2 - g2) - qf (g1 + (y1 - g1) / 2) (g2 + (y2 - g2) / 2) μ (y1 - g1) (y2 - g2)) / t := by
    unfold IP F1 F2 Nw qf; field_simp; ring
  rw [e]
  have hN := Nw_nonneg (y1 - g1) (y2 - g2)
  have hμN : μ * Nw (y1 - g1) (y2 - g2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hμ hN
  have ht1p : 0 < t1 := lt_of_lt_of_le ht ht1
  rw [div_le_iff₀ ht]
  have : μ / t1 * Nw (y1 - g1) (y2 - g2) * t = μ * Nw (y1 - g1) (y2 - g2) * (t / t1) := by
    field_simp
  rw [this]
  have htt : t / t1 ≤ 1 := (div_le_one ht1p).2 ht1
  nlinarith

/-- One cell: start `t0`, length `h`, input radius `δ`, defect bound `ε`, ball radius `B`, output
radius `Be` (all in the weighted norm), one-sided constant `μ ≤ 0` (per unit of log-radius), box
`[UL, UH] × [VL, VH]`, Taylor polynomials `pu`, `pv` in σ = t − t0. -/
structure OCell where
  t0 : ℚ
  h : ℚ
  δ : ℚ
  ε : ℚ
  B : ℚ
  Be : ℚ
  μ : ℚ
  UL : ℚ
  UH : ℚ
  VL : ℚ
  VH : ℚ
  pu : List ℚ
  pv : List ℚ

/-- (t0+σ) pu′ − pu (3 − pu − pv), computed. -/
def du1 (c : OCell) : List ℚ :=
  qsub (qmul [c.t0, 1] (qderiv c.pu)) (qmul c.pu (qsub (qsub [3] c.pu) c.pv))

/-- (t0+σ) pv′ − pv (pu − 1), computed. -/
def dv1 (c : OCell) : List ℚ :=
  qsub (qmul [c.t0, 1] (qderiv c.pv)) (qmul c.pv (qsub c.pu [1]))

/-- du1 + 2 dv1, computed. -/
def dx (c : OCell) : List ℚ := qadd (du1 c) (qsmul 2 (dv1 c))

theorem du1_eval (c : OCell) (σ : ℝ) :
    ((c.t0 : ℝ) + σ) * dEvalQ c.pu σ - evalQ c.pu σ * (3 - evalQ c.pu σ - evalQ c.pv σ) =
      evalQ (du1 c) σ := by
  simp only [du1, evalQ_qsub, evalQ_qmul, ← dEvalQ_eq, evalQ]; push_cast; ring

theorem dv1_eval (c : OCell) (σ : ℝ) :
    ((c.t0 : ℝ) + σ) * dEvalQ c.pv σ - evalQ c.pv σ * (evalQ c.pu σ - 1) = evalQ (dv1 c) σ := by
  simp only [dv1, evalQ_qsub, evalQ_qmul, ← dEvalQ_eq, evalQ]; push_cast; ring

theorem dx_eval (c : OCell) (σ : ℝ) : evalQ (du1 c) σ + 2 * evalQ (dv1 c) σ = evalQ (dx c) σ := by
  simp only [dx, evalQ_qadd, evalQ_qsmul]; push_cast; ring

/-- All side conditions of a cell as one proposition over ℚ. -/
def CellProp (L T : ℚ) (c : OCell) : Prop :=
  L ≤ c.t0 ∧ 0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h ∧ c.μ ≤ 0 ∧ 0 < c.ε ∧ 0 < c.δ ∧
  c.δ + c.ε * c.h ≤ c.B ∧ 0 < c.UL ∧ 0 < c.VL ∧
  c.UL + c.B ≤ lo c.pu c.h ∧ hi c.pu c.h + c.B ≤ c.UH ∧
  c.VL + c.B ≤ lo c.pv c.h ∧ hi c.pv c.h + c.B ≤ c.VH ∧
  CornerOK c.UL c.VL c.μ ∧ CornerOK c.UL c.VH c.μ ∧ CornerOK c.UH c.VL c.μ ∧ CornerOK c.UH c.VH c.μ ∧
  7 * qabs (du1 c) c.h ^ 2 + qabs (dx c) c.h ^ 2 < (c.ε * c.t0) ^ 2 ∧
  c.δ * (1 / (1 - c.μ / (c.t0 + c.h) * c.h)) + c.ε * c.h ≤ c.Be

instance (L T : ℚ) (c : OCell) : Decidable (CellProp L T c) := by
  unfold CellProp; infer_instance

/-- One validated cell from its Boolean check, for every solution (u, v) of the homology system with
derivatives within [L, T]. -/
theorem cell_q {L T : ℚ} (c : OCell) (hok : decide (CellProp L T c) = true) {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : Nw (u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)) (v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)) ≤ (c.δ : ℝ) ^ 2) :
    (∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      Nw (u t - evalQ c.pu (t - c.t0)) (v t - evalQ c.pv (t - c.t0)) ≤ (c.B : ℝ) ^ 2) ∧
    Nw (u (c.t0 + c.h) - ((qeval c.pu c.h : ℚ) : ℝ)) (v (c.t0 + c.h) - ((qeval c.pv c.h : ℚ) : ℝ))
      ≤ (c.Be : ℝ) ^ 2 := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, c1, c2, c3, c4, kd, ke⟩ :
    CellProp L T c := of_decide_eq_true hok
  have r : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => by exact_mod_cast h
  have r0 := r k0; have r7 := r k7; have r10 := r k10; have r11 := r k11; have r12 := r k12
  have r13 := r k13; have re := r ke
  have rd : ((7 * qabs (du1 c) c.h ^ 2 + qabs (dx c) c.h ^ 2 : ℚ) : ℝ) < (((c.ε * c.t0) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast kd
  push_cast at r0 r7 r10 r11 r12 r13 re rd
  have ht0 : (0 : ℝ) < c.t0 := by exact_mod_cast k1
  have hT : ((c.t0 : ℝ) + c.h) ≤ T := by exact_mod_cast k2
  have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
  have hμ : (c.μ : ℝ) ≤ 0 := by exact_mod_cast k4
  have hε : (0 : ℝ) < c.ε := by exact_mod_cast k5
  have hδ : (0 : ℝ) < c.δ := by exact_mod_cast k6
  have hT0 : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc (L : ℝ) T := Icc_subset_Icc r0 hT
  have hs : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), t - c.t0 ∈ Icc (0 : ℝ) c.h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hB0 : (0 : ℝ) ≤ c.B := by nlinarith
  set μt : ℝ := (c.μ : ℝ) / (c.t0 + c.h) with hμt
  have hμt0 : μt ≤ 0 := div_nonpos_of_nonpos_of_nonneg hμ (by linarith)
  have key := os_cell (F1 := F1) (F2 := F2) (f1 := u) (f2 := v)
    (g1 := fun t => evalQ c.pu (t - c.t0)) (g2 := fun t => evalQ c.pv (t - c.t0))
    (G1 := fun t => dEvalQ c.pu (t - c.t0)) (G2 := fun t => dEvalQ c.pv (t - c.t0))
    (a := c.t0) (b := c.t0 + c.h) (μ := μt) (ε := c.ε) (δ := c.δ) (B := c.B)
    hμt0 hε hδ
    (fun t ht => ((hu t ht).continuousWithinAt).mono hT0)
    (fun t ht => ((hv t ht).continuousWithinAt).mono hT0)
    ((continuous_evalQ c.pu).comp (continuous_sub_right _)).continuousOn
    ((continuous_evalQ c.pv).comp (continuous_sub_right _)).continuousOn
    (fun t ht => (hu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    (fun t ht => (hv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    (fun t _ => ((hasDerivAt_evalQ c.pu (t - c.t0)).comp_sub_const t _).hasDerivWithinAt)
    (fun t _ => ((hasDerivAt_evalQ c.pv (t - c.t0)).comp_sub_const t _).hasDerivWithinAt)
    (fun t ht => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      have et : (c.t0 : ℝ) + (t - c.t0) = t := by ring
      have a1 := abs_le_qabs (du1 c) hσ.1 hσ.2
      have a2 := abs_le_qabs (dx c) hσ.1 hσ.2
      rw [← du1_eval, et] at a1
      rw [← dx_eval, ← du1_eval, ← dv1_eval, et] at a2
      set P := evalQ c.pu (t - c.t0)
      set Q := evalQ c.pv (t - c.t0)
      set P' := dEvalQ c.pu (t - c.t0)
      set Q' := dEvalQ c.pv (t - c.t0)
      have e : Nw (P' - F1 t P Q) (Q' - F2 t P Q) * t ^ 2 =
          7 * (t * P' - P * (3 - P - Q)) ^ 2 +
            ((t * P' - P * (3 - P - Q)) + 2 * (t * Q' - Q * (P - 1))) ^ 2 := by
        unfold Nw F1 F2; field_simp
      have b1 : (t * P' - P * (3 - P - Q)) ^ 2 ≤ ((qabs (du1 c) c.h : ℚ) : ℝ) ^ 2 :=
        sq_le_sq' (abs_le.1 a1).1 (abs_le.1 a1).2
      have b2 : ((t * P' - P * (3 - P - Q)) + 2 * (t * Q' - Q * (P - 1))) ^ 2 ≤
          ((qabs (dx c) c.h : ℚ) : ℝ) ^ 2 := sq_le_sq' (abs_le.1 a2).1 (abs_le.1 a2).2
      have htt : (c.ε : ℝ) ^ 2 * c.t0 ^ 2 ≤ c.ε ^ 2 * t ^ 2 := by
        have : (c.t0 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ht0.le ht.1 2
        exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
      have ht2 : 0 < t ^ 2 := by positivity
      have : Nw (P' - F1 t P Q) (Q' - F2 t P Q) * t ^ 2 < c.ε ^ 2 * t ^ 2 := by
        rw [e]; nlinarith
      exact lt_of_mul_lt_mul_right this ht2.le)
    (fun t ht y1 y2 hy => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      obtain ⟨a1, a2⟩ := coords hB0 hy
      have g1 := lo_le c.pu hσ.1 hσ.2
      have g2 := le_hi c.pu hσ.1 hσ.2
      have g3 := lo_le c.pv hσ.1 hσ.2
      have g4 := le_hi c.pv hσ.1 hσ.2
      have b1 := abs_le.1 a1; have b2 := abs_le.1 a2
      exact os_box rfl rfl rfl rfl rfl htpos ht.2.le hμ c1 c2 c3 c4
        (by linarith) (by linarith) (by linarith) (by linarith))
    (by
      simp only [sub_self]
      rw [evalQ_zero_head, evalQ_zero_head]
      exact h0)
    (by linarith)
  refine ⟨fun t ht => (key t ht).trans ?_, ?_⟩
  · have hσ := hs t ht
    have he : Real.exp (μt * (t - c.t0)) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hμt0 hσ.1)
    have h1 : (c.δ : ℝ) * Real.exp (μt * (t - c.t0)) + c.ε * (t - c.t0) ≤ c.B := by
      have a1 := mul_le_mul_of_nonneg_left he hδ.le
      have a2 := mul_le_mul_of_nonneg_left hσ.2 hε.le
      linarith only [a1, a2, r7]
    have h2 : 0 ≤ (c.δ : ℝ) * Real.exp (μt * (t - c.t0)) + c.ε * (t - c.t0) := by
      have a1 := mul_pos hδ (Real.exp_pos (μt * (t - c.t0)))
      have a2 := mul_nonneg hε.le hσ.1
      linarith only [a1, a2]
    exact pow_le_pow_left₀ h2 h1 2
  · have k := key (c.t0 + c.h) ⟨by linarith, le_rfl⟩
    rw [add_sub_cancel_left, ← qeval_cast, ← qeval_cast] at k
    refine k.trans ?_
    have hx : μt * c.h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hμt0 hh.le
    have he := exp_le_inv' hx
    have h1 : (c.δ : ℝ) * Real.exp (μt * c.h) + c.ε * c.h ≤ c.Be := by
      have := mul_le_mul_of_nonneg_left he hδ.le
      calc _ ≤ (c.δ : ℝ) * (1 / (1 - μt * c.h)) + c.ε * c.h := by linarith only [this]
        _ ≤ c.Be := re
    have h2 : 0 ≤ (c.δ : ℝ) * Real.exp (μt * c.h) + c.ε * c.h := by
      have a1 := mul_pos hδ (Real.exp_pos (μt * c.h))
      have a2 := mul_pos hε hh
      linarith only [a1, a2]
    exact pow_le_pow_left₀ h2 h1 2

/-- Box form of the cell's enclosure. -/
theorem cell_box' {L T : ℚ} (c : OCell) (hok : decide (CellProp L T c) = true) {u v : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h))
    (hN : Nw (u t - evalQ c.pu (t - c.t0)) (v t - evalQ c.pv (t - c.t0)) ≤ (c.B : ℝ) ^ 2) :
    |u t - evalQ c.pu (t - c.t0)| ≤ c.B ∧ |v t - evalQ c.pv (t - c.t0)| ≤ c.B ∧
    (c.UL : ℝ) ≤ u t ∧ u t ≤ c.UH ∧ (c.VL : ℝ) ≤ v t ∧ v t ≤ c.VH ∧
    (c.UL : ℝ) ≤ evalQ c.pu (t - c.t0) ∧ evalQ c.pu (t - c.t0) ≤ c.UH ∧
    (c.VL : ℝ) ≤ evalQ c.pv (t - c.t0) ∧ evalQ c.pv (t - c.t0) ≤ c.VH ∧ (0 : ℝ) ≤ c.B ∧
    (0 : ℝ) < c.UL ∧ (0 : ℝ) < c.VL := by
  obtain ⟨-, -, -, -, -, k5, k6, k7, k8, k9, k10, k11, k12, k13, -⟩ : CellProp L T c :=
    of_decide_eq_true hok
  have r : ∀ {a b : ℚ}, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun h => by exact_mod_cast h
  have r7 := r k7; have r10 := r k10; have r11 := r k11; have r12 := r k12; have r13 := r k13
  push_cast at r7 r10 r11 r12 r13
  have hε : (0 : ℝ) < c.ε := by exact_mod_cast k5
  have hδ : (0 : ℝ) < c.δ := by exact_mod_cast k6
  have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
  have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
  have hh : (0 : ℝ) ≤ c.h := le_trans hσ0 hσ1
  have hB : (0 : ℝ) ≤ c.B := by nlinarith
  obtain ⟨a1, a2⟩ := coords hB hN
  have e1 : |u t - evalQ c.pu (t - c.t0)| ≤ c.B := a1.trans (by linarith)
  have e2 : |v t - evalQ c.pv (t - c.t0)| ≤ c.B := a2.trans (by linarith)
  have g1 := lo_le c.pu hσ0 hσ1
  have g2 := le_hi c.pu hσ0 hσ1
  have g3 := lo_le c.pv hσ0 hσ1
  have g4 := le_hi c.pv hσ0 hσ1
  have b1 := abs_le.1 e1
  have b2 := abs_le.1 e2
  have r4 : (0 : ℝ) < c.UL := by exact_mod_cast k8
  have r5 : (0 : ℝ) < c.VL := by exact_mod_cast k9
  refine ⟨e1, e2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hB, r4, r5⟩ <;> linarith

/-- The invariant of a cell as a proposition over ℚ (as in `BEHCell.InvProp`). -/
def InvProp (m : ℕ) (c : OCell) : Prop :=
  match m with
  | 1 => 0 < lo (Checked.Math.BEHCell.gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) c.h - 3 * c.B
  | 2 => hi (Checked.Math.BEHCell.gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) c.h + 3 * c.B < 0
  | 3 => 0 < lo (Checked.Math.BEHCell.Gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) c.h -
      (7 + 7 * c.UH + 3 * c.VH) * c.B
  | 4 => hi (Checked.Math.BEHCell.Gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) c.h +
      (7 + 7 * c.UH + 3 * c.VH) * c.B < 0
  | _ => True

/-- The invariant as a statement about the solution at radius t: `BEHCell.Inv`, and 4 =
(6u − 2u² − 3uv + v < 0). -/
def OInv (m : ℕ) (u v : ℝ → ℝ) (t : ℝ) : Prop :=
  match m with
  | 4 => 6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t < 0
  | n => Inv n u v t

instance (m : ℕ) (c : OCell) : Decidable (InvProp m c) := by
  unfold InvProp; split <;> infer_instance

/-- Cell conditions and invariant, as a Boolean for evaluation by the kernel. -/
def cellOK (L T : ℚ) (m : ℕ) (c : OCell) : Bool := decide (CellProp L T c) && decide (InvProp m c)

theorem cell_basic {L T : ℚ} {m : ℕ} (c : OCell) (hok : cellOK L T m c = true) :
    L ≤ c.t0 ∧ 0 < c.t0 ∧ c.t0 + c.h ≤ T ∧ 0 < c.h := by
  simp only [cellOK, Bool.and_eq_true] at hok
  obtain ⟨k0, k1, k2, k3, -⟩ : CellProp L T c := of_decide_eq_true hok.1
  exact ⟨k0, k1, k2, k3⟩

/-- What one cell gives: the invariant on the cell and the end enclosure. -/
theorem cell_facts {L T : ℚ} {m : ℕ} (c : OCell) (hok : cellOK L T m c = true) {u v : ℝ → ℝ}
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : Nw (u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)) (v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)) ≤ (c.δ : ℝ) ^ 2) :
    (∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), OInv m u v t) ∧
    Nw (u (c.t0 + c.h) - ((qeval c.pu c.h : ℚ) : ℝ)) (v (c.t0 + c.h) - ((qeval c.pv c.h : ℚ) : ℝ))
      ≤ (c.Be : ℝ) ^ 2 := by
  have hok' := hok
  simp only [cellOK, Bool.and_eq_true] at hok'
  have hc := cell_q c hok'.1 hu hv h0
  refine ⟨fun t ht => ?_, hc.2⟩
  have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
  have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
  obtain ⟨e1, e2, b1, b2, b3, b4, b5, b6, b7, b8, hB, hUL, hVL⟩ := cell_box' c hok'.1 ht (hc.1 t ht)
  have a1 := abs_le.1 e1
  have a2 := abs_le.1 e2
  have kv := of_decide_eq_true hok'.2
  match m, kv with
  | 1, kv =>
    have rv : ((0 : ℚ) : ℝ) < ((lo (Checked.Math.BEHCell.gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) c.h - 3 * c.B : ℚ) : ℝ) := by
      exact_mod_cast kv
    push_cast at rv
    have hl := lo_le (Checked.Math.BEHCell.gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) hσ0 hσ1
    rw [← Checked.Math.BEHCell.gp_eval] at hl
    show 0 < 2 * u t - v t
    linarith
  | 2, kv =>
    have rv : ((hi (Checked.Math.BEHCell.gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) c.h + 3 * c.B : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by
      exact_mod_cast kv
    push_cast at rv
    have hl := le_hi (Checked.Math.BEHCell.gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) hσ0 hσ1
    rw [← Checked.Math.BEHCell.gp_eval] at hl
    show 2 * u t - v t < 0
    linarith
  | 3, kv =>
    have rv : ((0 : ℚ) : ℝ) < ((lo (Checked.Math.BEHCell.Gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) c.h - (7 + 7 * c.UH + 3 * c.VH) * c.B : ℚ) : ℝ) := by
      exact_mod_cast kv
    push_cast at rv
    have hl := lo_le (Checked.Math.BEHCell.Gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) hσ0 hσ1
    rw [← Checked.Math.BEHCell.Gp_eval] at hl
    show 0 < 6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t
    set p := evalQ c.pu (t - c.t0)
    set q := evalQ c.pv (t - c.t0)
    have e : (6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t) -
        (6 * p - 2 * p ^ 2 - 3 * (p * q) + q) =
        (6 - 2 * (u t + p) - 3 * v t) * (u t - p) + (1 - 3 * p) * (v t - q) := by ring
    have c1 : |6 - 2 * (u t + p) - 3 * v t| ≤ 6 + 4 * c.UH + 3 * c.VH := by
      rw [abs_le]; constructor <;> linarith
    have c2 : |1 - 3 * p| ≤ 1 + 3 * c.UH := by rw [abs_le]; constructor <;> linarith
    have d : |(6 - 2 * (u t + p) - 3 * v t) * (u t - p) + (1 - 3 * p) * (v t - q)| ≤
        (7 + 7 * c.UH + 3 * c.VH) * c.B := by
      calc _ ≤ |(6 - 2 * (u t + p) - 3 * v t) * (u t - p)| + |(1 - 3 * p) * (v t - q)| :=
            abs_add_le _ _
        _ = |6 - 2 * (u t + p) - 3 * v t| * |u t - p| + |1 - 3 * p| * |v t - q| := by
            rw [abs_mul, abs_mul]
        _ ≤ (6 + 4 * c.UH + 3 * c.VH) * c.B + (1 + 3 * c.UH) * c.B := by
            gcongr <;> linarith [abs_nonneg (6 - 2 * (u t + p) - 3 * v t), abs_nonneg (1 - 3 * p)]
        _ = (7 + 7 * c.UH + 3 * c.VH) * c.B := by ring
    rw [← e] at d
    have := (abs_le.1 d).1
    linarith
  | 4, kv =>
    have rv : ((hi (Checked.Math.BEHCell.Gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) c.h + (7 + 7 * c.UH + 3 * c.VH) * c.B : ℚ) : ℝ) < ((0 : ℚ) : ℝ) := by
      exact_mod_cast kv
    push_cast at rv
    have hl := le_hi (Checked.Math.BEHCell.Gp ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, c.pu, c.pv⟩) hσ0 hσ1
    rw [← Checked.Math.BEHCell.Gp_eval] at hl
    show 6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t < 0
    set p := evalQ c.pu (t - c.t0)
    set q := evalQ c.pv (t - c.t0)
    have e : (6 * u t - 2 * u t ^ 2 - 3 * (u t * v t) + v t) -
        (6 * p - 2 * p ^ 2 - 3 * (p * q) + q) =
        (6 - 2 * (u t + p) - 3 * v t) * (u t - p) + (1 - 3 * p) * (v t - q) := by ring
    have c1 : |6 - 2 * (u t + p) - 3 * v t| ≤ 6 + 4 * c.UH + 3 * c.VH := by
      rw [abs_le]; constructor <;> linarith
    have c2 : |1 - 3 * p| ≤ 1 + 3 * c.UH := by rw [abs_le]; constructor <;> linarith
    have d : |(6 - 2 * (u t + p) - 3 * v t) * (u t - p) + (1 - 3 * p) * (v t - q)| ≤
        (7 + 7 * c.UH + 3 * c.VH) * c.B := by
      calc _ ≤ |(6 - 2 * (u t + p) - 3 * v t) * (u t - p)| + |(1 - 3 * p) * (v t - q)| :=
            abs_add_le _ _
        _ = |6 - 2 * (u t + p) - 3 * v t| * |u t - p| + |1 - 3 * p| * |v t - q| := by
            rw [abs_mul, abs_mul]
        _ ≤ (6 + 4 * c.UH + 3 * c.VH) * c.B + (1 + 3 * c.UH) * c.B := by
            gcongr <;> linarith [abs_nonneg (6 - 2 * (u t + p) - 3 * v t), abs_nonneg (1 - 3 * p)]
        _ = (7 + 7 * c.UH + 3 * c.VH) * c.B := by ring
    rw [← e] at d
    have := (abs_le.1 d).2
    linarith
  | 0, _ => trivial
  | (n + 5), _ => trivial

/-- The weighted squared norm over ℚ. -/
def NwQ (e1 e2 : ℚ) : ℚ := 7 * e1 ^ 2 + (e1 + 2 * e2) ^ 2

theorem NwQ_cast (e1 e2 : ℚ) : ((NwQ e1 e2 : ℚ) : ℝ) = Nw e1 e2 := by
  unfold NwQ Nw; push_cast; ring

/-- Consecutive cells meet, and the end ball of `c` lies in the input ball of `d`. -/
def linkOK (c d : OCell) : Bool :=
  decide (c.t0 + c.h = d.t0 ∧ 0 ≤ c.Be ∧ c.Be ≤ d.δ ∧
    NwQ (qeval c.pu c.h - d.pu.headD 0) (qeval c.pv c.h - d.pv.headD 0) ≤ (d.δ - c.Be) ^ 2)

theorem link {x y gx gy hx hy Be δ : ℝ} (h1 : Nw (x - gx) (y - gy) ≤ Be ^ 2) (hBe : 0 ≤ Be)
    (hle : Be ≤ δ) (h2 : Nw (gx - hx) (gy - hy) ≤ (δ - Be) ^ 2) : Nw (x - hx) (y - hy) ≤ δ ^ 2 := by
  have := mink hBe (by linarith) h1 h2
  have e1 : x - gx + (gx - hx) = x - hx := by ring
  have e2 : y - gy + (gy - hy) = y - hy := by ring
  rw [e1, e2] at this
  simpa using this

/-- A chain of cells inside [L, T] with invariant `m`, whose last cell satisfies `term`. -/
def chainTo (L T : ℚ) (m : ℕ) (term : OCell → Bool) : List OCell → Bool
  | [] => false
  | [c] => cellOK L T m c && term c
  | c :: d :: l => cellOK L T m c && linkOK c d && chainTo L T m term (d :: l)

/-- Terminal condition: the last cell ends at `te` with its enclosure within `r` of (fu, fv). -/
def endOK (te fu fv r : ℚ) (c : OCell) : Bool :=
  decide (c.t0 + c.h = te ∧ 0 ≤ c.Be ∧ |qeval c.pu c.h - fu| + c.Be ≤ r ∧
    |qeval c.pv c.h - fv| + c.Be ≤ r)

theorem chain_gen {L T : ℚ} {m : ℕ} {term : OCell → Bool} {u v : ℝ → ℝ} :
    ∀ (l : List OCell) (c : OCell), chainTo L T m term (c :: l) = true →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t) →
    (∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t) →
    Nw (u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)) (v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)) ≤ (c.δ : ℝ) ^ 2 →
    ∃ e : OCell, term e = true ∧ (c.t0 : ℝ) ≤ e.t0 + e.h ∧
    (∀ t ∈ Icc (c.t0 : ℝ) (e.t0 + e.h), OInv m u v t) ∧
    Nw (u (e.t0 + e.h) - ((qeval e.pu e.h : ℚ) : ℝ)) (v (e.t0 + e.h) - ((qeval e.pv e.h : ℚ) : ℝ))
      ≤ (e.Be : ℝ) ^ 2 := by
  intro l
  induction l with
  | nil =>
    intro c hok hu hv h0
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨k1, kt⟩ := hok
    obtain ⟨-, -, k2, k3⟩ := cell_basic c k1
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    push_cast at k2'
    have hf := cell_facts c k1 (u := u) (v := v)
      (fun t ht => hu t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hv t ⟨ht.1, by linarith [ht.2]⟩) h0
    exact ⟨c, kt, by linarith, hf⟩
  | cons d l ih =>
    intro c hok hu hv h0
    simp only [chainTo, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kl⟩, krest⟩ := hok
    obtain ⟨ke, kB0, kB, kN⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    obtain ⟨-, -, k2, k3⟩ := cell_basic c k1
    have hh : (0 : ℝ) < c.h := by exact_mod_cast k3
    have k2' : ((c.t0 + c.h : ℚ) : ℝ) ≤ T := by exact_mod_cast k2
    push_cast at k2'
    have hf := cell_facts c k1 (u := u) (v := v)
      (fun t ht => hu t ⟨ht.1, by linarith [ht.2]⟩)
      (fun t ht => hv t ⟨ht.1, by linarith [ht.2]⟩) h0
    rw [he] at hf
    have kB' : (c.Be : ℝ) ≤ d.δ := by exact_mod_cast kB
    have kN'' : Nw (((qeval c.pu c.h : ℚ) : ℝ) - ((d.pu.headD 0 : ℚ) : ℝ))
        (((qeval c.pv c.h : ℚ) : ℝ) - ((d.pv.headD 0 : ℚ) : ℝ)) ≤ ((d.δ : ℝ) - c.Be) ^ 2 := by
      have := (show ((NwQ (qeval c.pu c.h - d.pu.headD 0) (qeval c.pv c.h - d.pv.headD 0) : ℚ) : ℝ)
        ≤ (((d.δ - c.Be) ^ 2 : ℚ) : ℝ) by exact_mod_cast kN)
      rw [NwQ_cast] at this; push_cast at this; exact this
    have hBe0 : (0 : ℝ) ≤ c.Be := by exact_mod_cast kB0
    obtain ⟨e, het, hce, hinv, hb⟩ := ih d krest
      (fun t ht => hu t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hv t ⟨by linarith [ht.1], ht.2⟩)
      (link hf.2 hBe0 kB' kN'')
    exact ⟨e, het, by linarith, icc_glue hf.1 hinv, hb⟩

/-- A segment of a chain: the invariant up to the start of `d`, and the solution enters the input
ball of `d`. -/
theorem seg_q {L T : ℚ} {m : ℕ} {u v : ℝ → ℝ} (d : OCell) (l : List OCell) (c : OCell)
    (hok : chainTo L T m (fun e => linkOK e d) (c :: l) = true)
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : Nw (u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)) (v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)) ≤ (c.δ : ℝ) ^ 2) :
    (c.t0 : ℝ) ≤ d.t0 ∧ (∀ t ∈ Icc (c.t0 : ℝ) d.t0, OInv m u v t) ∧
    Nw (u d.t0 - ((d.pu.headD 0 : ℚ) : ℝ)) (v d.t0 - ((d.pv.headD 0 : ℚ) : ℝ)) ≤ (d.δ : ℝ) ^ 2 := by
  obtain ⟨e, het, hce, hinv, hb⟩ := chain_gen l c hok hu hv h0
  obtain ⟨ke, kB0, kB, kN⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hce hinv hb
  have kB' : (e.Be : ℝ) ≤ d.δ := by exact_mod_cast kB
  have kN'' : Nw (((qeval e.pu e.h : ℚ) : ℝ) - ((d.pu.headD 0 : ℚ) : ℝ))
      (((qeval e.pv e.h : ℚ) : ℝ) - ((d.pv.headD 0 : ℚ) : ℝ)) ≤ ((d.δ : ℝ) - e.Be) ^ 2 := by
    have := (show ((NwQ (qeval e.pu e.h - d.pu.headD 0) (qeval e.pv e.h - d.pv.headD 0) : ℚ) : ℝ)
      ≤ (((d.δ - e.Be) ^ 2 : ℚ) : ℝ) by exact_mod_cast kN)
    rw [NwQ_cast] at this; push_cast at this; exact this
  have hBe0 : (0 : ℝ) ≤ e.Be := by exact_mod_cast kB0
  exact ⟨hce, hinv, link hb hBe0 kB' kN''⟩

/-- The last segment of a chain: the invariant up to `te`, and the solution is within `r` of
(fu, fv) at `te`. -/
theorem end_q {L T te fu fv r : ℚ} {m : ℕ} {u v : ℝ → ℝ} (l : List OCell) (c : OCell)
    (hok : chainTo L T m (endOK te fu fv r) (c :: l) = true)
    (hu : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt u (u t * (3 - u t - v t) / t) (Icc (L : ℝ) T) t)
    (hv : ∀ t ∈ Icc (c.t0 : ℝ) T, HasDerivWithinAt v (v t * (u t - 1) / t) (Icc (L : ℝ) T) t)
    (h0 : Nw (u c.t0 - ((c.pu.headD 0 : ℚ) : ℝ)) (v c.t0 - ((c.pv.headD 0 : ℚ) : ℝ)) ≤ (c.δ : ℝ) ^ 2) :
    (∀ t ∈ Icc (c.t0 : ℝ) te, OInv m u v t) ∧ |u te - fu| ≤ r ∧ |v te - fv| ≤ r := by
  obtain ⟨e, het, -, hinv, hb⟩ := chain_gen l c hok hu hv h0
  obtain ⟨ke, kB0, kE, kφ⟩ := of_decide_eq_true het
  have he : ((e.t0 + e.h : ℚ) : ℝ) = (te : ℝ) := by exact_mod_cast ke
  push_cast at he
  rw [he] at hinv hb
  have hB0 : (0 : ℝ) ≤ e.Be := by exact_mod_cast kB0
  obtain ⟨a1, a2⟩ := coords hB0 hb
  have kE' : |((qeval e.pu e.h : ℚ) : ℝ) - fu| + e.Be ≤ r := by exact_mod_cast kE
  have kφ' : |((qeval e.pv e.h : ℚ) : ℝ) - fv| + e.Be ≤ r := by exact_mod_cast kφ
  exact ⟨hinv, abs_link (a1.trans (by linarith)) kE', abs_link (a2.trans (by linarith)) kφ'⟩

/-- Entering a chain from a box enclosure. -/
theorem start_box {u0 v0 p q r δ : ℝ} (h1 : |u0 - p| ≤ r) (h2 : |v0 - q| ≤ r) (hr : 4 * r ≤ δ)
    (hr0 : 0 ≤ r) : Nw (u0 - p) (v0 - q) ≤ δ ^ 2 :=
  (of_box h1 h2).trans (pow_le_pow_left₀ (by linarith) hr 2)

end Checked.Math.BEOCell
