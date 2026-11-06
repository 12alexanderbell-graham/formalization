import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Bound
import Checked.Sim.ODETools
import Checked.Sim.OneSidedNeg
import Checked.Sim.RobCell
import Checked.Sim.ChebBound

/-!
# Robertson network at long horizons: the sheared-weight contracting cell step

On the slow manifold of Robertson's network no diagonal weight makes the field contracting
(best one-sided bound μ ≥ 0, run 2026-11-06T0628Z). In sheared coordinates
(e₂, k) = (y₂ − g₂, (y₃ + c y₂) − (g₃ + c g₂)) with norm d²e₂² + k² the one-sided bound reaches
the slow eigenvalue (≈ −2/t). This file gives:

* `shear_onesided`: the one-sided bound on a ball, certified by a 2×2 positive-semidefinite
  condition at the 8 corners of the box (x₂, x₃, h₂) — the form μ·N − ⟨ΔF, e⟩ is affine in the
  base point and in h₂ for fixed (u, k) = (d h₂, k), so nonnegativity at the corners suffices;
* `cellS`, `stepS`: one cell of the long-horizon enclosure (`Checked.Sim.OneSidedNeg.onesided_cell_neg`
  in sheared coordinates), with Chebyshev defect bounds (`Checked.Sim.ChebBound`) and a change of
  shear c → c' at the end of the cell;
* `start_shear`, `final_shear`: from the t = 40 ball (weight 4900·e₂² + e₃²) into the sheared norm,
  and from the sheared norm back to componentwise bounds.
-/

namespace Checked.Sim.RobShear
open Set Checked.Sim Checked.Sim.RobCell Checked.Sim.ChebBound

/-- Coefficient of u² (u = d·h₂) in the sheared one-sided form. -/
noncomputable def Al (c x2 x3 h2 : ℝ) : ℝ :=
  (c * (1 / 25) + c * 10000 * x2 - 1 / 25 - 10000 * x3 - 2 * 30000000 * x2)
    + h2 * (c * 10000 - 30000000)

/-- Coefficient of u·k. -/
noncomputable def Be (d c x2 x3 h2 : ℝ) : ℝ :=
  (c ^ 2 * (1 / 25) + c ^ 2 * 10000 * x2 - c * (1 / 25) - c * 10000 * x3 - 2 * c * 30000000 * x2
    - 1 / 25 * d ^ 2 - 10000 * d ^ 2 * x2 + 2 * 30000000 * x2) / d
    + h2 * (c ^ 2 * 10000 - c * 30000000 - 10000 * d ^ 2 + 30000000) / d

/-- Coefficient of k². -/
noncomputable def Ga (c x2 h2 : ℝ) : ℝ := -c * (1 / 25 + 10000 * x2) + h2 * (-c * 10000)

/-- The quadratic form μ(u² + k²) − (Al u² + Be u k + Ga k²). -/
noncomputable def Φ (d c μ x2 x3 h2 u k : ℝ) : ℝ :=
  (μ - Al c x2 x3 h2) * u ^ 2 - Be d c x2 x3 h2 * u * k + (μ - Ga c x2 h2) * k ^ 2

/-- The corner condition: the 2×2 matrix of Φ is positive semidefinite. -/
def CornerOK (d c μ x2 x3 h2 : ℝ) : Prop :=
  0 < μ - Al c x2 x3 h2 ∧
    Be d c x2 x3 h2 ^ 2 ≤ 4 * (μ - Al c x2 x3 h2) * (μ - Ga c x2 h2)

/-- The eight corners. -/
def Corners (d c μ L2 U2 L3 U3 H : ℝ) : Prop :=
  CornerOK d c μ L2 L3 (-H) ∧ CornerOK d c μ L2 L3 H ∧
  CornerOK d c μ L2 U3 (-H) ∧ CornerOK d c μ L2 U3 H ∧
  CornerOK d c μ U2 L3 (-H) ∧ CornerOK d c μ U2 L3 H ∧
  CornerOK d c μ U2 U3 (-H) ∧ CornerOK d c μ U2 U3 H

theorem corner_nonneg {d c μ x2 x3 h2 : ℝ} (h : CornerOK d c μ x2 x3 h2) (u k : ℝ) :
    0 ≤ Φ d c μ x2 x3 h2 u k := by
  obtain ⟨hp, hq⟩ := h
  unfold Φ
  set P := μ - Al c x2 x3 h2
  set Q := Be d c x2 x3 h2
  set R := μ - Ga c x2 h2
  have e : 4 * P * (P * u ^ 2 - Q * u * k + R * k ^ 2)
      = (2 * P * u - Q * k) ^ 2 + (4 * P * R - Q ^ 2) * k ^ 2 := by ring
  have : 0 ≤ 4 * P * (P * u ^ 2 - Q * u * k + R * k ^ 2) := by
    rw [e]; have : 0 ≤ 4 * P * R - Q ^ 2 := by linarith
    positivity
  have h4 : 0 < 4 * P := by linarith
  by_contra hneg; rw [not_le] at hneg
  have := mul_neg_of_pos_of_neg h4 hneg; linarith

/-- Affine interpolation: an affine function nonnegative at both ends of an interval is
nonnegative inside. -/
theorem interp {a b L U x : ℝ} (hL : L ≤ x) (hU : x ≤ U) (h1 : 0 ≤ a + b * L)
    (h2 : 0 ≤ a + b * U) : 0 ≤ a + b * x := by
  rcases le_total 0 b with hb | hb
  · nlinarith [mul_le_mul_of_nonneg_left hL hb]
  · nlinarith [mul_le_mul_of_nonpos_left hU hb]

theorem Φ_x2 (d c μ x2 x3 h2 u k : ℝ) (hd : d ≠ 0) : Φ d c μ x2 x3 h2 u k
    = Φ d c μ 0 x3 h2 u k + (Φ d c μ 1 x3 h2 u k - Φ d c μ 0 x3 h2 u k) * x2 := by
  unfold Φ Al Be Ga; field_simp; ring

theorem Φ_x3 (d c μ x2 x3 h2 u k : ℝ) (hd : d ≠ 0) : Φ d c μ x2 x3 h2 u k
    = Φ d c μ x2 0 h2 u k + (Φ d c μ x2 1 h2 u k - Φ d c μ x2 0 h2 u k) * x3 := by
  unfold Φ Al Be Ga; field_simp; ring

theorem Φ_h2 (d c μ x2 x3 h2 u k : ℝ) (hd : d ≠ 0) : Φ d c μ x2 x3 h2 u k
    = Φ d c μ x2 x3 0 u k + (Φ d c μ x2 x3 1 u k - Φ d c μ x2 x3 0 u k) * h2 := by
  unfold Φ Al Be Ga; field_simp; ring

theorem Φ_nonneg {d c μ L2 U2 L3 U3 H x2 x3 h2 : ℝ} (hd : d ≠ 0)
    (h : Corners d c μ L2 U2 L3 U3 H)
    (hx2 : L2 ≤ x2) (hx2' : x2 ≤ U2) (hx3 : L3 ≤ x3) (hx3' : x3 ≤ U3)
    (hh : -H ≤ h2) (hh' : h2 ≤ H) (u k : ℝ) : 0 ≤ Φ d c μ x2 x3 h2 u k := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := h
  have g : ∀ a b, CornerOK d c μ a b (-H) → CornerOK d c μ a b H →
      0 ≤ Φ d c μ a b h2 u k := fun a b p q => by
    rw [Φ_h2 _ _ _ _ _ _ _ _ hd]
    apply interp hh hh'
    · rw [← Φ_h2 _ _ _ _ _ _ _ _ hd]; exact corner_nonneg p u k
    · rw [← Φ_h2 _ _ _ _ _ _ _ _ hd]; exact corner_nonneg q u k
  have f : ∀ a, 0 ≤ Φ d c μ a L3 h2 u k → 0 ≤ Φ d c μ a U3 h2 u k →
      0 ≤ Φ d c μ a x3 h2 u k := fun a p q => by
    rw [Φ_x3 _ _ _ _ _ _ _ _ hd]
    apply interp hx3 hx3'
    · rw [← Φ_x3 _ _ _ _ _ _ _ _ hd]; exact p
    · rw [← Φ_x3 _ _ _ _ _ _ _ _ hd]; exact q
  rw [Φ_x2 _ _ _ _ _ _ _ _ hd]
  apply interp hx2 hx2'
  · rw [← Φ_x2 _ _ _ _ _ _ _ _ hd]; exact f _ (g _ _ c1 c2) (g _ _ c3 c4)
  · rw [← Φ_x2 _ _ _ _ _ _ _ _ hd]; exact f _ (g _ _ c5 c6) (g _ _ c7 c8)

/-- One-sided bound of the reduced Robertson field in sheared coordinates: base point (x₂, x₃),
perturbation (h₂, h₃) with k = h₃ + c h₂ on the ball d²h₂² + k² ≤ B². -/
theorem shear_onesided {d c μ L2 U2 L3 U3 B x2 x3 h2 k : ℝ} (hd : 0 < d) (hB : 0 ≤ B)
    (hc : Corners d c μ L2 U2 L3 U3 (B / d))
    (hx2 : L2 ≤ x2) (hx2' : x2 ≤ U2) (hx3 : L3 ≤ x3) (hx3' : x3 ≤ U3)
    (hball : d ^ 2 * h2 ^ 2 + k ^ 2 ≤ B ^ 2) :
    d ^ 2 * (robP (x2 + h2) (x3 + (k - c * h2)) - robP x2 x3) * h2
      + ((robQ (x2 + h2) (x3 + (k - c * h2)) - robQ x2 x3)
        + c * (robP (x2 + h2) (x3 + (k - c * h2)) - robP x2 x3)) * k
      ≤ μ * (d ^ 2 * h2 ^ 2 + k ^ 2) := by
  have hh : |h2| ≤ B / d := by
    have : (d * h2) ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg k]
    have h := abs_le_of_sq hB this
    rw [abs_mul, abs_of_pos hd] at h
    rw [le_div_iff₀ hd]; linarith
  rw [abs_le] at hh
  have hΦ := Φ_nonneg hd.ne' hc hx2 hx2' hx3 hx3' hh.1 hh.2 (d * h2) k
  have e : μ * (d ^ 2 * h2 ^ 2 + k ^ 2)
      - (d ^ 2 * (robP (x2 + h2) (x3 + (k - c * h2)) - robP x2 x3) * h2
        + ((robQ (x2 + h2) (x3 + (k - c * h2)) - robQ x2 x3)
          + c * (robP (x2 + h2) (x3 + (k - c * h2)) - robP x2 x3)) * k)
      = Φ d c μ x2 x3 h2 (d * h2) k := by
    unfold Φ Al Be Ga robP robQ; field_simp; ring
  linarith

/-- e^x ≤ 1/(1 − x) for x ≤ 0. -/
theorem exp_le_inv {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  rw [le_div_iff₀ h1]
  have := Real.add_one_le_exp (-x)
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

/-- Sheared norm: componentwise bounds. -/
theorem shear_comp {d c e2 k B : ℝ} (hd : 0 < d) (hB : 0 ≤ B)
    (h : d ^ 2 * e2 ^ 2 + k ^ 2 ≤ B ^ 2) : |e2| ≤ B / d ∧ |k| ≤ B ∧ |k - c * e2| ≤ B + |c| * (B / d) := by
  have h2 : |e2| ≤ B / d := by
    have : (d * e2) ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg k]
    have h := abs_le_of_sq hB this
    rw [abs_mul, abs_of_pos hd] at h
    rw [le_div_iff₀ hd]; linarith
  have h3 : |k| ≤ B := abs_le_of_sq hB (by nlinarith [sq_nonneg e2, sq_nonneg d])
  refine ⟨h2, h3, ?_⟩
  calc |k - c * e2| ≤ |k| + |c * e2| := abs_sub _ _
    _ = |k| + |c| * |e2| := by rw [abs_mul]
    _ ≤ B + |c| * (B / d) := by gcongr

/-- Change of shear: N_{c'}(e) ≤ N_c(e)·(1 + |c' − c|/d). -/
theorem shear_switch {d c c' e2 k R : ℝ} (hd : 0 < d) (hR : 0 ≤ R)
    (h : d ^ 2 * e2 ^ 2 + k ^ 2 ≤ R ^ 2) :
    d ^ 2 * e2 ^ 2 + (k + (c' - c) * e2) ^ 2 ≤ (R * (1 + |c' - c| / d)) ^ 2 := by
  obtain ⟨h2, h3, -⟩ := shear_comp (c := 0) hd hR h
  have m := mink (w := d ^ 2) (d := d) (x2 := e2) (x3 := k + (c' - c) * e2) (g2 := 0)
    (g3 := (c' - c) * e2) (c2 := 0) (c3 := 0) (R := R) hd.le rfl hR (by simpa using h)
  simp only [sub_zero, abs_zero, mul_zero, add_zero] at m
  refine m.trans (pow_le_pow_left₀ (by positivity) ?_ 2)
  rw [abs_mul]
  have : |c' - c| * |e2| ≤ |c' - c| * (R / d) := by gcongr
  calc R + |c' - c| * |e2| ≤ R + |c' - c| * (R / d) := by linarith
    _ = R * (1 + |c' - c| / d) := by field_simp

/-- From the diagonal ball 4900 e₂² + e₃² ≤ Δ² into the sheared norm. -/
theorem start_shear {d c e2 e3 Δ : ℝ} (hd : 0 < d) (hΔ : 0 ≤ Δ)
    (h : 4900 * e2 ^ 2 + e3 ^ 2 ≤ Δ ^ 2) :
    d ^ 2 * e2 ^ 2 + (e3 + c * e2) ^ 2 ≤ (Δ * (d / 70 + 1 + |c| / 70)) ^ 2 := by
  have h2 : |e2| ≤ Δ / 70 := by
    have : (70 * e2) ^ 2 ≤ Δ ^ 2 := by nlinarith [sq_nonneg e3]
    have h := abs_le_of_sq hΔ this
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 70)] at h
    linarith
  have h3 : |e3| ≤ Δ := abs_le_of_sq hΔ (by nlinarith [sq_nonneg e2])
  have hn : 0 ≤ d * |e2| + |e3 + c * e2| := by positivity
  have hsq : d ^ 2 * e2 ^ 2 + (e3 + c * e2) ^ 2 ≤ (d * |e2| + |e3 + c * e2|) ^ 2 := by
    have : d ^ 2 * e2 ^ 2 = (d * |e2|) ^ 2 := by rw [mul_pow, sq_abs]
    rw [this, ← sq_abs (e3 + c * e2)]
    nlinarith [mul_nonneg (mul_nonneg hd.le (abs_nonneg e2)) (abs_nonneg (e3 + c * e2))]
  refine hsq.trans (pow_le_pow_left₀ hn ?_ 2)
  have : |e3 + c * e2| ≤ |e3| + |c| * |e2| := by
    calc |e3 + c * e2| ≤ |e3| + |c * e2| := abs_add_le _ _
      _ = |e3| + |c| * |e2| := by rw [abs_mul]
  have a1 : d * |e2| ≤ d * (Δ / 70) := by gcongr
  have a2 : |c| * |e2| ≤ |c| * (Δ / 70) := by gcongr
  calc d * |e2| + |e3 + c * e2| ≤ d * (Δ / 70) + (Δ + |c| * (Δ / 70)) := by linarith
    _ = Δ * (d / 70 + 1 + |c| / 70) := by ring

/-- One long-horizon cell [t₀, t₀ + h] in the sheared norm d²e₂² + (e₃ + c e₂)², for any field
equal to the reduced Robertson field on the box (contracting one-sided step, μ ≤ 0). -/
theorem cellS (p2 p3 : List ℚ) {d : ℝ} (hd : 0 < d) {P Q : ℝ → ℝ → ℝ}
    (hP : ∀ y2 y3, -1 / 1000 ≤ y2 → y2 ≤ 1 / 1000 → -1 / 10 ≤ y3 → y3 ≤ 11 / 10 →
      P y2 y3 = robP y2 y3 ∧ Q y2 y3 = robQ y2 y3)
    {T t0 h Δ δ ε μ B c L2 U2 L3 U3 e2 e3 c2 c3 : ℝ} {y2 y3 : ℝ → ℝ}
    (ht0 : 0 ≤ t0) (hT : t0 + h ≤ T) (hh : 0 < h)
    (hd2 : ∀ t ∈ Icc 0 T, HasDerivWithinAt y2 (P (y2 t) (y3 t)) (Icc 0 T) t)
    (hd3 : ∀ t ∈ Icc 0 T, HasDerivWithinAt y3 (Q (y2 t) (y3 t)) (Icc 0 T) t)
    (hR2 : ∀ u, |u| ≤ h / 2 → L2 ≤ evalQ p2 u ∧ evalQ p2 u ≤ U2)
    (hR3 : ∀ u, |u| ≤ h / 2 → L3 ≤ evalQ p3 u ∧ evalQ p3 u ≤ U3)
    (hdf2 : ∀ u, |u| ≤ h / 2 → |dEvalQ p2 u - robP (evalQ p2 u) (evalQ p3 u)| ≤ e2)
    (hdf3 : ∀ u, |u| ≤ h / 2 → |dEvalQ p3 u - robQ (evalQ p2 u) (evalQ p3 u)| ≤ e3)
    (hε0 : 0 < ε) (hε : d ^ 2 * e2 ^ 2 + (e3 + |c| * e2) ^ 2 < ε ^ 2)
    (hμ : μ ≤ 0) (hc : Corners d c μ L2 U2 L3 U3 (B / d))
    (hbox : -1 / 1000 ≤ L2 - B / d ∧ U2 + B / d ≤ 1 / 1000 ∧
      -1 / 10 ≤ L3 - (B + |c| * (B / d)) ∧ U3 + (B + |c| * (B / d)) ≤ 11 / 10)
    (hΔ : 0 ≤ Δ)
    (hstart : d ^ 2 * (y2 t0 - c2) ^ 2 + ((y3 t0 + c * y2 t0) - (c3 + c * c2)) ^ 2 ≤ Δ ^ 2)
    (hδ0 : 0 < δ)
    (hδ : Δ + d * |c2 - evalQ p2 (-(h / 2))|
      + |(c3 + c * c2) - (evalQ p3 (-(h / 2)) + c * evalQ p2 (-(h / 2)))| ≤ δ)
    (hB : δ + ε * h ≤ B) :
    ∀ t ∈ Icc t0 (t0 + h),
      d ^ 2 * (y2 t - evalQ p2 (t - (t0 + h / 2))) ^ 2
        + ((y3 t + c * y2 t) - (evalQ p3 (t - (t0 + h / 2)) + c * evalQ p2 (t - (t0 + h / 2)))) ^ 2
      ≤ (δ * Real.exp (μ * (t - t0)) + ε * (t - t0)) ^ 2 := by
  have hB0 : 0 ≤ B := by nlinarith
  have hsub : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0 hT
  have hu : ∀ t ∈ Icc t0 (t0 + h), |t - (t0 + h / 2)| ≤ h / 2 := fun t ht => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  set g2 : ℝ → ℝ := fun t => evalQ p2 (t - (t0 + h / 2)) with hg2
  set g3 : ℝ → ℝ := fun t => evalQ p3 (t - (t0 + h / 2)) with hg3
  -- the field in sheared coordinates
  set Pt : ℝ → ℝ → ℝ := fun a b => P a (b - c * a) with hPt
  set Qt : ℝ → ℝ → ℝ := fun a b => Q a (b - c * a) + c * P a (b - c * a) with hQt
  -- box membership near the approximation
  have hin : ∀ t ∈ Icc t0 (t0 + h), ∀ h2 k : ℝ, |h2| ≤ B / d → |k - c * h2| ≤ B + |c| * (B / d) →
      P (g2 t + h2) (g3 t + (k - c * h2)) = robP (g2 t + h2) (g3 t + (k - c * h2)) ∧
      Q (g2 t + h2) (g3 t + (k - c * h2)) = robQ (g2 t + h2) (g3 t + (k - c * h2)) := by
    intro t ht h2 k hh2 hk
    obtain ⟨a, b⟩ := hR2 _ (hu t ht)
    obtain ⟨a', b'⟩ := hR3 _ (hu t ht)
    rw [abs_le] at hh2 hk
    obtain ⟨k1, k2, k3, k4⟩ := hbox
    exact hP _ _ (by simp only [hg2]; linarith [hh2.1]) (by simp only [hg2]; linarith [hh2.2])
      (by simp only [hg3]; linarith [hk.1]) (by simp only [hg3]; linarith [hk.2])
  have hin0 : ∀ t ∈ Icc t0 (t0 + h), P (g2 t) (g3 t) = robP (g2 t) (g3 t) ∧
      Q (g2 t) (g3 t) = robQ (g2 t) (g3 t) := fun t ht => by
    have := hin t ht 0 0 (by simp; positivity) (by simp; positivity)
    simpa using this
  have key := Checked.Sim.OneSidedNeg.onesided_cell_neg (P := Pt) (Q := Qt) (f2 := y2)
    (f3 := fun t => y3 t + c * y2 t) (g2 := g2) (g3 := fun t => g3 t + c * g2 t)
    (G2 := fun t => dEvalQ p2 (t - (t0 + h / 2)))
    (G3 := fun t => dEvalQ p3 (t - (t0 + h / 2)) + c * dEvalQ p2 (t - (t0 + h / 2)))
    (a := t0) (b := t0 + h) (w := d ^ 2) (μ := μ) (ε := ε) (δ := δ) (B := B)
    (by linarith) (by positivity) hμ hε0 hδ0
    (fun t ht => ((hd2 t (hsub ht)).continuousWithinAt).mono hsub)
    (fun t ht => (((hd3 t (hsub ht)).continuousWithinAt).add
      (((hd2 t (hsub ht)).continuousWithinAt).const_mul c)).mono hsub)
    ((continuous_evalQ p2).comp (continuous_sub_right _)).continuousOn
    ((((continuous_evalQ p3).comp (continuous_sub_right _))).add
      (((continuous_evalQ p2).comp (continuous_sub_right _)).const_mul c)).continuousOn
    (fun t ht => by
      have := (hd2 t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht.2, ht0], by linarith [ht.1, ht.2]⟩)
      simpa [hPt] using this)
    (fun t ht => by
      have m : Icc (0 : ℝ) T ∈ nhdsWithin t (Ici t) :=
        Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht.2, ht0], by linarith [ht.1, ht.2]⟩
      have a3 := (hd3 t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin m
      have a2 := (hd2 t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin m
      have h' : HasDerivWithinAt (fun t => y3 t + c * y2 t)
          (Q (y2 t) (y3 t) + c * P (y2 t) (y3 t)) (Ici t) t := a3.add (a2.const_mul c)
      simpa [hQt] using h')
    (fun t _ => ((hasDerivAt_evalQ p2 _).comp_sub_const t _).hasDerivWithinAt)
    (fun t _ => (((hasDerivAt_evalQ p3 _).comp_sub_const t _).add
      (((hasDerivAt_evalQ p2 _).comp_sub_const t _).const_mul c)).hasDerivWithinAt)
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      obtain ⟨eP, eQ⟩ := hin0 t ht'
      have e1 : Pt (g2 t) (g3 t + c * g2 t) = robP (g2 t) (g3 t) := by
        simp only [hPt, add_sub_cancel_right]; exact eP
      have e2' : Qt (g2 t) (g3 t + c * g2 t) = robQ (g2 t) (g3 t) + c * robP (g2 t) (g3 t) := by
        simp only [hQt, add_sub_cancel_right]; rw [eP, eQ]
      rw [e1, e2']
      have a := hdf2 _ (hu t ht')
      have b := hdf3 _ (hu t ht')
      set D2 := dEvalQ p2 (t - (t0 + h / 2)) - robP (g2 t) (g3 t)
      set D3 := dEvalQ p3 (t - (t0 + h / 2)) - robQ (g2 t) (g3 t)
      have hD : |D3 + c * D2| ≤ e3 + |c| * e2 := by
        calc |D3 + c * D2| ≤ |D3| + |c * D2| := abs_add_le _ _
          _ = |D3| + |c| * |D2| := by rw [abs_mul]
          _ ≤ e3 + |c| * e2 := by gcongr
      have s1 := sq_le_of_abs a
      have s2 := sq_le_of_abs hD
      have e3' : dEvalQ p3 (t - (t0 + h / 2)) + c * dEvalQ p2 (t - (t0 + h / 2))
          - (robQ (g2 t) (g3 t) + c * robP (g2 t) (g3 t)) = D3 + c * D2 := by
        simp only [D2, D3]; ring
      rw [e3']
      have : d ^ 2 * D2 ^ 2 ≤ d ^ 2 * e2 ^ 2 := mul_le_mul_of_nonneg_left s1 (by positivity)
      linarith)
    (fun t ht z2 z3 hz => by
      have ht' := Ico_subset_Icc_self ht
      set h2 := z2 - g2 t
      set k := z3 - (g3 t + c * g2 t)
      have hz' : d ^ 2 * h2 ^ 2 + k ^ 2 ≤ B ^ 2 := hz
      obtain ⟨b2, -, b3⟩ := shear_comp (c := c) hd hB0 hz'
      have ez2 : z2 = g2 t + h2 := by simp only [h2]; ring
      have ez3 : z3 - c * z2 = g3 t + (k - c * h2) := by simp only [h2, k]; ring
      obtain ⟨eP, eQ⟩ := hin t ht' h2 k b2 b3
      obtain ⟨eP0, eQ0⟩ := hin0 t ht'
      have r1 : Pt z2 z3 = robP (g2 t + h2) (g3 t + (k - c * h2)) := by
        simp only [hPt]; rw [ez3, ← eP, ← ez2]
      have r2 : Qt z2 z3 = robQ (g2 t + h2) (g3 t + (k - c * h2))
          + c * robP (g2 t + h2) (g3 t + (k - c * h2)) := by
        simp only [hQt]; rw [ez3, ← eP, ← eQ, ← ez2]
      have r3 : Pt (g2 t) (g3 t + c * g2 t) = robP (g2 t) (g3 t) := by
        simp only [hPt, add_sub_cancel_right]; exact eP0
      have r4 : Qt (g2 t) (g3 t + c * g2 t) = robQ (g2 t) (g3 t) + c * robP (g2 t) (g3 t) := by
        simp only [hQt, add_sub_cancel_right]; rw [eP0, eQ0]
      rw [r1, r2, r3, r4]
      obtain ⟨a, b⟩ := hR2 _ (hu t ht')
      obtain ⟨a', b'⟩ := hR3 _ (hu t ht')
      have hs := shear_onesided (x2 := g2 t) (x3 := g3 t) (h2 := h2) (k := k) hd hB0 hc a b a' b' hz'
      linarith)
    (by
      have e1 : t0 - (t0 + h / 2) = -(h / 2) := by ring
      simp only [hg2, hg3, e1]
      have hm := mink (w := d ^ 2) (d := d) (x2 := y2 t0) (x3 := y3 t0 + c * y2 t0) (g2 := c2)
        (g3 := c3 + c * c2) (c2 := evalQ p2 (-(h / 2)))
        (c3 := evalQ p3 (-(h / 2)) + c * evalQ p2 (-(h / 2))) (R := Δ) hd.le rfl hΔ hstart
      refine hm.trans ?_
      have : 0 ≤ Δ + d * |c2 - evalQ p2 (-(h / 2))|
          + |(c3 + c * c2) - (evalQ p3 (-(h / 2)) + c * evalQ p2 (-(h / 2)))| := by positivity
      exact pow_le_pow_left₀ this hδ 2)
    (by rw [show t0 + h - t0 = h by ring]; exact hB)
  intro t ht
  exact key t ht

/-- One cell step with a change of shear c → c' at its end: from a sheared ball around (c₂, c₃)
at t₀ to a sheared ball around (n₂, n₃) at t₀ + h; the solution stays in the box on the cell. -/
theorem stepS (p2 p3 : List ℚ) {d : ℝ} (hd : 0 < d) {P Q : ℝ → ℝ → ℝ}
    (hP : ∀ y2 y3, -1 / 1000 ≤ y2 → y2 ≤ 1 / 1000 → -1 / 10 ≤ y3 → y3 ≤ 11 / 10 →
      P y2 y3 = robP y2 y3 ∧ Q y2 y3 = robQ y2 y3)
    {T t0 h Δ δ ε μ B c c' L2 U2 L3 U3 e2 e3 c2 c3 n2 n3 Rend Δ' : ℝ} {y2 y3 : ℝ → ℝ}
    (ht0 : 0 ≤ t0) (hT : t0 + h ≤ T) (hh : 0 < h)
    (hd2 : ∀ t ∈ Icc 0 T, HasDerivWithinAt y2 (P (y2 t) (y3 t)) (Icc 0 T) t)
    (hd3 : ∀ t ∈ Icc 0 T, HasDerivWithinAt y3 (Q (y2 t) (y3 t)) (Icc 0 T) t)
    (hR2 : ∀ u, |u| ≤ h / 2 → L2 ≤ evalQ p2 u ∧ evalQ p2 u ≤ U2)
    (hR3 : ∀ u, |u| ≤ h / 2 → L3 ≤ evalQ p3 u ∧ evalQ p3 u ≤ U3)
    (hdf2 : ∀ u, |u| ≤ h / 2 → |dEvalQ p2 u - robP (evalQ p2 u) (evalQ p3 u)| ≤ e2)
    (hdf3 : ∀ u, |u| ≤ h / 2 → |dEvalQ p3 u - robQ (evalQ p2 u) (evalQ p3 u)| ≤ e3)
    (hε0 : 0 < ε) (hε : d ^ 2 * e2 ^ 2 + (e3 + |c| * e2) ^ 2 < ε ^ 2)
    (hμ : μ ≤ 0) (hc : Corners d c μ L2 U2 L3 U3 (B / d))
    (hbox : -1 / 1000 ≤ L2 - B / d ∧ U2 + B / d ≤ 1 / 1000 ∧
      -1 / 10 ≤ L3 - (B + |c| * (B / d)) ∧ U3 + (B + |c| * (B / d)) ≤ 11 / 10)
    (hΔ : 0 ≤ Δ)
    (hstart : d ^ 2 * (y2 t0 - c2) ^ 2 + ((y3 t0 + c * y2 t0) - (c3 + c * c2)) ^ 2 ≤ Δ ^ 2)
    (hδ0 : 0 < δ)
    (hδ : Δ + d * |c2 - evalQ p2 (-(h / 2))|
      + |(c3 + c * c2) - (evalQ p3 (-(h / 2)) + c * evalQ p2 (-(h / 2)))| ≤ δ)
    (hB : δ + ε * h ≤ B)
    (hRend : δ / (1 - μ * h) + ε * h ≤ Rend)
    (hn : (Rend + d * |evalQ p2 (h / 2) - n2|
      + |(evalQ p3 (h / 2) + c * evalQ p2 (h / 2)) - (n3 + c * n2)|) * (1 + |c' - c| / d) ≤ Δ') :
    (∀ t ∈ Icc t0 (t0 + h), -1 / 1000 ≤ y2 t ∧ y2 t ≤ 1 / 1000 ∧ -1 / 10 ≤ y3 t ∧ y3 t ≤ 11 / 10) ∧
    d ^ 2 * (y2 (t0 + h) - n2) ^ 2 + ((y3 (t0 + h) + c' * y2 (t0 + h)) - (n3 + c' * n2)) ^ 2
      ≤ Δ' ^ 2 := by
  have hall := cellS p2 p3 hd hP ht0 hT hh hd2 hd3 hR2 hR3 hdf2 hdf3 hε0 hε hμ hc hbox hΔ hstart
    hδ0 hδ hB
  have hB0 : 0 ≤ B := by nlinarith
  have hRle : ∀ t ∈ Icc t0 (t0 + h), 0 ≤ δ * Real.exp (μ * (t - t0)) + ε * (t - t0) ∧
      δ * Real.exp (μ * (t - t0)) + ε * (t - t0) ≤ B := fun t ht => by
    have h1 : Real.exp (μ * (t - t0)) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hμ (by linarith [ht.1]))
    have h2 : 0 < Real.exp (μ * (t - t0)) := Real.exp_pos _
    constructor
    · have : 0 ≤ ε * (t - t0) := mul_nonneg hε0.le (by linarith [ht.1])
      positivity
    · have a : δ * Real.exp (μ * (t - t0)) ≤ δ := by nlinarith
      have b : ε * (t - t0) ≤ ε * h := by nlinarith [ht.2]
      linarith
  refine ⟨fun t ht => ?_, ?_⟩
  · have hu : |t - (t0 + h / 2)| ≤ h / 2 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hb := (hall t ht).trans (pow_le_pow_left₀ (hRle t ht).1 (hRle t ht).2 2)
    obtain ⟨b2, -, b3⟩ := shear_comp (c := c) hd hB0 hb
    obtain ⟨a, b⟩ := hR2 _ hu
    obtain ⟨a', b'⟩ := hR3 _ hu
    have e : (y3 t + c * y2 t - (evalQ p3 (t - (t0 + h / 2)) + c * evalQ p2 (t - (t0 + h / 2))))
        - c * (y2 t - evalQ p2 (t - (t0 + h / 2))) = y3 t - evalQ p3 (t - (t0 + h / 2)) := by ring
    rw [e] at b3
    rw [abs_le] at b2 b3
    obtain ⟨x1, x2, x3, x4⟩ := hbox
    exact ⟨by linarith [b2.1], by linarith [b2.2], by linarith [b3.1], by linarith [b3.2]⟩
  · have hc' := hall (t0 + h) ⟨by linarith, le_rfl⟩
    rw [show t0 + h - (t0 + h / 2) = h / 2 by ring, show t0 + h - t0 = h by ring] at hc'
    have hμh : μ * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hμ hh.le
    have hexp := exp_le_inv hμh
    have hR : δ * Real.exp (μ * h) + ε * h ≤ Rend := by
      have : δ * Real.exp (μ * h) ≤ δ * (1 / (1 - μ * h)) := mul_le_mul_of_nonneg_left hexp hδ0.le
      have e : δ * (1 / (1 - μ * h)) = δ / (1 - μ * h) := by ring
      linarith
    have hR0 : 0 ≤ δ * Real.exp (μ * h) + ε * h := by
      have := Real.exp_pos (μ * h); positivity
    have h1 := hc'.trans (pow_le_pow_left₀ hR0 hR 2)
    have hRend0 : 0 ≤ Rend := hR0.trans hR
    have hm := mink (w := d ^ 2) (d := d) (x2 := y2 (t0 + h))
      (x3 := y3 (t0 + h) + c * y2 (t0 + h)) (g2 := evalQ p2 (h / 2))
      (g3 := evalQ p3 (h / 2) + c * evalQ p2 (h / 2)) (c2 := n2) (c3 := n3 + c * n2)
      (R := Rend) hd.le rfl hRend0 h1
    have hR1 : 0 ≤ Rend + d * |evalQ p2 (h / 2) - n2|
        + |(evalQ p3 (h / 2) + c * evalQ p2 (h / 2)) - (n3 + c * n2)| := by positivity
    have hs := shear_switch (c := c) (c' := c') hd hR1 hm
    have e : y3 (t0 + h) + c * y2 (t0 + h) - (n3 + c * n2) + (c' - c) * (y2 (t0 + h) - n2)
        = y3 (t0 + h) + c' * y2 (t0 + h) - (n3 + c' * n2) := by ring
    rw [e] at hs
    have : 0 ≤ (Rend + d * |evalQ p2 (h / 2) - n2|
      + |(evalQ p3 (h / 2) + c * evalQ p2 (h / 2)) - (n3 + c * n2)|) * (1 + |c' - c| / d) := by
      positivity
    exact hs.trans (pow_le_pow_left₀ this hn 2)

end Checked.Sim.RobShear

#print axioms Checked.Sim.RobShear.shear_onesided
#print axioms Checked.Sim.RobShear.shear_switch
#print axioms Checked.Sim.RobShear.start_shear
#print axioms Checked.Sim.RobShear.stepS
