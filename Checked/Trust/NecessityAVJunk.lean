import Checked.Trust.NecessityAVFar

/-! Lower bounds for the chi-square of `Checked.Data.Moresco16` that do not assume the squared expansion
factor nonnegative (helper lemmas of `Checked.Trust.NecessityAV`, run 2026-11-19T0028Z). The square root
of a negative number is zero in Lean; the bound of `Moresco16Min.box_boundQ` still holds on a box where
each squared factor stays above minus the square of its tangent point, and a row whose squared factor
is at most zero contributes its whole term. -/

namespace Checked.Trust.NecessityAV
open Checked.Data.Moresco16 Checked.Data.Moresco16Lower Checked.Data.Moresco16Min

theorem term_ge (H0 e H σ : ℝ) (hσ : 0 < σ) :
    e / σ ^ 2 * H0 ^ 2 - 2 * (H * Real.sqrt e / σ ^ 2) * H0 + H ^ 2 / σ ^ 2 ≤
      (H0 * Real.sqrt e - H) ^ 2 / σ ^ 2 := by
  have hq : e ≤ Real.sqrt e ^ 2 := by
    rcases le_total 0 e with h | h
    · rw [Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero'.2 h]; nlinarith
  have key : (H0 * Real.sqrt e - H) ^ 2 / σ ^ 2 -
      (e / σ ^ 2 * H0 ^ 2 - 2 * (H * Real.sqrt e / σ ^ 2) * H0 + H ^ 2 / σ ^ 2) =
      H0 ^ 2 * (Real.sqrt e ^ 2 - e) / σ ^ 2 := by
    field_simp; ring
  have : 0 ≤ H0 ^ 2 * (Real.sqrt e ^ 2 - e) / σ ^ 2 := by
    apply div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (sq_nonneg _)
  linarith

theorem sigma_pos (i : Fin 30) : 0 < (m16Table i).2.2 := by
  fin_cases i <;> norm_num [m16Table]

/-- The chi-square is at least the quadratic in H₀ with the squared factors in place of the squares
of their square roots (no sign condition). -/
theorem chi_ge_quad (H0 m l : ℝ) :
    alf m l * H0 ^ 2 - 2 * ((∑ i, (m16Table i).2.1 * Real.sqrt (e2OL m l (m16Table i).1) /
      (m16Table i).2.2 ^ 2) + 73 / 2.4 ^ 2) * H0 + gam ≤ chiSqOL H0 m l := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 30))) fun i _ =>
    term_ge H0 (e2OL m l (m16Table i).1) (m16Table i).2.1 (m16Table i).2.2 (sigma_pos i)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.mul_sum] at h
  unfold chiSqOL alf gam
  set A := ∑ i, e2OL m l (m16Table i).1 / (m16Table i).2.2 ^ 2
  set B := ∑ i, (m16Table i).2.1 * Real.sqrt (e2OL m l (m16Table i).1) / (m16Table i).2.2 ^ 2
  set G := ∑ i, (m16Table i).2.1 ^ 2 / (m16Table i).2.2 ^ 2
  set S := ∑ i, (H0 * Real.sqrt (e2OL m l (m16Table i).1) - (m16Table i).2.1) ^ 2 /
    (m16Table i).2.2 ^ 2
  have hp : (A + 1 / 2.4 ^ 2) * H0 ^ 2 - 2 * (B + 73 / 2.4 ^ 2) * H0 + (G + 73 ^ 2 / 2.4 ^ 2) =
      (A * H0 ^ 2 - 2 * B * H0 + G) + (H0 - 73) ^ 2 / 2.4 ^ 2 := by ring
  have h' : A * H0 ^ 2 - 2 * B * H0 + G ≤ S := by linarith [h]
  linarith [h', hp]

theorem tangent_j {y s : ℝ} (hy : 0 ≤ y + s ^ 2) (hs : 0 < s) :
    Real.sqrt y ≤ (y + s ^ 2) / (2 * s) := by
  rcases le_total 0 y with h | h
  · exact sqrt_le_tangent h hs
  · rw [Real.sqrt_eq_zero'.2 h]; positivity

theorem ge_of_point_j (s : Fin 30 → ℝ) (hs : ∀ i, 0 < s i) (c H0 m l : ℝ)
    (hneg : ∀ i, 0 ≤ e2OL m l (m16Table i).1 + s i ^ 2) (hgc : c < gam)
    (h : Lf s m l ^ 2 ≤ alf m l * (gam - c)) :
    c ≤ chiSqOL H0 m l := by
  set β := (∑ i, (m16Table i).2.1 * Real.sqrt (e2OL m l (m16Table i).1) /
          (m16Table i).2.2 ^ 2) + 73 / 2.4 ^ 2 with hβ
  have hb0 : 0 ≤ β := by
    have : 0 ≤ ∑ i, (m16Table i).2.1 * Real.sqrt (e2OL m l (m16Table i).1) /
        (m16Table i).2.2 ^ 2 :=
      Finset.sum_nonneg fun i _ => div_nonneg (mul_nonneg (H_nonneg i) (Real.sqrt_nonneg _))
        (sq_nonneg _)
    rw [hβ]; positivity
  have hbL : β ≤ Lf s m l := by
    rw [hβ]; unfold Lf
    gcongr with i
    rw [show (m16Table i).2.1 * Real.sqrt (e2OL m l (m16Table i).1) / (m16Table i).2.2 ^ 2 =
      wt i * Real.sqrt (e2OL m l (m16Table i).1) by unfold wt; ring]
    exact mul_le_mul_of_nonneg_left (tangent_j (hneg i) (hs i))
      (div_nonneg (H_nonneg i) (sq_nonneg _))
  have hL : 0 < Lf s m l := by
    unfold Lf
    have : 0 ≤ ∑ i, wt i * ((e2OL m l (m16Table i).1 + s i ^ 2) / (2 * s i)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (div_nonneg (H_nonneg i) (sq_nonneg _))
        (div_nonneg (hneg i) (by linarith [hs i]))
    positivity
  have hα : 0 < alf m l := by
    have h1 : 0 < alf m l * (gam - c) := lt_of_lt_of_le (by positivity) h
    exact pos_of_mul_pos_left h1 (by linarith) |>.trans_le' le_rfl |> fun x => by
      rcases lt_or_ge 0 (alf m l) with h2 | h2
      · exact h2
      · nlinarith
  have hsq : β ^ 2 ≤ Lf s m l ^ 2 := pow_le_pow_left₀ hb0 hbL 2
  have := ge_of_disc (α := alf m l) (β := β) (γ := gam) (c := c) (H0 := H0) hα (le_trans hsq h)
  have hq := chi_ge_quad H0 m l
  rw [← hβ] at hq
  linarith

/-- An affine function nonnegative at the four corners of a box is nonnegative on it. -/
theorem aff_box {p q r m0 m1 l0 l1 m l : ℝ} (hm0 : m0 ≤ m) (hm1 : m ≤ m1) (hl0 : l0 ≤ l)
    (hl1 : l ≤ l1) (c00 : 0 ≤ p + q * m0 + r * l0) (c01 : 0 ≤ p + q * m0 + r * l1)
    (c10 : 0 ≤ p + q * m1 + r * l0) (c11 : 0 ≤ p + q * m1 + r * l1) :
    0 ≤ p + q * m + r * l := by
  rcases le_total 0 q with hq | hq <;> rcases le_total 0 r with hr | hr
  · nlinarith [mul_nonneg hq (sub_nonneg.2 hm0), mul_nonneg hr (sub_nonneg.2 hl0)]
  · nlinarith [mul_nonneg hq (sub_nonneg.2 hm0), mul_nonneg_of_nonpos_of_nonpos hr (sub_nonpos.2 hl1)]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos hq (sub_nonpos.2 hm1), mul_nonneg hr (sub_nonneg.2 hl0)]
  · nlinarith [mul_nonneg_of_nonpos_of_nonpos hq (sub_nonpos.2 hm1),
      mul_nonneg_of_nonpos_of_nonpos hr (sub_nonpos.2 hl1)]

/-- The corner checks of a box without the sign condition, as one decidable proposition over ℚ
(helper). -/
def BoxOKJ (s : Fin 30 → ℚ) (c m0 m1 l0 l1 : ℚ) : Prop :=
  BoxOK s c m0 m1 l0 l1 ∧ c < gamQ ∧ ∀ i, 0 ≤ yQ (tQ i).1 m0 l0 + s i ^ 2 ∧
    0 ≤ yQ (tQ i).1 m0 l1 + s i ^ 2 ∧ 0 ≤ yQ (tQ i).1 m1 l0 + s i ^ 2 ∧
    0 ≤ yQ (tQ i).1 m1 l1 + s i ^ 2

instance (s : Fin 30 → ℚ) (c m0 m1 l0 l1 : ℚ) : Decidable (BoxOKJ s c m0 m1 l0 l1) := by
  unfold BoxOKJ; infer_instance

/-- A box closed by an exact rational certificate, with no sign condition on the squared factors. -/
theorem box_boundQJ (s : Fin 30 → ℚ) (c m0 m1 l0 l1 : ℚ) (hok : BoxOKJ s c m0 m1 l0 l1)
    (H0 m l : ℝ) (hm0 : (m0 : ℝ) ≤ m) (hm1 : m ≤ m1) (hl0 : (l0 : ℝ) ≤ l) (hl1 : l ≤ l1) :
    (c : ℝ) ≤ chiSqOL H0 m l := by
  obtain ⟨⟨hs, c00, c01, c10, c11⟩, hgc, hc⟩ := hok
  have hsR : ∀ i, 0 < (s i : ℝ) := fun i => by exact_mod_cast hs i
  have hneg : ∀ i, 0 ≤ e2OL m l (m16Table i).1 + (s i : ℝ) ^ 2 := by
    intro i
    obtain ⟨d00, d01, d10, d11⟩ := hc i
    have cast : ∀ a b : ℚ, (((yQ (tQ i).1 a b + s i ^ 2 : ℚ)) : ℝ) =
        e2OL (a : ℝ) (b : ℝ) (m16Table i).1 + (s i : ℝ) ^ 2 := by
      intro a b; rw [tQ_cast i]; simp only [e2OL, yQ]; push_cast; ring
    have k : ∀ a b : ℝ, e2OL a b (m16Table i).1 + (s i : ℝ) ^ 2 =
        (e2OL 0 0 (m16Table i).1 + (s i : ℝ) ^ 2) + (e2OL 1 0 (m16Table i).1 - e2OL 0 0 (m16Table i).1) * a
          + (e2OL 0 1 (m16Table i).1 - e2OL 0 0 (m16Table i).1) * b := by
      intro a b; rw [e2OL_affine a b]; ring
    have e00 := cast m0 l0; have e01 := cast m0 l1; have e10 := cast m1 l0; have e11 := cast m1 l1
    have f00 : (0 : ℝ) ≤ ((yQ (tQ i).1 m0 l0 + s i ^ 2 : ℚ) : ℝ) := by exact_mod_cast d00
    have f01 : (0 : ℝ) ≤ ((yQ (tQ i).1 m0 l1 + s i ^ 2 : ℚ) : ℝ) := by exact_mod_cast d01
    have f10 : (0 : ℝ) ≤ ((yQ (tQ i).1 m1 l0 + s i ^ 2 : ℚ) : ℝ) := by exact_mod_cast d10
    have f11 : (0 : ℝ) ≤ ((yQ (tQ i).1 m1 l1 + s i ^ 2 : ℚ) : ℝ) := by exact_mod_cast d11
    rw [e00, k] at f00; rw [e01, k] at f01; rw [e10, k] at f10; rw [e11, k] at f11
    rw [k]
    exact aff_box hm0 hm1 hl0 hl1 f00 f01 f10 f11
  apply ge_of_point_j (fun i => (s i : ℝ)) hsR c H0 m l hneg
  · rw [gam_cast]; exact_mod_cast hgc
  · have key : ∀ m l, Lf (fun i => (s i : ℝ)) m l ^ 2 ≤ alf m l * (gam - c) ↔
        (Lf (fun i => (s i : ℝ)) 0 0 + (Lf (fun i => (s i : ℝ)) 1 0 - Lf (fun i => (s i : ℝ)) 0 0) * m
          + (Lf (fun i => (s i : ℝ)) 0 1 - Lf (fun i => (s i : ℝ)) 0 0) * l) ^ 2 ≤
          alf 0 0 * (gam - c) + ((alf 1 0 - alf 0 0) * (gam - c)) * m
            + ((alf 0 1 - alf 0 0) * (gam - c)) * l := by
      intro m l
      rw [Lf_affine _ m l, alf_affine m l]
      constructor <;> intro h <;> linarith
    have g : ∀ a b : ℚ, LfQ s a b ^ 2 ≤ alfQ a b * (gamQ - c) →
        Lf (fun i => (s i : ℝ)) a b ^ 2 ≤ alf a b * (gam - c) := by
      intro a b hab
      rw [Lf_cast, alf_cast, gam_cast]; exact_mod_cast hab
    have g00 := (key _ _).1 (g _ _ c00); have g01 := (key _ _).1 (g _ _ c01)
    have g10 := (key _ _).1 (g _ _ c10); have g11 := (key _ _).1 (g _ _ c11)
    rw [key]
    exact box_convex hm0 hm1 hl0 hl1 g00 g01 g10 g11

/-- A row whose squared factor is at most zero contributes its whole term (helper). -/
theorem neg_row (H0 m l : ℝ) (k : Fin 30) (hk : e2OL m l (m16Table k).1 ≤ 0)
    (hc : (29933 / 2000 : ℝ) ≤ (m16Table k).2.1 ^ 2 / (m16Table k).2.2 ^ 2) :
    (((29933 / 2000 : ℚ)) : ℝ) ≤ chiSqOL H0 m l := by
  set f : Fin 30 → ℝ := fun j =>
    (H0 * Real.sqrt (e2OL m l (m16Table j).1) - (m16Table j).2.1) ^ 2 / (m16Table j).2.2 ^ 2 with hf
  have hS : f k ≤ ∑ j, f j :=
    Finset.single_le_sum (fun j _ => by rw [hf]; positivity) (Finset.mem_univ k)
  have hchi : chiSqOL H0 m l = (∑ j, f j) + (H0 - 73) ^ 2 / 2.4 ^ 2 := rfl
  have hfk : f k = (m16Table k).2.1 ^ 2 / (m16Table k).2.2 ^ 2 := by
    rw [hf]; dsimp only; rw [Real.sqrt_eq_zero'.2 hk]; ring
  have hP0 : 0 ≤ (H0 - 73) ^ 2 / 2.4 ^ 2 := by positivity
  rw [hchi]; push_cast
  linarith

/-- The squared factors nonnegative at the four corners of a box, over ℚ (helper). -/
def CornersOK (m0 m1 l0 l1 : ℚ) : Prop :=
  ∀ i, 0 ≤ yQ (tQ i).1 m0 l0 ∧ 0 ≤ yQ (tQ i).1 m0 l1 ∧ 0 ≤ yQ (tQ i).1 m1 l0 ∧ 0 ≤ yQ (tQ i).1 m1 l1

instance (m0 m1 l0 l1 : ℚ) : Decidable (CornersOK m0 m1 l0 l1) := by
  unfold CornersOK; infer_instance

/-- Every squared factor is nonnegative on a box whose corners pass `CornersOK` (helper). -/
theorem hy_boxQ (m0 m1 l0 l1 : ℚ) (hc : CornersOK m0 m1 l0 l1) (m l : ℝ) (hm0 : (m0 : ℝ) ≤ m)
    (hm1 : m ≤ m1) (hl0 : (l0 : ℝ) ≤ l) (hl1 : l ≤ l1) : ∀ i, 0 ≤ e2OL m l (m16Table i).1 := by
  intro i
  obtain ⟨d00, d01, d10, d11⟩ := hc i
  have cast : ∀ a b : ℚ, (((yQ (tQ i).1 a b : ℚ)) : ℝ) = e2OL (a : ℝ) (b : ℝ) (m16Table i).1 := by
    intro a b; rw [tQ_cast i]; simp only [e2OL, yQ]; push_cast; ring
  have k : ∀ a b : ℝ, e2OL a b (m16Table i).1 =
      e2OL 0 0 (m16Table i).1 + (e2OL 1 0 (m16Table i).1 - e2OL 0 0 (m16Table i).1) * a
        + (e2OL 0 1 (m16Table i).1 - e2OL 0 0 (m16Table i).1) * b := by
    intro a b; rw [e2OL_affine a b]; ring
  have f00 : (0 : ℝ) ≤ ((yQ (tQ i).1 m0 l0 : ℚ) : ℝ) := by exact_mod_cast d00
  have f01 : (0 : ℝ) ≤ ((yQ (tQ i).1 m0 l1 : ℚ) : ℝ) := by exact_mod_cast d01
  have f10 : (0 : ℝ) ≤ ((yQ (tQ i).1 m1 l0 : ℚ) : ℝ) := by exact_mod_cast d10
  have f11 : (0 : ℝ) ≤ ((yQ (tQ i).1 m1 l1 : ℚ) : ℝ) := by exact_mod_cast d11
  rw [cast, k] at f00 f01 f10 f11
  rw [k]
  exact aff_box hm0 hm1 hl0 hl1 f00 f01 f10 f11

end Checked.Trust.NecessityAV
