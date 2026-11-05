import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Cast.Order
import Checked.Data.Moresco16Lower

/-!
# Tools for the certified minimum of `Checked.Data.Moresco16.chiSqOL` (helper lemmas)

Promoted unchanged from `Work/Data/Moresco16MinTools.lean` (run 2026-11-05T0628Z) in run
2026-11-05T1028Z. Per box [m₀, m₁] × [l₀, l₁] of (Ω_m, Ω_Λ) and per rational vector s > 0:
β ≤ `Lf s m l` (tangent bound of each √E²); `Lf s` and `alf` are affine in (m, l), so the inequality
`Lf s ² ≤ alf · (gam − c)` at the four corners gives it on the box (`box_convex`), and then c ≤ χ²
for every H₀ (`ge_of_disc`). `box_bound` packages this; `box_vacuous` closes a box on which some
E²(zᵢ) is negative everywhere.
-/

namespace Checked.Data.Moresco16Min
open Checked.Data.Moresco16 Checked.Data.Moresco16Lower

/-- H_i/σ_i² (helper). -/
noncomputable def wt (i : Fin 30) : ℝ := (m16Table i).2.1 / (m16Table i).2.2 ^ 2

/-- Tangent upper bound of β = Σ H_i √E²_i/σ_i² + 73/2.4² (helper). -/
noncomputable def Lf (s : Fin 30 → ℝ) (m l : ℝ) : ℝ :=
  (∑ i, wt i * ((e2OL m l (m16Table i).1 + s i ^ 2) / (2 * s i))) + 73 / 2.4 ^ 2

/-- α = Σ E²_i/σ_i² + 1/2.4² (helper). -/
noncomputable def alf (m l : ℝ) : ℝ :=
  (∑ i, e2OL m l (m16Table i).1 / (m16Table i).2.2 ^ 2) + 1 / 2.4 ^ 2

/-- γ = Σ H_i²/σ_i² + 73²/2.4² (helper). -/
noncomputable def gam : ℝ := (∑ i, (m16Table i).2.1 ^ 2 / (m16Table i).2.2 ^ 2) + 73 ^ 2 / 2.4 ^ 2

theorem H_nonneg (i : Fin 30) : 0 ≤ (m16Table i).2.1 := by
  fin_cases i <;> norm_num [m16Table]

theorem e2OL_affine (m l z : ℝ) :
    e2OL m l z = e2OL 0 0 z + m * (e2OL 1 0 z - e2OL 0 0 z) + l * (e2OL 0 1 z - e2OL 0 0 z) := by
  unfold e2OL; ring

theorem Lf_affine (s : Fin 30 → ℝ) (m l : ℝ) :
    Lf s m l = Lf s 0 0 + m * (Lf s 1 0 - Lf s 0 0) + l * (Lf s 0 1 - Lf s 0 0) := by
  unfold Lf
  have h : ∀ i, wt i * ((e2OL m l (m16Table i).1 + s i ^ 2) / (2 * s i)) =
      wt i * ((e2OL 0 0 (m16Table i).1 + s i ^ 2) / (2 * s i))
      + m * (wt i * ((e2OL 1 0 (m16Table i).1 + s i ^ 2) / (2 * s i))
          - wt i * ((e2OL 0 0 (m16Table i).1 + s i ^ 2) / (2 * s i)))
      + l * (wt i * ((e2OL 0 1 (m16Table i).1 + s i ^ 2) / (2 * s i))
          - wt i * ((e2OL 0 0 (m16Table i).1 + s i ^ 2) / (2 * s i))) := by
    intro i; rw [e2OL_affine m l]; ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

theorem alf_affine (m l : ℝ) :
    alf m l = alf 0 0 + m * (alf 1 0 - alf 0 0) + l * (alf 0 1 - alf 0 0) := by
  unfold alf
  have h : ∀ i, e2OL m l (m16Table i).1 / (m16Table i).2.2 ^ 2 =
      e2OL 0 0 (m16Table i).1 / (m16Table i).2.2 ^ 2
      + m * (e2OL 1 0 (m16Table i).1 / (m16Table i).2.2 ^ 2
          - e2OL 0 0 (m16Table i).1 / (m16Table i).2.2 ^ 2)
      + l * (e2OL 0 1 (m16Table i).1 / (m16Table i).2.2 ^ 2
          - e2OL 0 0 (m16Table i).1 / (m16Table i).2.2 ^ 2) := by
    intro i; rw [e2OL_affine m l]; ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- If Lf s ² ≤ alf · (gam − c) at (m, l) and every E² ≥ 0 there, then c ≤ χ² for every H₀. -/
theorem ge_of_point (s : Fin 30 → ℝ) (hs : ∀ i, 0 < s i) (c H0 m l : ℝ)
    (hy : ∀ i, 0 ≤ e2OL m l (m16Table i).1) (h : Lf s m l ^ 2 ≤ alf m l * (gam - c)) :
    c ≤ chiSqOL H0 m l := by
  rw [chiSqOL_eq H0 m l hy]
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
    exact mul_le_mul_of_nonneg_left (sqrt_le_tangent (hy i) (hs i))
      (div_nonneg (H_nonneg i) (sq_nonneg _))
  have hα : 0 < alf m l := by
    unfold alf
    have : 0 ≤ ∑ i, e2OL m l (m16Table i).1 / (m16Table i).2.2 ^ 2 :=
      Finset.sum_nonneg fun i _ => div_nonneg (hy i) (sq_nonneg _)
    positivity
  have hsq : β ^ 2 ≤ Lf s m l ^ 2 := pow_le_pow_left₀ hb0 hbL 2
  have := ge_of_disc (α := alf m l) (β := β) (γ := gam) (c := c) (H0 := H0) hα
    (le_trans hsq h)
  unfold alf gam at this
  linarith

/-- A box closed by corner checks. -/
theorem box_bound (s : Fin 30 → ℝ) (hs : ∀ i, 0 < s i) (c m0 m1 l0 l1 H0 m l : ℝ)
    (hm0 : m0 ≤ m) (hm1 : m ≤ m1) (hl0 : l0 ≤ l) (hl1 : l ≤ l1)
    (hy : ∀ i, 0 ≤ e2OL m l (m16Table i).1)
    (c00 : Lf s m0 l0 ^ 2 ≤ alf m0 l0 * (gam - c))
    (c01 : Lf s m0 l1 ^ 2 ≤ alf m0 l1 * (gam - c))
    (c10 : Lf s m1 l0 ^ 2 ≤ alf m1 l0 * (gam - c))
    (c11 : Lf s m1 l1 ^ 2 ≤ alf m1 l1 * (gam - c)) :
    c ≤ chiSqOL H0 m l := by
  apply ge_of_point s hs c H0 m l hy
  have key : ∀ m l, Lf s m l ^ 2 ≤ alf m l * (gam - c) ↔
      (Lf s 0 0 + (Lf s 1 0 - Lf s 0 0) * m + (Lf s 0 1 - Lf s 0 0) * l) ^ 2 ≤
        alf 0 0 * (gam - c) + ((alf 1 0 - alf 0 0) * (gam - c)) * m
          + ((alf 0 1 - alf 0 0) * (gam - c)) * l := by
    intro m l
    rw [Lf_affine s m l, alf_affine m l]
    constructor <;> intro h <;> linarith
  rw [key] at c00 c01 c10 c11 ⊢
  exact box_convex hm0 hm1 hl0 hl1 c00 c01 c10 c11

/-- α as an explicit affine function (helper). -/
theorem alf_val (m l : ℝ) : alf m l = (29683848753019249277080357478587401221293 / 44957886861201436075178588802566400000000 : ℝ) + (91542076874978476974851496281529789753577253 / 321127763294295971965561348589760000000000000 : ℝ) * m + (-17248735465781830985713249682877298343 / 69059734041784079992593838406400000000 : ℝ) * l := by
  rw [alf_affine m l]
  have e00 : alf 0 0 = (29683848753019249277080357478587401221293 / 44957886861201436075178588802566400000000 : ℝ) := by norm_num [alf, e2OL, m16Table, Fin.sum_univ_succ]
  have e10 : alf 1 0 = (2124986975775811802677978347900078589339690771 / 2247894343060071803758929440128320000000000000 : ℝ) := by norm_num [alf, e2OL, m16Table, Fin.sum_univ_succ]
  have e01 : alf 0 1 = (461373049119881932634525798375857 / 1123947171530035901879464720064160 : ℝ) := by norm_num [alf, e2OL, m16Table, Fin.sum_univ_succ]
  rw [e00, e10, e01]; ring

/-- γ as a rational (helper). -/
theorem gam_val : gam = (753873368365253323890764901457904269 / 266022999178706722338334844985600 : ℝ) := by norm_num [gam, m16Table, Fin.sum_univ_succ]

/-! ## Exact rational evaluation (kernel computation)

The corner checks of a box are decided by kernel evaluation over ℚ (`decide +kernel`, which adds no
axioms); `Lf_cast`, `alf_cast`, `gam_cast` transfer them to the real definitions. -/

/-- Table 4 as rationals (helper; equal to `m16Table` entry by entry, `tQ_cast`). -/
def tQ : Fin 30 → ℚ × ℚ × ℚ :=
  ![(7/100, 69, 98/5), (9/100, 69, 12), (3/25, 343/5, 131/5), (17/100, 83, 8), (179/1000, 75, 4), (199/1000, 75, 5), (1/5, 729/10, 148/5), (27/100, 77, 14), (7/25, 444/5, 183/5), (44/125, 83, 14), (1901/5000, 83, 27/2), (2/5, 95, 17), (1001/2500, 77, 51/5), (4247/10000, 871/10, 56/5), (44497/100000, 464/5, 129/10), (4783/10000, 809/10, 9), (12/25, 97, 62), (593/1000, 104, 13), (17/25, 92, 8), (781/1000, 105, 12), (7/8, 125, 17), (22/25, 90, 40), (9/10, 117, 23), (1037/1000, 154, 20), (13/10, 168, 17), (1363/1000, 160, 168/5), (143/100, 177, 18), (153/100, 140, 14), (7/4, 202, 40), (393/200, 373/2, 252/5)]

theorem tQ_cast (i : Fin 30) : m16Table i = (((tQ i).1 : ℝ), ((tQ i).2.1 : ℝ), ((tQ i).2.2 : ℝ)) := by
  fin_cases i <;> norm_num [m16Table, tQ]

/-- E² over ℚ (helper). -/
def yQ (z m l : ℚ) : ℚ := m * (1 + z) ^ 3 + (1 - m - l) * (1 + z) ^ 2 + l

/-- `Lf` over ℚ (helper). -/
def LfQ (s : Fin 30 → ℚ) (m l : ℚ) : ℚ :=
  (∑ i, (tQ i).2.1 / (tQ i).2.2 ^ 2 * ((yQ (tQ i).1 m l + s i ^ 2) / (2 * s i))) + 73 / (12 / 5) ^ 2

/-- `alf` over ℚ (helper). -/
def alfQ (m l : ℚ) : ℚ := (∑ i, yQ (tQ i).1 m l / (tQ i).2.2 ^ 2) + 1 / (12 / 5) ^ 2

/-- `gam` over ℚ (helper). -/
def gamQ : ℚ := (∑ i, (tQ i).2.1 ^ 2 / (tQ i).2.2 ^ 2) + 73 ^ 2 / (12 / 5) ^ 2

theorem Lf_cast (s : Fin 30 → ℚ) (m l : ℚ) :
    Lf (fun i => (s i : ℝ)) m l = (LfQ s m l : ℝ) := by
  simp only [Lf, LfQ, wt, e2OL, yQ, tQ_cast]
  push_cast
  norm_num

theorem alf_cast (m l : ℚ) : alf m l = (alfQ m l : ℝ) := by
  simp only [alf, alfQ, e2OL, yQ, tQ_cast]
  push_cast
  norm_num

theorem gam_cast : gam = (gamQ : ℝ) := by
  simp only [gam, gamQ, tQ_cast]
  push_cast
  norm_num

/-- The four corner checks and positivity of s, as one decidable proposition over ℚ (helper). -/
def BoxOK (s : Fin 30 → ℚ) (c m0 m1 l0 l1 : ℚ) : Prop :=
  (∀ i, 0 < s i) ∧ LfQ s m0 l0 ^ 2 ≤ alfQ m0 l0 * (gamQ - c) ∧
    LfQ s m0 l1 ^ 2 ≤ alfQ m0 l1 * (gamQ - c) ∧ LfQ s m1 l0 ^ 2 ≤ alfQ m1 l0 * (gamQ - c) ∧
    LfQ s m1 l1 ^ 2 ≤ alfQ m1 l1 * (gamQ - c)

instance (s : Fin 30 → ℚ) (c m0 m1 l0 l1 : ℚ) : Decidable (BoxOK s c m0 m1 l0 l1) := by
  unfold BoxOK; infer_instance

/-- A box closed by an exact rational certificate. -/
theorem box_boundQ (s : Fin 30 → ℚ) (c m0 m1 l0 l1 : ℚ) (hok : BoxOK s c m0 m1 l0 l1)
    (H0 m l : ℝ) (hm0 : (m0 : ℝ) ≤ m) (hm1 : m ≤ m1) (hl0 : (l0 : ℝ) ≤ l) (hl1 : l ≤ l1)
    (hy : ∀ i, 0 ≤ e2OL m l (m16Table i).1) : (c : ℝ) ≤ chiSqOL H0 m l := by
  obtain ⟨hs, c00, c01, c10, c11⟩ := hok
  apply box_bound (fun i => (s i : ℝ)) (fun i => by exact_mod_cast hs i) c m0 m1 l0 l1 H0 m l
    hm0 hm1 hl0 hl1 hy <;>
  · rw [Lf_cast, alf_cast, gam_cast]; exact_mod_cast ‹_›

end Checked.Data.Moresco16Min
