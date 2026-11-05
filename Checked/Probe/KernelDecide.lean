import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fin.VecNotation

/-!
# Probe (run 2026-11-05T0628Z, branch `probe/kernel-decide`, not for main)

Does a certificate decided by kernel evaluation over ℚ (`decide +kernel`) pass every blocking
step of the checked job (axiom audit, nanoda replay, trust step)? One box of the Moresco 2016 χ²
cover (`Work/Data/Moresco16MinCerts1.lean`) as a test case.
-/

namespace Checked.Probe.KernelDecide

/-- Table 4 as rationals (helper; equal to `m16Table` entry by entry, `tQ_cast`). -/
def tQ : Fin 30 → ℚ × ℚ × ℚ :=
  ![(7/100, 69, 98/5), (9/100, 69, 12), (3/25, 343/5, 131/5), (17/100, 83, 8), (179/1000, 75, 4), (199/1000, 75, 5), (1/5, 729/10, 148/5), (27/100, 77, 14), (7/25, 444/5, 183/5), (44/125, 83, 14), (1901/5000, 83, 27/2), (2/5, 95, 17), (1001/2500, 77, 51/5), (4247/10000, 871/10, 56/5), (44497/100000, 464/5, 129/10), (4783/10000, 809/10, 9), (12/25, 97, 62), (593/1000, 104, 13), (17/25, 92, 8), (781/1000, 105, 12), (7/8, 125, 17), (22/25, 90, 40), (9/10, 117, 23), (1037/1000, 154, 20), (13/10, 168, 17), (1363/1000, 160, 168/5), (143/100, 177, 18), (153/100, 140, 14), (7/4, 202, 40), (393/200, 373/2, 252/5)]

/-- E² over ℚ (helper). -/
def yQ (z m l : ℚ) : ℚ := m * (1 + z) ^ 3 + (1 - m - l) * (1 + z) ^ 2 + l

/-- `Lf` over ℚ (helper). -/
def LfQ (s : Fin 30 → ℚ) (m l : ℚ) : ℚ :=
  (∑ i, (tQ i).2.1 / (tQ i).2.2 ^ 2 * ((yQ (tQ i).1 m l + s i ^ 2) / (2 * s i))) + 73 / (12 / 5) ^ 2

/-- `alf` over ℚ (helper). -/
def alfQ (m l : ℚ) : ℚ := (∑ i, yQ (tQ i).1 m l / (tQ i).2.2 ^ 2) + 1 / (12 / 5) ^ 2

/-- `gam` over ℚ (helper). -/
def gamQ : ℚ := (∑ i, (tQ i).2.1 ^ 2 / (tQ i).2.2 ^ 2) + 73 ^ 2 / (12 / 5) ^ 2

/-- The four corner checks and positivity of s, as one decidable proposition over ℚ (helper). -/
def BoxOK (s : Fin 30 → ℚ) (c m0 m1 l0 l1 : ℚ) : Prop :=
  (∀ i, 0 < s i) ∧ LfQ s m0 l0 ^ 2 ≤ alfQ m0 l0 * (gamQ - c) ∧
    LfQ s m0 l1 ^ 2 ≤ alfQ m0 l1 * (gamQ - c) ∧ LfQ s m1 l0 ^ 2 ≤ alfQ m1 l0 * (gamQ - c) ∧
    LfQ s m1 l1 ^ 2 ≤ alfQ m1 l1 * (gamQ - c)

instance (s : Fin 30 → ℚ) (c m0 m1 l0 l1 : ℚ) : Decidable (BoxOK s c m0 m1 l0 l1) := by
  unfold BoxOK; infer_instance


/-- One box of the cover, decided by kernel evaluation (helper). -/
theorem box_ok : BoxOK ![103223 / 100000, 3257 / 3125, 10579 / 10000, 3393 / 3125, 1091 / 1000, 110291 / 100000, 6897 / 6250, 22959 / 20000, 14433 / 12500, 60261 / 50000, 61309 / 50000, 124127 / 100000, 62079 / 50000, 126053 / 100000, 127669 / 100000, 65197 / 50000, 16317 / 12500, 351 / 250, 37151 / 25000, 4961 / 3125, 84381 / 50000, 169309 / 100000, 171511 / 100000, 37439 / 20000, 219993 / 100000, 22833 / 10000, 237387 / 100000, 251257 / 100000, 11327 / 4000, 316103 / 100000] (29933 / 2000) (13 / 32) (7 / 16) (3 / 4) (13 / 16) := by decide +kernel

end Checked.Probe.KernelDecide
