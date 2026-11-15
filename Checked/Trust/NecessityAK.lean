import Checked.FSAtt.AAssemble
import Checked.Trust.NonVacuity
import Checked.FalknerSkan.NegWindow
import Checked.FalknerSkan.NegWallShear
import Checked.FalknerSkan.NegWallShearRows
import Checked.FalknerSkan.NegWallShearRowsTop
import Checked.Records.FalknerSkan
import Checked.FalknerSkan.NegDecay
import Checked.Trust.AKSlow13
import Checked.Trust.AKSlow14
import Checked.Trust.AKSlow15
import Checked.Trust.AKSlow16
import Checked.Trust.AKSlow17
import Checked.Trust.AKSlow18
import Checked.Trust.AKSlow19
import Checked.Trust.AKSlow10
import Checked.Trust.AKSlow1988

/-! Hypothesis necessity for the attached Falkner–Skan wall-shear windows with an adverse pressure gradient (the decelerating rows of the attached table read blind, the separation-near row and the row at minus one tenth, and the record built on the separation-near row): the fast-approach hypothesis (for every `M`, eventually `M (1 − p) ≤ q`) is needed. Witness: for a decelerating stream the edge condition `p → 1` does not select one solution; a whole range of smaller wall shears gives solutions that reach the edge velocity only algebraically. For each row a certified chain of weighted one-sided cells (`Checked.Trust.AKSlow…`), started well below the window, shows the slow-approach event, and the generic slow-class theorem of the attached-flow stack (`Checked.FSAtt.AAssemble.slow_class`) turns it into a solution on the whole half-line with `f(0) = 0`, `p(0) = 0`, `p → 1` and `q > 0` everywhere, whose wall shear lies below the window. Run 2026-11-15T0628Z. -/

namespace Checked.Trust.NCAK

open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSAtt.ABase

/-- A slow-approach chain at a scaled wall value `α` whose square is below `c² K` gives a solution of the
Falkner–Skan problem with coefficient `−1/K` on the half-line, with every hypothesis of the attached windows
but the fast approach, and wall shear below `c`. -/
theorem slow_witness {K α c : ℝ} (hK5 : 5 ≤ K) (hα0 : 0 < α) (hα1 : α ≤ 11 / 10) (hc0 : 0 < c)
    (hc : α ^ 2 < c ^ 2 * K) (hS : ChainA K α SlowA) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / K) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧ q 0 < c := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -⟩ :=
    Checked.FSAtt.AAssemble.slow_class hK5 hα0 hα1 (Checked.FSAtt.AAssemble.of_chain hS)
  refine ⟨f, p, q, a1, a2, a3, a4, a5, a7, fun η hη => (a8 η hη).1, ?_⟩
  rw [a6]
  have hK : 0 < K := by linarith
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  rw [div_lt_iff₀ hs]
  have h1 : α < Real.sqrt (c ^ 2 * K) := by
    rw [Real.lt_sqrt hα0.le]; exact hc
  rwa [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0.le] at h1

/-- The fast-approach hypothesis is needed in `fs_neg_wall_shear_13_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow13.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_wall_shear_13_window_h8 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_13_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 100 / 13) (α := 363 / 1000) (c := 0.2614227559) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow13.chain
  have hK : (-1 / (100 / 13 : ℝ)) = -13 / 100 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `fs_neg_wall_shear_14_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow14.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_wall_shear_14_window_h8 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_14_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 100 / 14) (α := 8 / 25) (c := 0.2397359553) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow14.chain
  have hK : (-1 / (100 / 14 : ℝ)) = -14 / 100 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `fs_neg_wall_shear_15_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow15.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_wall_shear_15_window_h8 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_15_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 100 / 15) (α := 279 / 1000) (c := 0.2163614056) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow15.chain
  have hK : (-1 / (100 / 15 : ℝ)) = -15 / 100 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `fs_neg_wall_shear_16_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow16.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_wall_shear_16_window_h8 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_16_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 100 / 16) (α := 119 / 500) (c := 0.1907798552) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow16.chain
  have hK : (-1 / (100 / 16 : ℝ)) = -16 / 100 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `fs_neg_wall_shear_17_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow17.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_wall_shear_17_window_h8 : necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 100 / 17) (α := 197 / 1000) (c := 0.1621146770) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow17.chain
  have hK : (-1 / (100 / 17 : ℝ)) = -17 / 100 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `fs_neg_wall_shear_18_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow18.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_wall_shear_18_window_h8 : necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 100 / 18) (α := 19 / 125) (c := 0.1286362205) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow18.chain
  have hK : (-1 / (100 / 18 : ℝ)) = -18 / 100 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `fs_neg_wall_shear_19_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow19.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_wall_shear_19_window_h8 : necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 100 / 19) (α := 49 / 500) (c := 0.0856997440) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow19.chain
  have hK : (-1 / (100 / 19 : ℝ)) = -19 / 100 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `fs_neg_tenth_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow10.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_tenth_window_h8 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 10 / 1) (α := 101 / 200) (c := 0.3192697598) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow10.chain
  have hK : (-1 / (10 / 1 : ℝ)) = -1 / 10 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `fs_neg_wall_shear_window`: a solution reaching the edge velocity only
algebraically (certified slow-approach chain `Checked.Trust.AKSlow1988.chain`) meets every other hypothesis and has
a wall shear below the window. -/
theorem fs_neg_wall_shear_window_h8 : necessity% Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 2500 / 497) (α := 3 / 500) (c := 0.0052181) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) Checked.Trust.AKSlow1988.chain
  have hK : (-1 / (2500 / 497 : ℝ)) = -1988 / 10000 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  linarith [h.1]

/-- The fast-approach hypothesis is needed in `F13_wall_shear`: the slow-approach solution of the
separation-near row has a wall shear below three thousandths, so the printed value minus it is far from the
recorded difference. -/
theorem F13_wall_shear_h8 : necessity% Checked.Records.F13_wall_shear 8 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, w⟩ :=
    slow_witness (K := 2500 / 497) (α := 3 / 500) (c := 3 / 1000) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) Checked.Trust.AKSlow1988.chain
  have hK : (-1 / (2500 / 497 : ℝ)) = -1988 / 10000 := by norm_num
  refine ⟨f, p, q, a1, a2, fun η hη => by rw [← hK]; exact a3 η hη, a4, a5, a6, a7, fun h => ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioWall at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

/-- The restriction of the conclusion to the half-line is needed in `fs_neg_decay_equal`: the hypotheses
constrain the two solutions only on the half-line, so a copy of a fast-approach solution changed at a negative
abscissa meets every hypothesis and differs there. -/
theorem fs_neg_decay_equal_h18 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 18 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_exists_decay
  have e : ∀ η ∈ Ici (0 : ℝ), (if η < 0 then f η + 1 else f η) = f η :=
    fun η hη => by simp [not_lt.mpr (mem_Ici.mp hη)]
  refine ⟨-17 / 100, by norm_num, f, p, q, fun η => if η < 0 then f η + 1 else f η, p, q, hf, hp, hq, hf0, hp0,
    hlim, hpos, hdec, fun η hη => (hf η hη).congr (fun y hy => e y hy) (e η hη), hp,
    fun η hη => ((hq η hη).congr_deriv (by simp only [e η hη])), by simp [hf0], hp0, hlim, hpos, hdec, -1, ?_⟩
  simp

end Checked.Trust.NCAK
