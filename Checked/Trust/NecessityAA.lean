import Checked.FSRev.RFlowCells
import Checked.Trust.NonVacuity
import Checked.Trust.NecessityY
import Checked.FSRev.RThirteenOver
import Checked.FSRev.RThirteenSlow
import Checked.FSRev.RThirteenTube
import Checked.FalknerSkan.NegWallShearRowsTop
import Checked.FalknerSkan.NegDecay
import Checked.FalknerSkan.NegReversedWallShear
import Checked.FalknerSkan.SeparationEqual
import Checked.FalknerSkan.SeparationPrinted
import Checked.Records.FalknerSkan

/-! Hypothesis necessity for the comparison and equality theorems of the fast-approach Falkner–Skan class
(`Checked.FalknerSkan.NegDecay`), for the separation pair (`SeparationEqual`, `SeparationPrinted`, record
`F12_separation`) and for the overshoot of the printed reverse-flow wall value (run 2026-11-14T0228Z).

Three kinds of witness, all at one decelerating row of Ganapol's tables where both branches are Checked:

* The reversed-flow solution of the row, translated along the half-line (`RFlowCells`, the cells of its
  Checked tube, as in `Checked.Trust.NecessityY`). Translated to the point where its velocity returns to zero it
  is a fast-approach solution with blowing at the wall and a wall shear below the attached one; translated to the
  point where its stream function returns to zero it has a wall moving downstream and a wall shear above the
  attached one. So the wall conditions of either profile of the comparison and of the equality theorem are
  needed, wherever the translate falls on the side that breaks the conclusion.
* An explicit profile `p = 1 − exp(−(c η + d η²))` with `q = p'`, which approaches the edge value faster than
  every exponential: with `f` defined from the equation it meets everything but `f' = p`; with `f = ∫ p` it
  meets everything but the equation for `q`. With `f = ∫ p` and the shear solving its own linear equation
  `q' = −f q − β(1 − p²)` by an integrating factor (as in `Checked.Trust.NecessityT`), it meets everything but
  `p' = q`; the shear then decays like `exp(−∫ f)`, slower than `1 − p`, so the fast-approach condition holds.
* The attached fast-approach solution of the row: it has every property of a separation profile except a zero
  wall shear, at a pressure-gradient parameter that is not the separation value.
-/

namespace Checked.Trust.NCAA

open Set Filter Topology Checked.Sim Checked.Sim.QPoly Checked.FSSep.SCellWC Checked.FSNeg.NBase
  Checked.FSSep.SBase Checked.FSAtt.AFlow Checked.FSRev.RBase Checked.FSRev.RCell Checked.FSRev.RFlowCells

/-! ### An explicit profile approaching the edge value faster than every exponential -/

/-- The exponent `c η + d η²`. -/
noncomputable def tg (c d η : ℝ) : ℝ := c * η + d * η ^ 2
/-- The velocity `1 − exp(−(c η + d η²))`. -/
noncomputable def tP (c d η : ℝ) : ℝ := 1 - Real.exp (-tg c d η)
/-- Its derivative. -/
noncomputable def tQ (c d η : ℝ) : ℝ := (c + 2 * d * η) * Real.exp (-tg c d η)
/-- Its second derivative. -/
noncomputable def tQ' (c d η : ℝ) : ℝ := (2 * d - (c + 2 * d * η) ^ 2) * Real.exp (-tg c d η)

theorem tE_deriv (c d η : ℝ) :
    HasDerivAt (fun η => Real.exp (-tg c d η)) (-(c + 2 * d * η) * Real.exp (-tg c d η)) η := by
  have h : HasDerivAt (fun η => tg c d η) (c + 2 * d * η) η := by
    have := ((hasDerivAt_id' η).const_mul c).add ((hasDerivAt_pow 2 η).const_mul d)
    unfold tg
    convert this using 1; push_cast; ring
  have := h.neg.exp
  convert this using 1; simp only [Pi.neg_apply]; ring

theorem tP_deriv (c d η : ℝ) : HasDerivAt (tP c d) (tQ c d η) η := by
  have := (tE_deriv c d η).const_sub 1
  unfold tP tQ
  convert this using 1; ring

theorem tQ_deriv (c d η : ℝ) : HasDerivAt (tQ c d) (tQ' c d η) η := by
  have hl : HasDerivAt (fun η : ℝ => c + 2 * d * η) (2 * d) η := by
    have := ((hasDerivAt_id' η).const_mul (2 * d)).const_add c
    convert this using 1; ring
  have := hl.mul (tE_deriv c d η)
  unfold tQ tQ'
  convert this using 1; ring

theorem tP_zero (c d : ℝ) : tP c d 0 = 0 := by simp [tP, tg]

theorem tQ_zero (c d : ℝ) : tQ c d 0 = c := by simp [tQ, tg]

theorem tQ_pos {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) : ∀ η ∈ Ici (0 : ℝ), 0 < tQ c d η := by
  intro η hη
  have : (0 : ℝ) ≤ η := hη
  unfold tQ
  have : 0 < c + 2 * d * η := by positivity
  positivity

theorem tg_atTop {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) : Tendsto (tg c d) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id.const_mul_atTop hc)
  filter_upwards [eventually_ge_atTop 0] with η hη
  unfold tg; simp only [id]; nlinarith [sq_nonneg η]

theorem tP_lim {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) : Tendsto (tP c d) atTop (𝓝 1) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tg_atTop hc hd)
  have := h.const_sub 1
  simp only [sub_zero] at this
  exact this

theorem t_decay {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - tP c d η) ≤ tQ c d η := by
  intro M
  filter_upwards [eventually_ge_atTop (|M| / (2 * d))] with η hη
  have he := Real.exp_pos (-tg c d η)
  have h2 : |M| ≤ 2 * d * η := by
    rw [div_le_iff₀ (by positivity)] at hη; linarith
  have hM : M ≤ c + 2 * d * η := by linarith [le_abs_self M]
  have : 1 - tP c d η = Real.exp (-tg c d η) := by unfold tP; ring
  rw [this]; unfold tQ
  exact mul_le_mul_of_nonneg_right hM he.le

/-- `f = ∫₀^η p`, so that `f' = p` and `f(0) = 0`. -/
noncomputable def tF (c d η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, tP c d s

theorem tP_cont (c d : ℝ) : Continuous (tP c d) := by unfold tP tg; fun_prop

theorem tF_deriv (c d η : ℝ) : HasDerivAt (tF c d) (tP c d η) η :=
  ((tP_cont c d).integral_hasStrictDerivAt 0 η).hasDerivAt

theorem tF_zero (c d : ℝ) : tF c d 0 = 0 := by simp [tF]

/-- `f` chosen from the Falkner–Skan equation with parameter `β`: `f = (−β(1 − p²) − q')/q`. -/
noncomputable def tG (β c d η : ℝ) : ℝ := (-(β * (1 - tP c d η ^ 2)) - tQ' c d η) / tQ c d η

theorem tG_ode {β c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) :
    tQ' c d η = -(tG β c d η * tQ c d η) - β * (1 - tP c d η ^ 2) := by
  have hq := (tQ_pos hc hd η hη).ne'
  unfold tG
  field_simp
  ring

theorem tG_zero {β c d : ℝ} (h : 2 * d - c ^ 2 = -β) : tG β c d 0 = 0 := by
  unfold tG
  rw [tP_zero, tQ_zero]
  have : tQ' c d 0 = 2 * d - c ^ 2 := by simp [tQ', tg]
  rw [this, h]; simp

/-- The explicit profile with `f` from the equation: every condition of the fast-approach class at `β`
except `f' = p`. -/
theorem toyG_all {β c d : ℝ} (hc : 0 < c) (hd : 0 < d) (h : 2 * d - c ^ 2 = -β) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (tP c d) (tQ c d η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (tQ c d)
      (-(tG β c d η * tQ c d η) - β * (1 - tP c d η ^ 2)) (Ici 0) η) ∧
    tG β c d 0 = 0 ∧ tP c d 0 = 0 ∧ Tendsto (tP c d) atTop (𝓝 1) ∧
    (∀ η ∈ Ici (0 : ℝ), 0 < tQ c d η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - tP c d η) ≤ tQ c d η) ∧ tQ c d 0 = c :=
  ⟨fun η _ => (tP_deriv c d η).hasDerivWithinAt,
    fun η hη => by rw [← tG_ode hc hd.le η hη]; exact (tQ_deriv c d η).hasDerivWithinAt,
    tG_zero h, tP_zero c d, tP_lim hc hd.le, tQ_pos hc hd.le, t_decay hc hd, tQ_zero c d⟩

/-- The explicit profile with `f = ∫ p`: every condition of the fast-approach class except the equation
for `q`. -/
theorem toyF_all {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (tF c d) (tP c d η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (tP c d) (tQ c d η) (Ici 0) η) ∧
    tF c d 0 = 0 ∧ tP c d 0 = 0 ∧ Tendsto (tP c d) atTop (𝓝 1) ∧
    (∀ η ∈ Ici (0 : ℝ), 0 < tQ c d η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - tP c d η) ≤ tQ c d η) ∧ tQ c d 0 = c :=
  ⟨fun η _ => (tF_deriv c d η).hasDerivWithinAt, fun η _ => (tP_deriv c d η).hasDerivWithinAt,
    tF_zero c d, tP_zero c d, tP_lim hc hd.le, tQ_pos hc hd.le, t_decay hc hd, tQ_zero c d⟩

/-! ### Row thirteen: the reversed-flow solution translated, and the attached solution -/

/-- The scale of row 13. -/
theorem sK_pos : 0 < Real.sqrt (100 / 13 : ℝ) := Real.sqrt_pos.2 (by norm_num)

/-- The reversed-flow solution of row 13 translated to the return point of its velocity: a fast-approach
solution with p(0) = 0 (and blowing at the wall) whose wall shear is below 4/25. -/
theorem trans_p : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-13 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
    p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ q 0 < 4 / 25 := by
  obtain ⟨a, hla, hah, A, B, C, hlim, hpb, hdec⟩ := core_rev_flow (K := 100 / 13) (by norm_num) (by norm_num)
    Checked.FSRev.RThirteenOver.chain Checked.FSRev.RThirteenSlow.chain Checked.FSRev.RThirteenTube.tube
  have hα : |a - (-6141116300843 / 15625000000000)| ≤ 55471 / 1000000000000000 := by
    rw [abs_le]; constructor <;> linarith
  have hc := sK_pos
  have hβ : (-1 / (100 / 13 : ℝ)) = (-13 / 100 : ℝ) := by norm_num
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 < (flowA (100 / 13 : ℝ) a (η / Real.sqrt (100 / 13 : ℝ))).2.1 ∧ (flowA (100 / 13 : ℝ) a (η / Real.sqrt (100 / 13 : ℝ))).2.1 < 1 :=
    fun η hη => ⟨by linarith [(hpb η hη).1], (hpb η hη).2⟩
  obtain ⟨t, ht, hz, hqL, hqU⟩ := Checked.Trust.NCY.cross_p_13 (flow_sol (100 / 13 : ℝ) a (3 / 2)) (flowA_zero _ _) hα
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have hs : 0 ≤ Real.sqrt (100 / 13 : ℝ) * t := mul_nonneg hc.le ht0
  have hst : Real.sqrt (100 / 13 : ℝ) * t / Real.sqrt (100 / 13 : ℝ) = t := by field_simp
  have hq0 : 0 < (flowA (100 / 13 : ℝ) a (Real.sqrt (100 / 13 : ℝ) * t / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ) := by
    rw [hst]; exact div_pos (by linarith) hc
  have hpos := pos_after (β := -1 / (100 / 13 : ℝ)) (by norm_num) C hb hs hq0
  have hC : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun x => (flowA (100 / 13 : ℝ) a ((x + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ))
      (-((Real.sqrt (100 / 13 : ℝ) * (flowA (100 / 13 : ℝ) a ((η + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).1) *
          ((flowA (100 / 13 : ℝ) a ((η + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ))) -
        (-13 / 100 : ℝ) * (1 - (flowA (100 / 13 : ℝ) a ((η + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.1 ^ 2)) (Ici 0) η := by
    intro η hη
    have := shift_deriv hs C η hη
    rw [hβ] at this
    exact this
  have A' := shift_deriv hs A
  have B' := shift_deriv hs B
  refine ⟨fun x => Real.sqrt (100 / 13 : ℝ) * (flowA (100 / 13 : ℝ) a ((x + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).1,
    fun x => (flowA (100 / 13 : ℝ) a ((x + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.1,
    fun x => (flowA (100 / 13 : ℝ) a ((x + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ),
    A', B', hC, ?_, shift_lim _ hlim, ?_, shift_dec _ hdec, ?_⟩
  · show (flowA (100 / 13 : ℝ) a ((0 + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.1 = 0
    rw [zero_add, hst]; exact hz
  · intro η hη
    exact hpos (η + Real.sqrt (100 / 13 : ℝ) * t) (by linarith [mem_Ici.1 hη])
  · show (flowA (100 / 13 : ℝ) a ((0 + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ) < 4 / 25
    rw [zero_add, hst]
    have hr : ((2773499 / 1000000 : ℝ)) < Real.sqrt (100 / 13 : ℝ) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    rw [div_lt_iff₀ hc]
    nlinarith

/-- The reversed-flow solution of row 13 translated to the return point of its stream function: a
fast-approach solution with f(0) = 0 (and a wall moving downstream) whose wall shear is above 7/25. -/
theorem trans_g : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-13 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ 7 / 25 < q 0 := by
  obtain ⟨a, hla, hah, A, B, C, hlim, hpb, hdec⟩ := core_rev_flow (K := 100 / 13) (by norm_num) (by norm_num)
    Checked.FSRev.RThirteenOver.chain Checked.FSRev.RThirteenSlow.chain Checked.FSRev.RThirteenTube.tube
  have hα : |a - (-6141116300843 / 15625000000000)| ≤ 55471 / 1000000000000000 := by
    rw [abs_le]; constructor <;> linarith
  have hc := sK_pos
  have hβ : (-1 / (100 / 13 : ℝ)) = (-13 / 100 : ℝ) := by norm_num
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 < (flowA (100 / 13 : ℝ) a (η / Real.sqrt (100 / 13 : ℝ))).2.1 ∧ (flowA (100 / 13 : ℝ) a (η / Real.sqrt (100 / 13 : ℝ))).2.1 < 1 :=
    fun η hη => ⟨by linarith [(hpb η hη).1], (hpb η hη).2⟩
  obtain ⟨t, ht, hz, hqL, hqU⟩ := Checked.Trust.NCY.cross_g_13 (flow_sol (100 / 13 : ℝ) a (3 / 2)) (flowA_zero _ _) hα
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
  have hs : 0 ≤ Real.sqrt (100 / 13 : ℝ) * t := mul_nonneg hc.le ht0
  have hst : Real.sqrt (100 / 13 : ℝ) * t / Real.sqrt (100 / 13 : ℝ) = t := by field_simp
  have hq0 : 0 < (flowA (100 / 13 : ℝ) a (Real.sqrt (100 / 13 : ℝ) * t / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ) := by
    rw [hst]; exact div_pos (by linarith) hc
  have hpos := pos_after (β := -1 / (100 / 13 : ℝ)) (by norm_num) C hb hs hq0
  have hC : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun x => (flowA (100 / 13 : ℝ) a ((x + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ))
      (-((Real.sqrt (100 / 13 : ℝ) * (flowA (100 / 13 : ℝ) a ((η + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).1) *
          ((flowA (100 / 13 : ℝ) a ((η + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ))) -
        (-13 / 100 : ℝ) * (1 - (flowA (100 / 13 : ℝ) a ((η + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.1 ^ 2)) (Ici 0) η := by
    intro η hη
    have := shift_deriv hs C η hη
    rw [hβ] at this
    exact this
  have A' := shift_deriv hs A
  have B' := shift_deriv hs B
  refine ⟨fun x => Real.sqrt (100 / 13 : ℝ) * (flowA (100 / 13 : ℝ) a ((x + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).1,
    fun x => (flowA (100 / 13 : ℝ) a ((x + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.1,
    fun x => (flowA (100 / 13 : ℝ) a ((x + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ),
    A', B', hC, ?_, shift_lim _ hlim, ?_, shift_dec _ hdec, ?_⟩
  · show Real.sqrt (100 / 13 : ℝ) * (flowA (100 / 13 : ℝ) a ((0 + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).1 = 0
    rw [zero_add, hst, hz, mul_zero]
  · intro η hη
    exact hpos (η + Real.sqrt (100 / 13 : ℝ) * t) (by linarith [mem_Ici.1 hη])
  · show 7 / 25 < (flowA (100 / 13 : ℝ) a ((0 + Real.sqrt (100 / 13 : ℝ) * t) / Real.sqrt (100 / 13 : ℝ))).2.2 / Real.sqrt (100 / 13 : ℝ)
    rw [zero_add, hst]
    have hr : Real.sqrt (100 / 13 : ℝ) < ((1386751 / 500000 : ℝ)) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    rw [lt_div_iff₀ hc]
    nlinarith

/-- The attached fast-approach solution of row 13 and its wall shear (from the Checked window). -/
theorem attached : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-13 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ 13 / 50 < q 0 ∧ q 0 < 27 / 100 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_13_exists_decay
  have w := Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_13_window f p q a1 a2 a3 a4 a5 a6 a7 a8
  exact ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, by norm_num at w; linarith [w.1],
    by norm_num at w; linarith [w.2]⟩

/-! ### The comparison theorem of the fast-approach class -/

/-- In `fs_neg_decay_max_shear`, `f' = p` of the fast-approach profile is needed: the explicit profile with
`f` from the equation has a smaller wall shear than the attached solution of the row. -/
theorem fs_neg_decay_max_shear_h2 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 2 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyG_all (β := -13 / 100) (c := 1 / 10) (d := 7 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, -, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, _, _, _, f, p, q, t1, t2, t3, t4, t5, t6, t7,
    a1, a2, a3, a4, a5, a6, a7, ?_⟩
  rw [t8]; intro h; linarith

/-- In `fs_neg_decay_max_shear`, the equation for `q` of the fast-approach profile is needed: the explicit
profile with `f = ∫ p` has a smaller wall shear than the attached solution of the row. -/
theorem fs_neg_decay_max_shear_h4 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 4 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyF_all (c := 1 / 10) (d := 7 / 100) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, -, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, _, _, _, f, p, q, t1, t2, t3, t4, t5, t6, t7,
    a1, a2, a3, a4, a5, a6, a7, ?_⟩
  rw [t8]; intro h; linarith

/-- In `fs_neg_decay_max_shear`, `f(0) = 0` of the fast-approach profile is needed: the reversed-flow
solution of the row translated to the return of its velocity has a smaller wall shear than the attached one. -/
theorem fs_neg_decay_max_shear_h5 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 5 := by
  obtain ⟨g, pg, qg, b1, b2, b3, b4, b5, b6, b7, b8⟩ := trans_p
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, -, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, g, pg, qg, f, p, q, b1, b2, b3, b4, b5, b6, b7,
    a1, a2, a3, a4, a5, a6, a7, ?_⟩
  intro h; linarith

/-- In `fs_neg_decay_max_shear`, `f' = p` of the second profile is needed: the explicit profile with `f`
from the equation has a larger wall shear than the attached solution of the row. -/
theorem fs_neg_decay_max_shear_h10 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 10 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, -, t8⟩ := toyG_all (β := -13 / 100) (c := 1) (d := 113 / 200)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, w2⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, _, _, _, a1, a2, a3, a4, a5, a6, a7, a8,
    t1, t2, t3, t4, t5, t6, ?_⟩
  rw [t8]; intro h; linarith

/-- In `fs_neg_decay_max_shear`, the equation for `q` of the second profile is needed: the explicit profile
with `f = ∫ p` has a larger wall shear than the attached solution of the row. -/
theorem fs_neg_decay_max_shear_h12 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 12 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, -, t8⟩ := toyF_all (c := 1) (d := 1) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, w2⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, _, _, _, a1, a2, a3, a4, a5, a6, a7, a8,
    t1, t2, t3, t4, t5, t6, ?_⟩
  rw [t8]; intro h; linarith

/-- In `fs_neg_decay_max_shear`, `p(0) = 0` of the second profile is needed: the reversed-flow solution of
the row translated to the return of its stream function has a larger wall shear than the attached one. -/
theorem fs_neg_decay_max_shear_h14 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 14 := by
  obtain ⟨g, pg, qg, b1, b2, b3, b4, b5, b6, -, b8⟩ := trans_g
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, w2⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, g, pg, qg, a1, a2, a3, a4, a5, a6, a7, a8,
    b1, b2, b3, b4, b5, b6, ?_⟩
  intro h; linarith

/-! ### The equality theorem of the fast-approach class -/

theorem fs_neg_decay_equal_h2 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 2 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyG_all (β := -13 / 100) (c := 1 / 10) (d := 7 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, _, _, _, f, p, q, t1, t2, t3, t4, t5, t6, t7,
    a1, a2, a3, a4, a5, a6, a7, a8, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; rw [t8] at he; linarith

theorem fs_neg_decay_equal_h4 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 4 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyF_all (c := 1 / 10) (d := 7 / 100) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, _, _, _, f, p, q, t1, t2, t3, t4, t5, t6, t7,
    a1, a2, a3, a4, a5, a6, a7, a8, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; rw [t8] at he; linarith

theorem fs_neg_decay_equal_h5 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 5 := by
  obtain ⟨g, pg, qg, b1, b2, b3, b4, b5, b6, b7, b8⟩ := trans_p
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, g, pg, qg, f, p, q, b1, b2, b3, b4, b5, b6, b7,
    a1, a2, a3, a4, a5, a6, a7, a8, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; linarith

theorem fs_neg_decay_equal_h6 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 6 := by
  obtain ⟨g, pg, qg, b1, b2, b3, b4, b5, b6, b7, b8⟩ := trans_g
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, w2⟩ := attached
  refine ⟨-13 / 100, by norm_num, g, pg, qg, f, p, q, b1, b2, b3, b4, b5, b6, b7,
    a1, a2, a3, a4, a5, a6, a7, a8, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; linarith

theorem fs_neg_decay_equal_h10 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 10 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyG_all (β := -13 / 100) (c := 1 / 10) (d := 7 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, _, _, _, a1, a2, a3, a4, a5, a6, a7, a8,
    t1, t2, t3, t4, t5, t6, t7, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; rw [t8] at he; linarith

theorem fs_neg_decay_equal_h12 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 12 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyF_all (c := 1 / 10) (d := 7 / 100) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, _, _, _, a1, a2, a3, a4, a5, a6, a7, a8,
    t1, t2, t3, t4, t5, t6, t7, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; rw [t8] at he; linarith

theorem fs_neg_decay_equal_h13 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 13 := by
  obtain ⟨g, pg, qg, b1, b2, b3, b4, b5, b6, b7, b8⟩ := trans_p
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, g, pg, qg, a1, a2, a3, a4, a5, a6, a7, a8,
    b1, b2, b3, b4, b5, b6, b7, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; linarith

theorem fs_neg_decay_equal_h14 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 14 := by
  obtain ⟨g, pg, qg, b1, b2, b3, b4, b5, b6, b7, b8⟩ := trans_g
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, w2⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, g, pg, qg, a1, a2, a3, a4, a5, a6, a7, a8,
    b1, b2, b3, b4, b5, b6, b7, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; linarith

/-! ### The separation pair: a zero wall shear is needed -/

/-- In `fs_separation_below_printed`, `q(0) = 0` is needed: the attached fast-approach solution of the row
meets every other condition at a parameter above the printed separation value. -/
theorem fs_separation_below_printed_h6 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed 6 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ := attached
  exact ⟨-13 / 100, f, p, q, a1, a2, a3, a4, a5, a6, fun η (hη : η ∈ Ioi (0 : ℝ)) => a7 η (mem_Ici.2 (le_of_lt hη)), a8, by norm_num⟩

/-- In the record `F12_separation`, `q(0) = 0` is needed (same witness). -/
theorem F12_separation_h6 : necessity% Checked.Records.F12_separation 6 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ := attached
  refine ⟨-13 / 100, f, p, q, a1, a2, a3, a4, a5, a6, fun η (hη : η ∈ Ioi (0 : ℝ)) => a7 η (mem_Ici.2 (le_of_lt hη)), a8, ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioSeparation
  rw [abs_le]; norm_num

/-- In `fs_separation_equal`, `q(0) = 0` of the first profile is needed: the attached fast-approach
solution of the row and the separation profile have different parameters. -/
theorem fs_separation_equal_h6 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 6 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ := attached
  obtain ⟨β, hβ, g, pg, qg, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := Checked.FalknerSkan.Separation.fs_separation_exists
  refine ⟨-13 / 100, β, f, p, q, g, pg, qg, a1, a2, a3, a4, a5, a6, fun η (hη : η ∈ Ioi (0 : ℝ)) => a7 η (mem_Ici.2 (le_of_lt hη)), a8,
    b1, b2, b3, b4, b5, b6, b7, b8, b9, ?_⟩
  intro h; have := hβ.2; linarith

/-- In `fs_separation_equal`, `q(0) = 0` of the second profile is needed (the same pair, swapped). -/
theorem fs_separation_equal_h15 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 15 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ := attached
  obtain ⟨β, hβ, g, pg, qg, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := Checked.FalknerSkan.Separation.fs_separation_exists
  refine ⟨β, -13 / 100, g, pg, qg, f, p, q, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    a1, a2, a3, a4, a5, a6, fun η (hη : η ∈ Ioi (0 : ℝ)) => a7 η (mem_Ici.2 (le_of_lt hη)), a8, ?_⟩
  intro h; have := hβ.2; linarith

/-! ### The overshoot of the printed reverse-flow wall value: `f' = p` is needed -/

/-- The velocity `−c η/(1 + a η)` of the explicit profile. -/
noncomputable def oP (η : ℝ) : ℝ := -(2579 / 500000) * η / (1 + 49700 / 2579 * η)
/-- Its derivative. -/
noncomputable def oQ (η : ℝ) : ℝ := -(2579 / 500000) / (1 + 49700 / 2579 * η) ^ 2
/-- Its second derivative. -/
noncomputable def oQ' (η : ℝ) : ℝ := 2 * (49700 / 2579) * (2579 / 500000) / (1 + 49700 / 2579 * η) ^ 3
/-- `f` from the equation with the parameter of the printed value. -/
noncomputable def oF (η : ℝ) : ℝ := (-((-1988 / 10000) * (1 - oP η ^ 2)) - oQ' η) / oQ η

theorem oD_pos (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) : 0 < 1 + 49700 / 2579 * η := by
  have : (0 : ℝ) ≤ η := hη; positivity

theorem oP_deriv (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) : HasDerivAt oP (oQ η) η := by
  have hD := oD_pos η hη
  have hl : HasDerivAt (fun η : ℝ => 1 + 49700 / 2579 * η) (49700 / 2579) η := by
    have := ((hasDerivAt_id' η).const_mul (49700 / 2579 : ℝ)).const_add 1
    convert this using 1; ring
  have hn : HasDerivAt (fun η : ℝ => -(2579 / 500000) * η) (-(2579 / 500000)) η := by
    have := (hasDerivAt_id' η).const_mul (-(2579 / 500000 : ℝ))
    convert this using 1; ring
  have := hn.div hl hD.ne'
  unfold oP oQ
  convert this using 1
  field_simp
  ring

theorem oQ_deriv (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) : HasDerivAt oQ (oQ' η) η := by
  have hD := oD_pos η hη
  have hl : HasDerivAt (fun η : ℝ => (1 + 49700 / 2579 * η) ^ 2)
      (2 * (1 + 49700 / 2579 * η) * (49700 / 2579)) η := by
    have := (((hasDerivAt_id' η).const_mul (49700 / 2579 : ℝ)).const_add 1).pow 2
    convert this using 1; push_cast; ring
  have := (hasDerivAt_const η (-(2579 / 500000 : ℝ))).div hl (by positivity)
  unfold oQ oQ'
  convert this using 1
  field_simp
  ring

theorem oQ_ne (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) : oQ η ≠ 0 := by
  have hD := oD_pos η hη
  unfold oQ
  have : 0 < (1 + 49700 / 2579 * η) ^ 2 := by positivity
  exact div_ne_zero (by norm_num) this.ne'

/-- In `fs_neg_reversed_printed_overshoots`, `f' = p` is needed: the explicit profile `p = −c η/(1 + a η)`,
`q = p'` with the printed wall value, and `f` from the equation (zero at the wall) meets every other
hypothesis, and its velocity is never positive. -/
theorem fs_neg_reversed_printed_overshoots_h1 :
    necessity% Checked.FalknerSkan.NegReversedWallShear.fs_neg_reversed_printed_overshoots 1 := by
  refine ⟨oF, oP, oQ, fun η hη => (oP_deriv η hη).hasDerivWithinAt, fun η hη => ?_, ?_, ?_, ?_, ?_⟩
  · have e : oQ' η = -(oF η * oQ η) - (-1988 / 10000) * (1 - oP η ^ 2) := by
      have := oQ_ne η hη
      unfold oF
      field_simp
      ring
    rw [← e]; exact (oQ_deriv η hη).hasDerivWithinAt
  · unfold oF oP oQ oQ'; norm_num
  · unfold oP; norm_num
  · unfold oQ; norm_num
  · rintro ⟨η, hη, h⟩
    have hD := oD_pos η (le_of_lt hη)
    have : oP η ≤ 0 := by
      unfold oP
      apply div_nonpos_of_nonpos_of_nonneg _ hD.le
      have : (0 : ℝ) < η := hη
      nlinarith
    linarith

/-! ### A fast-approach profile whose shear is not the derivative of the velocity -/

/-- `G = ∫₀^η f` for `f = ∫ p`. -/
noncomputable def tGG (c d η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, tF c d s

theorem tF_cont (c d : ℝ) : Continuous (tF c d) :=
  continuous_iff_continuousAt.2 fun η => (tF_deriv c d η).continuousAt

theorem tGG_deriv (c d η : ℝ) : HasDerivAt (tGG c d) (tF c d η) η :=
  ((tF_cont c d).integral_hasStrictDerivAt 0 η).hasDerivAt

theorem tGG_cont (c d : ℝ) : Continuous (tGG c d) :=
  continuous_iff_continuousAt.2 fun η => (tGG_deriv c d η).continuousAt

/-- The forcing `−β(1 − p²)` of the row. -/
noncomputable def tS (c d x : ℝ) : ℝ := 13 / 100 * (1 - tP c d x ^ 2)

theorem tS_cont (c d : ℝ) : Continuous (tS c d) := by
  have := tP_cont c d; unfold tS; fun_prop

theorem tP_le_one (c d η : ℝ) : tP c d η ≤ 1 := by
  unfold tP; linarith [Real.exp_pos (-tg c d η)]

theorem tP_nonneg {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) {η : ℝ} (hη : 0 ≤ η) : 0 ≤ tP c d η := by
  unfold tP
  have : 0 ≤ tg c d η := by unfold tg; positivity
  have : Real.exp (-tg c d η) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

theorem tS_nonneg {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) : ∀ x, 0 ≤ x → 0 ≤ tS c d x := by
  intro x hx
  have h1 := tP_nonneg hc hd hx
  have h2 := tP_le_one c d x
  unfold tS; nlinarith

/-- The shear solving its own linear equation `q' = −f q − β(1 − p²)` of the row, `q(0) = q0`. -/
noncomputable def tL (c d q0 η : ℝ) : ℝ :=
  Real.exp (-tGG c d η) * (q0 + ∫ x in (0 : ℝ)..η, Real.exp (tGG c d x) * tS c d x)

theorem tL_deriv (c d q0 η : ℝ) :
    HasDerivAt (tL c d q0) (-(tF c d η * tL c d q0 η) - (-13 / 100) * (1 - tP c d η ^ 2)) η := by
  have hc : Continuous (fun x => Real.exp (tGG c d x) * tS c d x) := by
    have := tGG_cont c d; have := tS_cont c d; fun_prop
  have hI := (hc.integral_hasStrictDerivAt 0 η).hasDerivAt
  have hE : HasDerivAt (fun u => Real.exp (-tGG c d u)) (Real.exp (-tGG c d η) * (-tF c d η)) η :=
    (tGG_deriv c d η).neg.exp
  have h := hE.mul (hI.const_add q0)
  unfold tL
  convert h using 1
  have : Real.exp (-tGG c d η) * Real.exp (tGG c d η) = 1 := by
    rw [← Real.exp_add]; simp
  unfold tS
  linear_combination (-(13 / 100 * (1 - tP c d η ^ 2))) * this

theorem tL_zero (c d q0 : ℝ) : tL c d q0 0 = q0 := by simp [tL, tGG]

theorem tL_ge {c d q0 : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) {η : ℝ} (hη : 0 ≤ η) :
    Real.exp (-tGG c d η) * q0 ≤ tL c d q0 η := by
  unfold tL
  have : 0 ≤ ∫ x in (0 : ℝ)..η, Real.exp (tGG c d x) * tS c d x :=
    intervalIntegral.integral_nonneg hη (fun x hx => mul_nonneg (Real.exp_pos _).le (tS_nonneg hc hd x hx.1))
  nlinarith [Real.exp_pos (-tGG c d η)]

theorem tL_pos {c d q0 : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hq0 : 0 < q0) {η : ℝ} (hη : 0 ≤ η) :
    0 < tL c d q0 η :=
  lt_of_lt_of_le (mul_pos (Real.exp_pos _) hq0) (tL_ge hc hd hη)

theorem tF_le (c d : ℝ) {η : ℝ} (hη : 0 ≤ η) : tF c d η ≤ η := by
  unfold tF
  have h := intervalIntegral.integral_mono_on hη ((tP_cont c d).intervalIntegrable (μ := MeasureTheory.volume) 0 η)
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 η) (fun x _ => tP_le_one c d x)
  simpa using h

theorem tGG_le (c d : ℝ) {η : ℝ} (hη : 0 ≤ η) : tGG c d η ≤ η ^ 2 / 2 := by
  unfold tGG
  have h := intervalIntegral.integral_mono_on hη ((tF_cont c d).intervalIntegrable (μ := MeasureTheory.volume) 0 η)
    (continuous_id.intervalIntegrable (μ := MeasureTheory.volume) 0 η) (fun x hx => tF_le c d hx.1)
  have e : ∫ x in (0 : ℝ)..η, id x = η ^ 2 / 2 := by simp [integral_id]
  rw [e] at h; exact h

theorem tL_decay {c q0 : ℝ} (hc : 0 ≤ c) (hq0 : 0 < q0) :
    ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - tP c 1 η) ≤ tL c 1 q0 η := by
  intro M
  filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (2 * |M| / q0)] with η h0 hη
  have hM : |M| ≤ q0 * η / 2 := by
    rw [div_le_iff₀ hq0] at hη; linarith
  have h1 : 1 - tP c 1 η = Real.exp (-tg c 1 η) := by unfold tP; ring
  rw [h1]
  have hG := tGG_le c 1 h0
  have hL := tL_ge (q0 := q0) hc zero_le_one h0
  -- M e^{−(cη + η²)} ≤ q0 e^{−η²/2} ≤ q0 e^{−G} ≤ q
  have e1 : Real.exp (-tg c 1 η) = Real.exp (-(η ^ 2 / 2)) * Real.exp (-(c * η + η ^ 2 / 2)) := by
    rw [← Real.exp_add]; unfold tg; ring_nf
  have e2 : Real.exp (-(η ^ 2 / 2)) ≤ Real.exp (-tGG c 1 η) := Real.exp_le_exp.2 (by linarith)
  have e3 : |M| * Real.exp (-(c * η + η ^ 2 / 2)) ≤ q0 := by
    have hx : 0 ≤ c * η + η ^ 2 / 2 := by positivity
    have h4 : 1 + (c * η + η ^ 2 / 2) ≤ Real.exp (c * η + η ^ 2 / 2) := by
      linarith [Real.add_one_le_exp (c * η + η ^ 2 / 2)]
    have h5 : Real.exp (-(c * η + η ^ 2 / 2)) * Real.exp (c * η + η ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have h6 : |M| ≤ q0 * Real.exp (c * η + η ^ 2 / 2) := by
      have : η ≤ 1 + (c * η + η ^ 2 / 2) := by nlinarith
      have : q0 * η ≤ q0 * Real.exp (c * η + η ^ 2 / 2) := by nlinarith
      have := mul_nonneg hq0.le h0
      linarith
    have hpos := Real.exp_pos (-(c * η + η ^ 2 / 2))
    nlinarith
  have hE1 := Real.exp_pos (-(η ^ 2 / 2))
  have hE2 := Real.exp_pos (-(c * η + η ^ 2 / 2))
  rw [e1]
  calc M * (Real.exp (-(η ^ 2 / 2)) * Real.exp (-(c * η + η ^ 2 / 2)))
      ≤ |M| * Real.exp (-(c * η + η ^ 2 / 2)) * Real.exp (-(η ^ 2 / 2)) := by
        have := le_abs_self M; nlinarith [mul_pos hE1 hE2]
    _ ≤ q0 * Real.exp (-(η ^ 2 / 2)) := mul_le_mul_of_nonneg_right e3 hE1.le
    _ ≤ q0 * Real.exp (-tGG c 1 η) := mul_le_mul_of_nonneg_left e2 hq0.le
    _ ≤ tL c 1 q0 η := by linarith

/-- The profile `f = ∫ p`, `p = 1 − exp(−(c η + η²))`, `q` solving its own linear equation with
`q(0) = q0`: every condition of the fast-approach class at the row's parameter except `p' = q`. -/
theorem toyL_all {c q0 : ℝ} (hc : 0 < c) (hq0 : 0 < q0) :
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (tF c 1) (tP c 1 η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (tL c 1 q0)
      (-(tF c 1 η * tL c 1 q0 η) - (-13 / 100) * (1 - tP c 1 η ^ 2)) (Ici 0) η) ∧
    tF c 1 0 = 0 ∧ tP c 1 0 = 0 ∧ Tendsto (tP c 1) atTop (𝓝 1) ∧
    (∀ η ∈ Ici (0 : ℝ), 0 < tL c 1 q0 η) ∧
    (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - tP c 1 η) ≤ tL c 1 q0 η) ∧ tL c 1 q0 0 = q0 :=
  ⟨fun η _ => (tF_deriv c 1 η).hasDerivWithinAt, fun η _ => (tL_deriv c 1 q0 η).hasDerivWithinAt,
    tF_zero c 1, tP_zero c 1, tP_lim hc zero_le_one, fun _ hη => tL_pos hc.le zero_le_one hq0 hη,
    tL_decay hc.le hq0, tL_zero c 1 q0⟩

theorem fs_neg_decay_max_shear_h3 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 3 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyL_all (c := 1 / 10) (q0 := 1 / 10) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, -, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, _, _, _, f, p, q, t1, t2, t3, t4, t5, t6, t7,
    a1, a2, a3, a4, a5, a6, a7, ?_⟩
  rw [t8]; intro h; linarith

theorem fs_neg_decay_max_shear_h11 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 11 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, -, t8⟩ := toyL_all (c := 1 / 10) (q0 := 1) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, w2⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, _, _, _, a1, a2, a3, a4, a5, a6, a7, a8,
    t1, t2, t3, t4, t5, t6, ?_⟩
  rw [t8]; intro h; linarith

theorem fs_neg_decay_equal_h3 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 3 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyL_all (c := 1 / 10) (q0 := 1 / 10) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, _, _, _, f, p, q, t1, t2, t3, t4, t5, t6, t7,
    a1, a2, a3, a4, a5, a6, a7, a8, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; rw [t8] at he; linarith

theorem fs_neg_decay_equal_h11 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_equal 11 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := toyL_all (c := 1 / 10) (q0 := 1 / 10) (by norm_num) (by norm_num)
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, -⟩ := attached
  refine ⟨-13 / 100, by norm_num, f, p, q, _, _, _, a1, a2, a3, a4, a5, a6, a7, a8,
    t1, t2, t3, t4, t5, t6, t7, 0, mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩; rw [t8] at he; linarith

end Checked.Trust.NCAA
