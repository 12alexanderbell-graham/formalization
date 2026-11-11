import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.FSTenth.F10ExBase
import Checked.FSTenth.F10ExFlow
import Work.Suction.F10SFlow
import Work.Suction.F10SLimit
import Work.Suction.F10SUData
import Work.Suction.F10SOData
/-! Scratch (run 2026-11-11T2228Z): the supremum argument of `Checked/FSTenth/F10ExAssemble.lean` for the
wall value f(0) = 0.01 (suction), between the certified shooting values 1.89 (undershoot) and 1.95
(overshoot); ported by `runs/2026-11-11T2228Z/scripts/port_suction_all.py`. -/

namespace Work.Suction.F10SAssemble
open Set Filter Topology Checked.FSTenth.F10ExBase Checked.FSTenth.F10ExFlow Work.Suction.F10SFlow

theorem cont_comp (α : ℝ) (η : ℝ) :
    ContinuousOn ((flowS 0.01) α) (Icc 0 η) := by
  intro s hs
  exact ((flowS_deriv 0.01 α s hs.1).continuousWithinAt).mono (fun x hx => hx.1)

theorem dist_comp1 {a b : ℝ × ℝ × ℝ} : |a.2.1 - b.2.1| ≤ dist a b := by
  have h1 : dist a.2 b.2 ≤ dist a b := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist a.2.1 b.2.1 ≤ dist a.2 b.2 := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  rw [← Real.dist_eq]; linarith

theorem dist_comp2 {a b : ℝ × ℝ × ℝ} : |a.2.2 - b.2.2| ≤ dist a b := by
  have h1 : dist a.2 b.2 ≤ dist a b := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have h2 : dist a.2.2 b.2.2 ≤ dist a.2 b.2 := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  rw [← Real.dist_eq]; linarith

theorem under_open (α₀ : ℝ) (h : Under ((flowS 0.01) α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → Under ((flowS 0.01) α) := by
  obtain ⟨η, hη, hq, hp⟩ := h
  have hc : ContinuousOn (fun s => ((flowS 0.01) α₀ s).2.1) (Icc 0 η) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (cont_comp α₀ η)
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hc
  set M := ((flowS 0.01) α₀ s0).2.1
  have hM : M < 1 := hp s0 hs0
  set ε := min (1 - M) (-((flowS 0.01) α₀ η).2.2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨δ, hδ, hcl⟩ := flowS_cont 0.01 η hη.le α₀ hε0
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_, fun s hs => ?_⟩⟩
  · have k := (hcl α hα η ⟨hη.le, le_rfl⟩)
    have k2 := (dist_comp2 (a := (flowS 0.01) α η) (b := (flowS 0.01) α₀ η)).trans_lt k
    have : ε ≤ -((flowS 0.01) α₀ η).2.2 := min_le_right _ _
    rw [abs_lt] at k2; linarith [k2.2]
  · have k := (hcl α hα s hs)
    have k2 := (dist_comp1 (a := (flowS 0.01) α s) (b := (flowS 0.01) α₀ s)).trans_lt k
    have hm : ((flowS 0.01) α₀ s).2.1 ≤ M := hmax hs
    have : ε ≤ 1 - M := min_le_left _ _
    rw [abs_lt] at k2; linarith [k2.2]

theorem over_open (α₀ : ℝ) (h : Over ((flowS 0.01) α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → Over ((flowS 0.01) α) := by
  obtain ⟨η, hη, hp, hq⟩ := h
  have hc : ContinuousOn (fun s => ((flowS 0.01) α₀ s).2.2) (Icc 0 η) :=
    (continuous_snd.comp continuous_snd).comp_continuousOn (cont_comp α₀ η)
  obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hc
  set m := ((flowS 0.01) α₀ s0).2.2
  have hm : 0 < m := hq s0 hs0
  set ε := min m (((flowS 0.01) α₀ η).2.1 - 1) with hε
  have hε0 : 0 < ε := lt_min hm (by linarith)
  obtain ⟨δ, hδ, hcl⟩ := flowS_cont 0.01 η hη.le α₀ hε0
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_, fun s hs => ?_⟩⟩
  · have k := (hcl α hα η ⟨hη.le, le_rfl⟩)
    have k2 := (dist_comp1 (a := (flowS 0.01) α η) (b := (flowS 0.01) α₀ η)).trans_lt k
    have : ε ≤ ((flowS 0.01) α₀ η).2.1 - 1 := min_le_right _ _
    rw [abs_lt] at k2; linarith [k2.1]
  · have k := (hcl α hα s hs)
    have k2 := (dist_comp2 (a := (flowS 0.01) α s) (b := (flowS 0.01) α₀ s)).trans_lt k
    have hm' : m ≤ ((flowS 0.01) α₀ s).2.2 := hmin hs
    have : ε ≤ m := min_le_left _ _
    rw [abs_lt] at k2; linarith [k2.1]

theorem deriv_Icc (α : ℝ) : ∀ t ∈ Icc (0 : ℝ) (3 / 2 : ℝ),
    HasDerivWithinAt ((flowS 0.01) α) (vH t ((flowS 0.01) α t)) (Icc 0 (3 / 2 : ℝ)) t :=
  fun t ht => (flowS_deriv 0.01 α t ht.1).mono (fun _ hx => hx.1)

theorem under_lo : Under ((flowS 0.01) 1.89) :=
  Work.Suction.F10SUData.chainC (deriv_Icc _) (flowS_zero 0.01 _)

theorem over_hi : Over ((flowS 0.01) 1.95) :=
  Work.Suction.F10SOData.chainC (deriv_Icc _) (flowS_zero 0.01 _)

/-- The K = 10 (Falkner–Skan β = 1/10, scaled) boundary-value problem with suction f(0) = 0.01 has a solution with 0 ≤ p < 1,
q > 0 and wall shear strictly between 1.89 and 1.95. -/
theorem exists_bvpS : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(10 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0.01 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.89 < q 0 ∧ q 0 < 1.95 ∧ (∀ t, 0 ≤ t → 0 ≤ p t ∧ p t < 1 ∧ 0 < q t) := by
  set lo : ℝ := 1.89 with hlo
  set hi : ℝ := 1.95 with hhi
  have hlh : lo < hi := by rw [hlo, hhi]; norm_num
  have hlo0 : (0 : ℝ) < lo := by rw [hlo]; norm_num
  have hhi2 : hi < 2 := by rw [hhi]; norm_num
  have under_lo' : Under ((flowS 0.01) lo) := by rw [hlo]; exact under_lo
  have over_hi' : Over ((flowS 0.01) hi) := by rw [hhi]; exact over_hi
  have hq0 : ∀ x, ((flowS 0.01) x 0).2.2 = x := fun x => by simp [flowS_zero 0.01]
  clear_value lo hi
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ Under ((flowS 0.01) α)} with hS
  have hloS : lo ∈ S := ⟨⟨le_rfl, hlh.le⟩, under_lo'⟩
  have hne : S.Nonempty := ⟨lo, hloS⟩
  have hbdd : BddAbove S := ⟨hi, fun α hα => hα.1.2⟩
  set a := sSup S with ha
  -- lo < a
  obtain ⟨δ1, hδ1, hU1⟩ := under_open lo under_lo'
  have hlo_lt : lo < a := by
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = lo + min (δ1 / 2) ((hi - lo) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ1 / 2) ((hi - lo) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ1 / 2) ((hi - lo) / 2) ≤ δ1 / 2 := min_le_left _ _
    have h3 : min (δ1 / 2) ((hi - lo) / 2) ≤ (hi - lo) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hU1 α' (by rw [abs_lt]; constructor <;> linarith)⟩
    exact lt_of_lt_of_le (by linarith) (le_csSup hbdd hα'S)
  -- a < hi
  obtain ⟨δ2, hδ2, hO2⟩ := over_open hi over_hi'
  have ha_lt : a < hi := by
    have hub : ∀ α ∈ S, α ≤ hi - δ2 / 2 := by
      intro α hα
      by_contra hc
      push Not at hc
      have hO := hO2 α (by rw [abs_lt]; constructor <;> linarith [hα.1.2])
      exact not_under_and_over _ hα.2 hO
    have := csSup_le hne hub
    linarith
  have hloa := le_csSup hbdd hloS
  -- no undershoot at a
  have hnU : ¬ Under ((flowS 0.01) a) := by
    intro hU
    obtain ⟨δ, hδ, hUa⟩ := under_open a hU
    obtain ⟨α', hα'd⟩ : ∃ x : ℝ, x = a + min (δ / 2) ((hi - a) / 2) := ⟨_, rfl⟩
    have h1 : 0 < min (δ / 2) ((hi - a) / 2) := lt_min (by linarith) (by linarith)
    have h2 : min (δ / 2) ((hi - a) / 2) ≤ δ / 2 := min_le_left _ _
    have h3 : min (δ / 2) ((hi - a) / 2) ≤ (hi - a) / 2 := min_le_right _ _
    have hα'S : α' ∈ S := ⟨⟨by linarith, by linarith⟩,
      hUa α' (by rw [abs_lt]; constructor <;> linarith)⟩
    have := le_csSup hbdd hα'S
    linarith
  -- no overshoot at a
  have hnO : ¬ Over ((flowS 0.01) a) := by
    intro hO
    obtain ⟨δ, hδ, hOa⟩ := over_open a hO
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact not_under_and_over _ hαS.2 (hOa α (by rw [abs_lt]; constructor <;> linarith))
  have ha0 : 0 < a := by linarith
  have ha2 : a < 2 := by linarith
  have hback : ∀ τ, 0 ≤ τ → ∀ Z : ℝ → ℝ × ℝ × ℝ,
      (∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vH t (Z t)) (Icc 0 τ) t) → Z τ = (flowS 0.01) a τ →
      Z 0 = (flowS 0.01) a 0 := by
    intro τ hτ Z hZ hZτ
    have hY : ∀ t ∈ Icc 0 τ, HasDerivWithinAt ((flowS 0.01) a) (vH t ((flowS 0.01) a t)) (Icc 0 τ) t :=
      fun t ht => (flowS_deriv 0.01 a t ht.1).mono (fun x hx => hx.1)
    exact (unique_left hτ hY hZ hZτ.symm (⟨le_rfl, hτ⟩ : (0 : ℝ) ∈ Icc 0 τ)).symm
  obtain ⟨d1, d2, d3, hlim, hcl⟩ := Work.Suction.F10SLimit.no_eventS (by norm_num) (by norm_num) ha0 ha2
    ((flowS 0.01) a) (flowS_zero 0.01 a) (flowS_deriv 0.01 a) hback hnU hnO
  refine ⟨fun s => ((flowS 0.01) a s).1, fun s => ((flowS 0.01) a s).2.1, fun s => ((flowS 0.01) a s).2.2,
    d1, d2, d3, ?_, ?_, hlim, ?_, ?_, ?_⟩
  · simp [flowS_zero 0.01]
  · simp [flowS_zero 0.01]
  · show lo < ((flowS 0.01) a 0).2.2
    rw [hq0]; exact hlo_lt
  · show ((flowS 0.01) a 0).2.2 < hi
    rw [hq0]; exact ha_lt
  · exact hcl

end Work.Suction.F10SAssemble
