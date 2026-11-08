import Mathlib
import Work.Homann.HmExBase
import Work.Homann.HmExFlow
import Work.Homann.HmExLimit
import Work.Homann.HmUDataC
import Work.Homann.HmODataC

/-!
# Homann existence: the shooting argument (run 2026-11-08T0428Z, ported from `Work.Homann.HExAssemble`)

The clamped flow `HExFlow.flow α` from (0, 0, α) depends continuously on α (`flow_cont`), so the
two events `Under` and `Over` are open in α (`under_open`, `over_open`) and exclusive
(`HExBase.not_under_and_over`). The certified clamped chains give `Under` at α = 1.3119376938 and
`Over` at α = 1.3119376939 (`HUDataC.chainC`, `HODataC.chainC`). The supremum α* of the
undershooting parameters in between has neither event, so by `HExLimit.no_event` its flow is a
solution of the Homann boundary-value problem on [0, ∞), and 1.3119376938 < α* < 1.3119376939.
-/

namespace Work.Homann.HmExAssemble
open Set Filter Topology Work.Homann.HmExBase Work.Homann.HmExFlow

theorem cont_comp (α : ℝ) (η : ℝ) :
    ContinuousOn (flow α) (Icc 0 η) := by
  intro s hs
  exact ((flow_deriv α s hs.1).continuousWithinAt).mono (fun x hx => hx.1)

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

theorem under_open (α₀ : ℝ) (h : Under (flow α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → Under (flow α) := by
  obtain ⟨η, hη, hq, hp⟩ := h
  have hc : ContinuousOn (fun s => (flow α₀ s).2.1) (Icc 0 η) :=
    (continuous_fst.comp continuous_snd).comp_continuousOn (cont_comp α₀ η)
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hc
  set M := (flow α₀ s0).2.1
  have hM : M < 1 := hp s0 hs0
  set ε := min (1 - M) (-(flow α₀ η).2.2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨δ, hδ, hcl⟩ := flow_cont η hη.le α₀ hε0
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_, fun s hs => ?_⟩⟩
  · have k := (hcl α hα η ⟨hη.le, le_rfl⟩)
    have k2 := (dist_comp2 (a := flow α η) (b := flow α₀ η)).trans_lt k
    have : ε ≤ -(flow α₀ η).2.2 := min_le_right _ _
    rw [abs_lt] at k2; linarith [k2.2]
  · have k := (hcl α hα s hs)
    have k2 := (dist_comp1 (a := flow α s) (b := flow α₀ s)).trans_lt k
    have hm : (flow α₀ s).2.1 ≤ M := hmax hs
    have : ε ≤ 1 - M := min_le_left _ _
    rw [abs_lt] at k2; linarith [k2.2]

theorem over_open (α₀ : ℝ) (h : Over (flow α₀)) :
    ∃ δ > 0, ∀ α, |α - α₀| < δ → Over (flow α) := by
  obtain ⟨η, hη, hp, hq⟩ := h
  have hc : ContinuousOn (fun s => (flow α₀ s).2.2) (Icc 0 η) :=
    (continuous_snd.comp continuous_snd).comp_continuousOn (cont_comp α₀ η)
  obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, hη.le⟩⟩ hc
  set m := (flow α₀ s0).2.2
  have hm : 0 < m := hq s0 hs0
  set ε := min m ((flow α₀ η).2.1 - 1) with hε
  have hε0 : 0 < ε := lt_min hm (by linarith)
  obtain ⟨δ, hδ, hcl⟩ := flow_cont η hη.le α₀ hε0
  refine ⟨δ, hδ, fun α hα => ⟨η, hη, ?_, fun s hs => ?_⟩⟩
  · have k := (hcl α hα η ⟨hη.le, le_rfl⟩)
    have k2 := (dist_comp1 (a := flow α η) (b := flow α₀ η)).trans_lt k
    have : ε ≤ (flow α₀ η).2.1 - 1 := min_le_right _ _
    rw [abs_lt] at k2; linarith [k2.1]
  · have k := (hcl α hα s hs)
    have k2 := (dist_comp2 (a := flow α s) (b := flow α₀ s)).trans_lt k
    have hm' : m ≤ (flow α₀ s).2.2 := hmin hs
    have : ε ≤ m := min_le_left _ _
    rw [abs_lt] at k2; linarith [k2.1]

theorem deriv_Icc (α : ℝ) : ∀ t ∈ Icc (0 : ℝ) 6,
    HasDerivWithinAt (flow α) (vH t (flow α t)) (Icc 0 6) t :=
  fun t ht => (flow_deriv α t ht.1).mono (fun _ hx => hx.1)

theorem under_lo : Under (flow 1.3119376938) :=
  Work.Homann.HmUDataC.chainC (deriv_Icc _) (flow_zero _)

theorem over_hi : Over (flow 1.3119376939) :=
  Work.Homann.HmODataC.chainC (deriv_Icc _) (flow_zero _)

/-- The Homann boundary-value problem has a solution with wall shear strictly between
1.3119376938 and 1.3119376939. -/
theorem exists_bvp : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  set lo : ℝ := 1.3119376938 with hlo
  set hi : ℝ := 1.3119376939 with hhi
  have hlh : lo < hi := by rw [hlo, hhi]; norm_num
  have hlo0 : (0 : ℝ) < lo := by rw [hlo]; norm_num
  have hhi2 : hi < 2 := by rw [hhi]; norm_num
  have under_lo' : Under (flow lo) := by rw [hlo]; exact under_lo
  have over_hi' : Over (flow hi) := by rw [hhi]; exact over_hi
  have hq0 : ∀ x, (flow x 0).2.2 = x := fun x => by simp [flow_zero]
  clear_value lo hi
  set S : Set ℝ := {α | α ∈ Icc lo hi ∧ Under (flow α)} with hS
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
  have hnU : ¬ Under (flow a) := by
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
  have hnO : ¬ Over (flow a) := by
    intro hO
    obtain ⟨δ, hδ, hOa⟩ := over_open a hO
    obtain ⟨α, hαS, hαa⟩ := exists_lt_of_lt_csSup hne (show a - δ < a by linarith)
    have hle : α ≤ a := le_csSup hbdd hαS
    exact not_under_and_over _ hαS.2 (hOa α (by rw [abs_lt]; constructor <;> linarith))
  have ha0 : 0 < a := by linarith
  have ha2 : a < 2 := by linarith
  have hback : ∀ τ, 0 ≤ τ → ∀ Z : ℝ → ℝ × ℝ × ℝ,
      (∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vH t (Z t)) (Icc 0 τ) t) → Z τ = flow a τ →
      Z 0 = flow a 0 := by
    intro τ hτ Z hZ hZτ
    have hY : ∀ t ∈ Icc 0 τ, HasDerivWithinAt (flow a) (vH t (flow a t)) (Icc 0 τ) t :=
      fun t ht => (flow_deriv a t ht.1).mono (fun x hx => hx.1)
    exact (unique_left hτ hY hZ hZτ.symm (⟨le_rfl, hτ⟩ : (0 : ℝ) ∈ Icc 0 τ)).symm
  obtain ⟨d1, d2, d3, hlim⟩ := Work.Homann.HmExLimit.no_event ha0 ha2 (flow a) (flow_zero a)
    (flow_deriv a) hback hnU hnO
  refine ⟨fun s => (flow a s).1, fun s => (flow a s).2.1, fun s => (flow a s).2.2,
    d1, d2, d3, ?_, ?_, hlim, ?_, ?_⟩
  · simp [flow_zero]
  · simp [flow_zero]
  · show lo < (flow a 0).2.2
    rw [hq0]; exact hlo_lt
  · show (flow a 0).2.2 < hi
    rw [hq0]; exact ha_lt

end Work.Homann.HmExAssemble
