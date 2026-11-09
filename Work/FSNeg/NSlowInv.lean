import Checked.FalknerSkan.LimitCore
import Mathlib
/-! Run 2026-11-09T0828Z (moved from the scratch of fork B): Lemma I of the β < 0 research note —
forward invariance of the Slow region for f' = p, p' = q, q' = −K f q + 1 − p². -/

namespace Work.FSNeg.NSlowInv
open Set Filter Topology Checked.FalknerSkan.LimitCore

/-- A function whose left values are positive and that has a positive derivative
at a zero is impossible: used at a first touch. -/
theorem no_touch_from_above {g : ℝ → ℝ} {d x a : ℝ} (hax : a < x) (h : HasDerivAt g d x)
    (hd : 0 < d) (h0 : g x = 0) (hpos : ∀ s ∈ Ioo a x, 0 < g s) : False := by
  have h1 := left_neg h hd h0
  have h2 : ∀ᶠ s in 𝓝[<] x, 0 < g s := by
    filter_upwards [Ioo_mem_nhdsLT hax] with s hs using hpos s hs
  obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
  linarith

theorem ge_of_left {g : ℝ → ℝ} {x a c : ℝ} (hax : a < x) (h : ContinuousAt g x)
    (hle : ∀ s ∈ Ioo a x, c ≤ g s) : c ≤ g x :=
  ge_of_tendsto (h.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [Ioo_mem_nhdsLT hax] with s hs using hle s hs)

theorem le_of_left {g : ℝ → ℝ} {x a c : ℝ} (hax : a < x) (h : ContinuousAt g x)
    (hle : ∀ s ∈ Ioo a x, g s ≤ c) : g x ≤ c :=
  le_of_tendsto (h.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [Ioo_mem_nhdsLT hax] with s hs using hle s hs)

/-- **Lemma I** (Slow region forward invariant). With Kθ ≥ μ + 2/μ, the strict conditions
0 ≤ p < 1, 0 < q < μ(1 − p), θ < f at η₀ persist for all η ≥ η₀. -/
theorem slow_inv {K μ θ : ℝ} (hK : 0 < K) (hμ : 0 < μ) (hθ : μ + 2 / μ ≤ K * θ)
    {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(K * f η * q η) + 1 - p η ^ 2) (Ici 0) η)
    {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (h1 : 0 ≤ p η₀) (h2 : p η₀ < 1) (h3 : 0 < q η₀)
    (h4 : q η₀ < μ * (1 - p η₀)) (h5 : θ < f η₀) :
    ∀ η ∈ Ici η₀, 0 ≤ p η ∧ p η < 1 ∧ 0 < q η ∧ q η < μ * (1 - p η) ∧ θ < f η := by
  -- the four strict conditions (0 ≤ p follows from q > 0)
  have main : ∀ T, η₀ ≤ T → ∀ s ∈ Icc η₀ T, p s < 1 ∧ 0 < q s ∧ q s < μ * (1 - p s) ∧ θ < f s := by
    intro T hT
    by_contra hcon
    push Not at hcon
    set S : Set ℝ := Icc η₀ T ∩ {s | 1 ≤ p s ∨ q s ≤ 0 ∨ μ * (1 - p s) ≤ q s ∨ f s ≤ θ} with hSdef
    have hpc := cont_of hp (b := T) hη₀
    have hqc := cont_of hq (b := T) hη₀
    have hfc := cont_of hf (b := T) hη₀
    have hSc : IsClosed S := by
      have e1 : IsClosed (Icc η₀ T ∩ p ⁻¹' Ici 1) := hpc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have e2 : IsClosed (Icc η₀ T ∩ q ⁻¹' Iic 0) := hqc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have e3 : IsClosed (Icc η₀ T ∩ (fun s => q s - μ * (1 - p s)) ⁻¹' Ici 0) :=
        (hqc.sub (continuousOn_const.mul (continuousOn_const.sub hpc))).preimage_isClosed_of_isClosed
          isClosed_Icc isClosed_Ici
      have e4 : IsClosed (Icc η₀ T ∩ f ⁻¹' Iic θ) := hfc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have : S = (Icc η₀ T ∩ p ⁻¹' Ici 1) ∪ (Icc η₀ T ∩ q ⁻¹' Iic 0) ∪
          (Icc η₀ T ∩ (fun s => q s - μ * (1 - p s)) ⁻¹' Ici 0) ∪ (Icc η₀ T ∩ f ⁻¹' Iic θ) := by
        ext s
        simp only [hSdef, mem_inter_iff, mem_ofPred_eq, mem_union, mem_preimage, mem_Ici, mem_Iic,
          sub_nonneg]
        tauto
      rw [this]
      exact ((e1.union e2).union e3).union e4
    obtain ⟨s₀, hs₀, hbad⟩ := hcon
    have hne : S.Nonempty := by
      refine ⟨s₀, hs₀, ?_⟩
      simp only [mem_ofPred_eq]
      by_contra hn
      push Not at hn
      obtain ⟨a1, a2, a3, a4⟩ := hn
      exact absurd (hbad a1 a2 a3) (not_le.2 a4)
    have hbdd : BddBelow S := ⟨η₀, fun s hs => hs.1.1⟩
    set τ := sInf S with hτ
    have hτS : τ ∈ S := hSc.csInf_mem hne hbdd
    have hτ0 : η₀ ≤ τ := hτS.1.1
    have hτT : τ ≤ T := hτS.1.2
    have hτne : τ ≠ η₀ := by
      intro he
      have := hτS.2
      rw [he] at this
      rcases this with h | h | h | h <;> linarith
    have hτlt : η₀ < τ := lt_of_le_of_ne hτ0 (Ne.symm hτne)
    have hτpos : 0 < τ := lt_of_le_of_lt hη₀ hτlt
    -- good on [η₀, τ)
    have good : ∀ s ∈ Ico η₀ τ, p s < 1 ∧ 0 < q s ∧ q s < μ * (1 - p s) ∧ θ < f s := by
      intro s hs
      have hsS : s ∉ S := notMem_of_lt_csInf hs.2 hbdd
      have hsI : s ∈ Icc η₀ T := ⟨hs.1, hs.2.le.trans hτT⟩
      have : ¬ (1 ≤ p s ∨ q s ≤ 0 ∨ μ * (1 - p s) ≤ q s ∨ f s ≤ θ) := fun h => hsS ⟨hsI, h⟩
      push Not at this
      exact this
    -- p strictly increasing, f nondecreasing on [η₀, τ]
    have hpm : StrictMonoOn p (Icc η₀ τ) :=
      smono hp hη₀ (fun x hx => (good x ⟨hx.1.le, hx.2⟩).2.1)
    have hp_ge : ∀ s ∈ Icc η₀ τ, p η₀ ≤ p s := fun s hs =>
      hpm.monotoneOn ⟨le_rfl, hτ0⟩ hs hs.1
    have hfm : MonotoneOn f (Icc η₀ τ) :=
      mono hf hη₀ (fun x hx => le_trans h1 (hp_ge x ⟨hx.1.le, hx.2.le⟩))
    have hfτ : θ < f τ := lt_of_lt_of_le h5 (hfm ⟨le_rfl, hτ0⟩ ⟨hτ0, le_rfl⟩ hτ0)
    have hpτ0 : 0 ≤ p τ := le_trans h1 (hp_ge τ ⟨hτ0, le_rfl⟩)
    -- (1 − p) e^{μη} nondecreasing
    have hG : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (1 - p s) * Real.exp (μ * s))
        (Real.exp (μ * η) * (μ * (1 - p η) - q η)) (Ici 0) η := by
      intro η hη
      have he : HasDerivWithinAt (fun s => Real.exp (μ * s)) (Real.exp (μ * η) * μ) (Ici 0) η :=
        (((hasDerivAt_id η).const_mul μ).exp.congr_deriv (by simp)).hasDerivWithinAt
      have := ((hp η hη).const_sub 1).mul he
      exact this.congr_deriv (by ring)
    have hGm := mono hG hη₀ (b := τ) (fun x hx => by
      have := good x ⟨hx.1.le, hx.2⟩
      exact mul_nonneg (Real.exp_pos _).le (by linarith))
    have hgτ : 0 < 1 - p τ := by
      have := hGm ⟨le_rfl, hτ0⟩ ⟨hτ0, le_rfl⟩ hτ0
      simp only at this
      have hA : 0 < (1 - p η₀) * Real.exp (μ * η₀) := mul_pos (by linarith) (Real.exp_pos _)
      have hB := lt_of_lt_of_le hA this
      exact pos_of_mul_pos_left hB (Real.exp_pos _).le
    have hpτ1 : p τ < 1 := by linarith
    -- W = q − μ(1 − p) < 0 at τ
    have hqA : HasDerivAt q (-(K * f τ * q τ) + 1 - p τ ^ 2) τ := at_of hq hτpos
    have hpA : HasDerivAt p (q τ) τ := at_of hp hτpos
    have hWA : HasDerivAt (fun s => q s - μ * (1 - p s))
        ((-(K * f τ * q τ) + 1 - p τ ^ 2) - μ * (0 - q τ)) τ :=
      hqA.sub (((hasDerivAt_const τ (1 : ℝ)).sub hpA).const_mul μ)
    have hWle : q τ - μ * (1 - p τ) ≤ 0 :=
      le_of_left (g := fun s => q s - μ * (1 - p s)) hτlt hWA.continuousAt (fun s hs => by
        have := (good s ⟨hs.1.le, hs.2⟩).2.2.1; linarith)
    have hKf : μ + 2 / μ < K * f τ := lt_of_le_of_lt hθ (mul_lt_mul_of_pos_left hfτ hK)
    have hμKf : μ * μ + 2 < μ * (K * f τ) := by
      have := mul_lt_mul_of_pos_left hKf hμ
      rwa [mul_add, mul_div_cancel₀ _ hμ.ne'] at this
    have hW : q τ < μ * (1 - p τ) := by
      rcases lt_or_eq_of_le hWle with h | h
      · linarith
      · exfalso
        -- derivative at the touch: g (μ² − μKf + 2 − g) < 0
        have hqeq : q τ = μ * (1 - p τ) := by linarith
        have hd : 0 < -((-(K * f τ * q τ) + 1 - p τ ^ 2) - μ * (0 - q τ)) := by
          rw [hqeq]
          have : (-(K * f τ * (μ * (1 - p τ))) + 1 - p τ ^ 2) - μ * (0 - μ * (1 - p τ)) =
              (1 - p τ) * (μ * μ - μ * (K * f τ) + 2 - (1 - p τ)) := by ring
          rw [this]
          have : μ * μ - μ * (K * f τ) + 2 - (1 - p τ) < 0 := by linarith
          nlinarith
        exact no_touch_from_above (g := fun s => -(q s - μ * (1 - p s))) hτlt hWA.neg hd (by linarith)
          (fun s hs => by have := (good s ⟨hs.1.le, hs.2⟩).2.2.1; linarith)
    -- q > 0 at τ
    have hqge : 0 ≤ q τ := ge_of_left hτlt hqA.continuousAt (fun s hs => (good s ⟨hs.1.le, hs.2⟩).2.1.le)
    have hqτ : 0 < q τ := by
      rcases lt_or_eq_of_le hqge with h | h
      · exact h
      · exfalso
        have hd : 0 < -(K * f τ * q τ) + 1 - p τ ^ 2 := by rw [← h]; nlinarith
        exact no_touch_from_above hτlt hqA hd h.symm (fun s hs => (good s ⟨hs.1.le, hs.2⟩).2.1)
    rcases hτS.2 with h | h | h | h <;> linarith
  intro η hη
  have hη' : η₀ ≤ η := hη
  obtain ⟨a1, a2, a3, a4⟩ := main η hη' η ⟨hη', le_rfl⟩
  refine ⟨?_, a1, a2, a3, a4⟩
  have hpm : MonotoneOn p (Icc η₀ η) :=
    mono hp hη₀ (fun x hx => (main η hη' x ⟨hx.1.le, hx.2.le⟩).2.1.le)
  exact le_trans h1 (hpm ⟨le_rfl, hη'⟩ ⟨hη', le_rfl⟩ hη')

end Work.FSNeg.NSlowInv

