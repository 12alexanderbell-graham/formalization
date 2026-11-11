import Mathlib
import Work.FSRev.RAssemble
import Work.FSRev.R1988Over
import Work.FSRev.R1988Slow
import Work.FSRev.R1988Tube
import Work.FSAtt.N1988Core
import Work.FSAtt.N1988Lo
import Work.FSAtt.N1988Hi

/-!
# Falkner–Skan at β = −0.1988: the reversed-flow branch (frozen in run 2026-11-11T1228Z, commit c9be92b; statements unchanged, proofs added)

Parts 2/5. Written in `runs/2026-11-11T1228Z/lean/` (auditor role under the LOCK of run 0828Z); to move to
`Work/FalknerSkan/Neg1988Rev.lean` unchanged when the LOCK is released.

Fazio (2012, arXiv:1212.5057v1, typeset p. 16, read blind in run 1028Z) prints for β = −0.1988 the attached
wall shear 0.005221 and the reversed-flow wall shear −0.005158. Independent numerics: run 1028Z referee
(collocation with the parabolic-cylinder tail) −0.0051574; this run (mpmath Taylor shooting, scaled
K = 2500/497) −0.00515742018. The printed reversed value is off in the fourth significant digit.

Statements: `fs_neg1988_reversed` is `Work.FalknerSkan.NegReversed.fs_neg_tenth_reversed` with
β = −1988/10000 and the window (−0.00515743, −0.00515741); `fs_neg1988_printed_reversed_overshoots`
says that the initial-value problem with Fazio's printed reversed wall value overshoots (f' > 1 somewhere),
so that value is the wall shear of no solution with f' ≤ 1 (both branches have f' ≤ 1);
`fs_neg1988_two_decay` is `fs_neg_tenth_two_decay` with β = −1988/10000 (non-uniqueness in the decay class
just above separation). Do not change them; prove them.
-/

namespace Work.FalknerSkan.Neg1988Rev

open Set Filter Topology

theorem sqrtK_pos : 0 < Real.sqrt (2500 / 497 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem hK : (-1 / (2500 / 497 : ℝ)) = -1988 / 10000 := by norm_num

theorem lo_pos : 11567117 / 1000000000 / Real.sqrt (2500 / 497) < (0.00515743 : ℝ) := by
  rw [div_lt_iff₀ sqrtK_pos]
  have h : 11567117 / 1000000000 / 0.00515743 < Real.sqrt (2500 / 497 : ℝ) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : (0.00515743 : ℝ) * (11567117 / 1000000000 / 0.00515743) < 0.00515743 * Real.sqrt (2500 / 497) :=
    mul_lt_mul_of_pos_left h (by norm_num)
  have h3 : (0.00515743 : ℝ) * (11567117 / 1000000000 / 0.00515743) = 11567117 / 1000000000 := by norm_num
  linarith

theorem hi_pos : (0.00515741 : ℝ) < 11567073 / 1000000000 / Real.sqrt (2500 / 497) := by
  rw [lt_div_iff₀ sqrtK_pos]
  have h : Real.sqrt (2500 / 497 : ℝ) < 11567073 / 1000000000 / 0.00515741 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h2 : (0.00515741 : ℝ) * Real.sqrt (2500 / 497) < 0.00515741 * (11567073 / 1000000000 / 0.00515741) :=
    mul_lt_mul_of_pos_left h (by norm_num)
  have h3 : (0.00515741 : ℝ) * (11567073 / 1000000000 / 0.00515741) = 11567073 / 1000000000 := by norm_num
  linarith

theorem lo_bound : (-0.00515743 : ℝ) < -11567117 / 1000000000 / Real.sqrt (2500 / 497) := by
  rw [neg_div, neg_div]; linarith [lo_pos]

theorem hi_bound : -11567073 / 1000000000 / Real.sqrt (2500 / 497) < (-0.00515741 : ℝ) := by
  rw [neg_div, neg_div]; linarith [hi_pos]

/-- Falkner–Skan with β = −1988/10000: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, whose wall value satisfies −0.00515743 < q(0) < −0.00515741 (reversed flow at the wall). -/
theorem fs_neg1988_reversed :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.00515743 < q 0 ∧ q 0 < -0.00515741 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Work.FSRev.RAssemble.core_rev (K := 2500 / 497) (by norm_num) (by norm_num)
      Work.FSRev.R1988Over.chain Work.FSRev.R1988Slow.chain Work.FSRev.R1988Tube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, lo_bound.trans w1, w2.trans hi_bound⟩
  rw [← hK]; exact a3 η hη

/-- Falkner–Skan with β = −1988/10000, the printed reversed-flow wall value: every solution (f, p, q) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with f(0) = 0, p(0) = 0 and q(0) = −0.005158 has p(η) > 1 at
some η > 0. -/
theorem fs_neg1988_printed_reversed_overshoots (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = -0.005158) :
    ∃ η > 0, 1 < p η := by
  sorry

/-- Falkner–Skan with β = −1988/10000: there are two solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on
[0, ∞) and, for every M, eventually M (1 − p) ≤ q, whose values q(0) and q₂(0) differ. -/
theorem fs_neg1988_two_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-1988 / 10000) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ := fs_neg1988_reversed
  obtain ⟨f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8⟩ :=
    Work.FSAtt.N1988Core.exists_core Work.FSAtt.N1988Lo.chain Work.FSAtt.N1988Hi.chain
  have h00 : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.2 le_rfl
  have hmono : MonotoneOn p₂ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := q₂) (convex_Ici 0)
      (HasDerivWithinAt.continuousOn (fun x hx => b2 x hx)) (fun x hx => ?_) (fun x hx => ?_)
    · exact (b2 x (interior_subset hx)).mono interior_subset
    · exact (b7 x (interior_subset hx)).le
  have hp₂ : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1 := by
    intro η hη
    have h0 : p₂ 0 ≤ p₂ η := hmono h00 hη hη
    have h1 : p₂ η ≤ 1 := ge_of_tendsto b6
      (eventually_atTop.2 ⟨η, fun t ht => hmono hη (le_trans hη ht) ht⟩)
    constructor <;> linarith
  refine ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, a7, hp₂, a8, b8, ?_⟩
  have := b7 0 h00
  intro h; rw [h] at w2; linarith

end Work.FalknerSkan.Neg1988Rev
