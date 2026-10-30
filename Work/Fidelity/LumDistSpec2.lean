import Work.Fidelity.SpecGaps
import Checked.Fidelity.Pins

/-!
# Spec gaps closed by `LumDistSpec2` (trust track T1)

`LumDistSpec2`, `lumDist_meets_spec2` and `lumDistSpec2_pins` now live in
`Checked/Fidelity/Pins.lean` (promoted run 1828Z); this file keeps the rejections of the gaps.

A spec-aware adversary (`SpecGaps.lean`) found four wrong definitions that satisfy
`LumDistSpec` (anchors only): three plausible (the closed branch without `(1+z)`; the
second-order cosmographic series, exact in de Sitter and Milne; Hogg's Ω_k form without the
square roots) and one contrived. It also proved that `DecelSpec` and `AngDistSpec` pin their
definitions: any function meeting them equals the program's definition on the admissible
domain.

`LumDistSpec2` adds one textbook law to the anchors: **Etherington's distance-duality**
`d_L = (1+z)² d_A`, with `d_A` any function meeting `AngDistSpec`. Then:

* `lumDist_meets_spec2`: the program's definition satisfies it;
* `lumDistSpec2_pins`: every `D` meeting it equals `lumDist` for every curvature `K`, every
  `t ≤ t₀` and every scale factor positive and continuous on `[t, t₀]`;
* all four gaps are rejected (`reject2_*`), as are all earlier mutants (`LumDistSpec2` contains
  `LumDistSpec`).

Trust statement: a theorem about `lumDist` is a theorem about every function satisfying these
textbook laws; the remaining trust is in the laws (`AngDistSpec`'s flat/closed/open formulas,
Etherington duality, and the anchors that cross-check them), not in the definition.
-/

namespace Work.Fidelity

open Real Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.Transverse
open Checked.Cosmography.BambaK Checked.Cosmography.BambaA Work.Fidelity.Gaps Checked.Fidelity

lemma exp_adm (t : ℝ) : (∀ s ∈ Set.Icc t 0, 0 < Real.exp s) ∧
    ContinuousOn Real.exp (Set.Icc t 0) :=
  ⟨fun s _ => Real.exp_pos s, Real.continuous_exp.continuousOn⟩

lemma neglog2_le : -Real.log 2 ≤ 0 := by linarith [Real.log_pos one_lt_two]

theorem reject2_closedNoZ : ¬ LumDistSpec2 gClosedNoZ := fun h =>
  gap_closedNoZ_differs (lumDistSpec2_pins _ h 1 Real.exp 0 _ neglog2_le
    (exp_adm _).1 (exp_adm _).2)

theorem reject2_omegaK : ¬ LumDistSpec2 gOmegaK := fun h =>
  gap_omegaK_differs (lumDistSpec2_pins _ h (-4) Real.exp 0 _ neglog2_le
    (exp_adm _).1 (exp_adm _).2)

theorem reject2_cosmo2 : ¬ LumDistSpec2 gCosmo2 := fun h =>
  gap_cosmo2_differs (lumDistSpec2_pins _ h 0 id 1 (1 / 2) (by norm_num)
    (fun s hs => by simp only [id]; linarith [hs.1]) continuous_id.continuousOn)

theorem reject2_qq1 : ¬ LumDistSpec2 gQQ1 := fun h => by
  have := gap_qq1_differs
  rw [lumDistSpec2_pins _ h 0 (fun s => s ^ 2) 1 (1 / 2) (by norm_num)
    (fun s hs => by have := hs.1; positivity) (continuous_pow 2).continuousOn] at this
  norm_num at this

end Work.Fidelity
