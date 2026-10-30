import Work.Fidelity.SpecGaps

/-!
# `LumDistSpec2`: a luminosity-distance specification that pins the definition (trust track T1)

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
open Checked.Cosmography.BambaK Checked.Cosmography.BambaA Work.Fidelity.Gaps

/-- Anchors plus Etherington distance duality `d_L = (1+z)² d_A`. -/
structure LumDistSpec2 (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  base : LumDistSpec D
  etherington : ∃ DA : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ, AngDistSpec DA ∧
    ∀ K (a : ℝ → ℝ) t₀ t, t ≤ t₀ → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
      ContinuousOn a (Set.Icc t t₀) → D K a t₀ t = (1 + redshift a t₀ t) ^ 2 * DA K a t₀ t

lemma onePlusRedshift_ne {a : ℝ → ℝ} {t₀ t : ℝ} (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) : 1 + redshift a t₀ t ≠ 0 := by
  obtain ⟨h0, h00⟩ := ms_ends htt hpos
  unfold redshift; rw [add_sub_cancel]; exact div_ne_zero h00 h0

theorem lumDist_meets_spec2 : LumDistSpec2 lumDist where
  base := lumDist_meets_spec
  etherington := ⟨angDist, angDist_meets_spec, fun K a t₀ t htt hpos _ => by
    have := onePlusRedshift_ne htt hpos
    unfold angDist; field_simp⟩

/-- **Pinning:** the specification determines the luminosity distance on the whole admissible
domain. -/
theorem lumDistSpec2_pins (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpec2 D) (K : ℝ)
    (a : ℝ → ℝ) (t₀ t : ℝ) (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hcont : ContinuousOn a (Set.Icc t t₀)) : D K a t₀ t = lumDist K a t₀ t := by
  obtain ⟨DA, hDA, hE⟩ := h.etherington
  rw [hE K a t₀ t htt hpos hcont, angDistSpec_pins DA hDA K a t₀ t htt hpos hcont]
  have := onePlusRedshift_ne htt hpos
  unfold angDist; field_simp

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

namespace Work.Fidelity

open Checked.Cosmography

/-- `HubbleSpec` pins `hubble` for every positive scale factor differentiable at `t`
(its `logDeriv` law `H = d ln a/dt` and uniqueness of derivatives). -/
theorem hubbleSpec_pins (H : (ℝ → ℝ) → ℝ → ℝ) (h : HubbleSpec H) (a : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) : H a t = hubble a t := by
  have h1 := h.logDeriv a t ha hd
  have h2 := hd.hasDerivAt.log ha.ne'
  exact h1.unique h2

end Work.Fidelity
