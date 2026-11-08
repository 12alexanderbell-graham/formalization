import Mathlib
import Work.FalknerSkan.MonotoneExists

/-!
# Same wall shear of monotone solutions: the blind restatement, closed (run 2026-11-08T1028Z)

`IsSol` and the two uniqueness theorems are the blind restater's text (Sonnet, from the claims in
words only; `runs/2026-11-08T1028Z/blind2/MEBlind.lean`), copied verbatim with their placeholder
proofs replaced by proofs from the program's `hiemenz_monotone_same_wall_shear` and
`homann_monotone_same_wall_shear`; `toSys` (program text) converts the blind iterated-`derivWithin`
encoding. The blind restater's two existence statements ask for `ContDiffOn ℝ ⊤` (in current
Mathlib `⊤` is analyticity) and are not closed here: the program's existence headlines assert the
derivative chain of the first-order system only (recorded in the run record).
-/

namespace Blind.MonotoneExists

open Filter Set Topology

/-- `f` solves `f''' + c f f'' + 1 - (f')² = 0` on `[0,∞)` with `f(0)=0`, `f'(0)=0`, `f' → 1`;
derivatives are one-sided at 0 (`derivWithin` on `Ici 0`), regularity `C^n` on `Ici 0`. -/
def IsSol (n : WithTop ℕ∞) (c : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ n f (Ici 0) ∧
  (∀ x ∈ Ici (0:ℝ),
    derivWithin (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) x
      + c * f x * derivWithin (derivWithin f (Ici 0)) (Ici 0) x + 1
      - (derivWithin f (Ici 0) x) ^ 2 = 0) ∧
  f 0 = 0 ∧ derivWithin f (Ici 0) 0 = 0 ∧
  Tendsto (derivWithin f (Ici 0)) atTop (𝓝 1)

/-- From the blind `IsSol 3 c` to the program's first-order system with derivatives within
`Ici 0` (program lemma, not part of the blind text). -/
theorem toSys {c : ℝ} {f : ℝ → ℝ} (h : IsSol 3 c f) :
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f (derivWithin f (Ici 0) x) (Ici 0) x) ∧
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (derivWithin f (Ici 0))
      (derivWithin (derivWithin f (Ici 0)) (Ici 0) x) (Ici 0) x) ∧
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (derivWithin (derivWithin f (Ici 0)) (Ici 0))
      (-(c * f x * derivWithin (derivWithin f (Ici 0)) (Ici 0) x) - 1 +
        derivWithin f (Ici 0) x ^ 2) (Ici 0) x) ∧
    f 0 = 0 ∧ derivWithin f (Ici 0) 0 = 0 ∧ Tendsto (derivWithin f (Ici 0)) atTop (𝓝 1) := by
  obtain ⟨hc, hode, h0, h1, hlim⟩ := h
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have c1 : ContDiffOn ℝ 2 (derivWithin f (Ici 0)) (Ici 0) := hc.derivWithin hu (by norm_num)
  have c2 : ContDiffOn ℝ 1 (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) :=
    c1.derivWithin hu (by norm_num)
  refine ⟨fun x hx => ((hc.differentiableOn (by norm_num)) x hx).hasDerivWithinAt,
    fun x hx => ((c1.differentiableOn (by norm_num)) x hx).hasDerivWithinAt,
    fun x hx => (((c2.differentiableOn (by norm_num)) x hx).hasDerivWithinAt).congr_deriv
      (by linarith [hode x hx]), h0, h1, hlim⟩

/-- Hiemenz: two `C^3` solutions with `f'' > 0` on `[0,∞)` have equal wall shear. -/
theorem hiemenz_unique_blind (f g : ℝ → ℝ) (hf : IsSol 3 1 f) (hg : IsSol 3 1 g)
    (hf2 : ∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin f (Ici 0)) (Ici 0) x)
    (hg2 : ∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin g (Ici 0)) (Ici 0) x) :
    derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 =
      derivWithin (derivWithin g (Ici 0)) (Ici 0) 0 := by
  obtain ⟨A1, B1, C1, D1, E1, F1⟩ := Blind.MonotoneExists.toSys hf
  obtain ⟨A2, B2, C2, D2, E2, F2⟩ := Blind.MonotoneExists.toSys hg
  exact Work.FalknerSkan.MonotoneExists.hiemenz_monotone_same_wall_shear _ _ _ _ _ _ A1 B1
    (fun x hx => (C1 x hx).congr_deriv (by ring)) D1 E1 F1 hf2 A2 B2
    (fun x hx => (C2 x hx).congr_deriv (by ring)) D2 E2 F2 hg2

/-- Homann: two `C^3` solutions with `f'' > 0` on `[0,∞)` have equal wall shear. -/
theorem homann_unique_blind (f g : ℝ → ℝ) (hf : IsSol 3 2 f) (hg : IsSol 3 2 g)
    (hf2 : ∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin f (Ici 0)) (Ici 0) x)
    (hg2 : ∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin g (Ici 0)) (Ici 0) x) :
    derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 =
      derivWithin (derivWithin g (Ici 0)) (Ici 0) 0 := by
  obtain ⟨A1, B1, C1, D1, E1, F1⟩ := Blind.MonotoneExists.toSys hf
  obtain ⟨A2, B2, C2, D2, E2, F2⟩ := Blind.MonotoneExists.toSys hg
  exact Work.FalknerSkan.MonotoneExists.homann_monotone_same_wall_shear _ _ _ _ _ _ A1 B1
    (fun x hx => (C1 x hx).congr_deriv (by ring)) D1 E1 F1 hf2 A2 B2
    (fun x hx => (C2 x hx).congr_deriv (by ring)) D2 E2 F2 hg2

end Blind.MonotoneExists
