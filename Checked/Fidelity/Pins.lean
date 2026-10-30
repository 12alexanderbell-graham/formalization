import Checked.Fidelity.MoreSpecs

/-!
# Pinning theorems: specifications that determine the definitions (trust track T1)

A specification `XSpec` (textbook laws + closed-form anchors, written blind to the mutation
benchmark, `Checked/Fidelity/LumDistSpec.lean`, `MoreSpecs.lean`) *pins* a definition when every
function meeting it equals the program's definition on the physical domain. Then a theorem about
the definition is a theorem about whatever satisfies the textbook laws: no wrong definition can
hide on that domain. Remaining trust is in the laws themselves (referee report
`runs/2026-10-30T1828Z/referee_specs.md`: all fields physically correct, closed forms checked
with sympy).

* `decelSpec_pins`, `angDistSpec_pins` (found by the spec-aware adversary, `Work/Fidelity/SpecGaps.lean`);
* `hubbleSpec_pins` (logarithmic-derivative law);
* `LumDistSpec2` = `LumDistSpec` + Etherington duality `d_L = (1+z)² d_A` (closes the four
  gaps the adversary found in the anchors-only `LumDistSpec`), `lumDist_meets_spec2`,
  `lumDistSpec2_pins`.
-/

namespace Checked.Fidelity

open Real Filter Topology Checked.Cosmography Checked.Cosmography.BambaY
open Checked.Cosmography.BambaK Checked.Cosmography.BambaA Checked.Cosmography.Transverse

/-- No gap in `DecelSpec`: on every positive scale factor, twice differentiable at `t` with
`ȧ(t) ≠ 0`, any `Q` meeting the spec equals `decel`. -/
theorem decelSpec_pins (Q : (ℝ → ℝ) → ℝ → ℝ) (h : DecelSpec Q) (a a' : ℝ → ℝ) (a'' t : ℝ)
    (h1 : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) (h2 : HasDerivAt a' a'' t) (ha : 0 < a t)
    (hd : a' t ≠ 0) : Q a t = decel a t := by
  rw [h.formula a a' a'' t h1 h2 ha hd, ms_decel_formula a a' a'' t h1 h2]

lemma int_div_const (a : ℝ → ℝ) (c t₀ t : ℝ) :
    (∫ s in t..t₀, 1 / (a s / c)) = c * comoving a t₀ t := by
  unfold comoving
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext s; rw [one_div_div, div_eq_mul_one_div]

/-- No gap in `AngDistSpec`: for every curvature `K`, every scale factor positive and
continuous on `[t, t₀]`, and `t ≤ t₀`, any `D` meeting the spec equals `angDist`
(`flat`/`closed`/`open` fix `K ∈ {0, ±1}`, `rescale` transports them to every `K`). -/
theorem angDistSpec_pins (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : AngDistSpec D) (K : ℝ)
    (a : ℝ → ℝ) (t₀ t : ℝ) (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hcont : ContinuousOn a (Set.Icc t t₀)) : D K a t₀ t = angDist K a t₀ t := by
  obtain ⟨h0, h00⟩ := ms_ends htt hpos
  rw [ms_angDist_eq K a t₀ t h0 h00]
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · set c := Real.sqrt (-K) with hcdef
    have hc : 0 < c := Real.sqrt_pos.2 (by linarith)
    have e1 : c ^ 2 * (-1) = K := by rw [hcdef, Real.sq_sqrt (by linarith)]; ring
    have hab : (fun s => c * (a s / c)) = a := by funext s; field_simp
    have hb : ∀ s ∈ Set.Icc t t₀, 0 < a s / c := fun s hs => div_pos (hpos s hs) hc
    calc D K a t₀ t = D (c ^ 2 * (-1)) (fun s => c * (a s / c)) t₀ t := by rw [e1, hab]
      _ = D (-1) (fun s => a s / c) t₀ t := h.rescale c hc (-1) (fun s => a s / c) t₀ t
      _ = a t / c * Real.sinh (∫ s in t..t₀, 1 / (a s / c)) :=
          h.open (fun s => a s / c) t₀ t htt hb (hcont.div_const c)
      _ = a t * transverse K (comoving a t₀ t) := by
          rw [int_div_const]
          simp only [transverse, not_lt.2 hK.le, hK, ite_false, ite_true, ← hcdef]
          field_simp
  · rw [h.flat a t₀ t htt hpos hcont]; simp [transverse, comoving]
  · set c := Real.sqrt K with hcdef
    have hc : 0 < c := Real.sqrt_pos.2 hK
    have e1 : c ^ 2 * 1 = K := by rw [hcdef, Real.sq_sqrt hK.le]; ring
    have hab : (fun s => c * (a s / c)) = a := by funext s; field_simp
    have hb : ∀ s ∈ Set.Icc t t₀, 0 < a s / c := fun s hs => div_pos (hpos s hs) hc
    calc D K a t₀ t = D (c ^ 2 * 1) (fun s => c * (a s / c)) t₀ t := by rw [e1, hab]
      _ = D 1 (fun s => a s / c) t₀ t := h.rescale c hc 1 (fun s => a s / c) t₀ t
      _ = a t / c * Real.sin (∫ s in t..t₀, 1 / (a s / c)) :=
          h.closed (fun s => a s / c) t₀ t htt hb (hcont.div_const c)
      _ = a t * transverse K (comoving a t₀ t) := by
          rw [int_div_const]
          simp only [transverse, hK, ite_true, ← hcdef]
          field_simp


/-- `HubbleSpec` pins `hubble` for every positive scale factor differentiable at `t`
(its `logDeriv` law `H = d ln a/dt` and uniqueness of derivatives). -/
theorem hubbleSpec_pins (H : (ℝ → ℝ) → ℝ → ℝ) (h : HubbleSpec H) (a : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) : H a t = hubble a t := by
  have h1 := h.logDeriv a t ha hd
  have h2 := hd.hasDerivAt.log ha.ne'
  exact h1.unique h2


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

end Checked.Fidelity
