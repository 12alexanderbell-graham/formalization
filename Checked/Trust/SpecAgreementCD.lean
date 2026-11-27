import Checked.Cosmography.BambaZ
import Checked.Cosmography.FRCosmo
import Checked.Cosmography.CPLCoefficients
import Checked.Trust.SecondReadingSpecC
import Checked.Trust.SecondReadingSpecD

/-!
# Blind specification readings C and D against seven more pinned definitions (run 2026-11-27T0228Z)

Second batch of `Checked/Trust/SpecAgreement.lean` (same theorem names and shapes, same namespace):
`transverse`, `lumDist`, `angDist`, `IsFlatLCDM`, `IsFlatCPL`, `curvK`, `curv`. For a condition
(`IsFlatLCDM`, `IsFlatCPL`) the pin is an equivalence. Both readers had their web fetches of the sources
refused and wrote from memory.

Proved disagreements:
* `not_meets_IsFlatLCDM_C`, `not_meets_IsFlatCPL_C`: reader C does not require expansion at the
  observation time; the program's model sentence does (a contracting de Sitter universe meets reader C's
  condition, not the program's). Where the universe expands at the observation time the two agree
  (`pins_IsFlatLCDM_C`, `pins_IsFlatCPL_C`).
* `not_meets_IsFlatLCDM_D`, `not_meets_IsFlatCPL_D`: reader D requires the law and a positive scale factor
  at every time; the program's holds near the observation time (a model with a big bang meets the
  program's condition and not reader D's). No agreement theorem.
* `not_meets_curv_C`, `not_meets_curv_D`: both readers take the Ricci scalar with the opposite sign of the
  program, which follows the sign convention its source states in its F(R) section; their specifications
  determine minus the program's definition (`pins_neg_curv_C`, `pins_neg_curv_D`). Neither reader could
  open that source.
-/

namespace Checked.Trust.SpecAgreement

open Filter Topology Real Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.BambaY
open Checked.Cosmography.BambaK Checked.Cosmography.BambaA Checked.Cosmography.BambaZ
open Checked.Cosmography.Transverse Checked.Cosmography.CPL Checked.Cosmography.FRCosmo
open Checked.Cosmography.AvilesWitness
open Checked.Trust.SecondReadingSpecC Checked.Trust.SecondReadingSpecD

/-! ## Transverse distance function -/

lemma transverse_pos {K : ℝ} (hK : 0 < K) (χ : ℝ) :
    transverse K χ = Real.sin (Real.sqrt K * χ) / Real.sqrt K := by
  simp only [transverse, if_pos hK]

lemma transverse_neg {K : ℝ} (hK : K < 0) (χ : ℝ) :
    transverse K χ = Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K) := by
  simp only [transverse, if_neg (not_lt.2 hK.le), if_pos hK]

lemma transverse_zero (χ : ℝ) : transverse 0 χ = χ := by simp [transverse]

theorem meets_transverse_C : TransverseSpecC transverse where
  closed _ _ hK _ := transverse_pos hK _
  flat _ _ := transverse_zero _
  open_ _ _ hK _ := transverse_neg hK _

theorem pins_transverse_C (S : ℝ → ℝ → ℝ) (h : TransverseSpecC S) (K χ : ℝ) (hχ : 0 ≤ χ) :
    S K χ = transverse K χ := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [h.open_ K χ hK hχ, transverse_neg hK]
  · rw [h.flat χ hχ, transverse_zero]
  · rw [h.closed K χ hK hχ, transverse_pos hK]

theorem meets_transverse_D : TransverseSpecD transverse where
  closed _ _ hK := transverse_pos hK _
  flat _ := transverse_zero _
  open_ _ _ hK := transverse_neg hK _

theorem pins_transverse_D (S : ℝ → ℝ → ℝ) (h : TransverseSpecD S) (K χ : ℝ) :
    S K χ = transverse K χ := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [h.open_ K χ hK, transverse_neg hK]
  · rw [h.flat χ, transverse_zero]
  · rw [h.closed K χ hK, transverse_pos hK]

/-! ## Luminosity and angular diameter distance -/

lemma lumDist_eq' (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) :
    lumDist K a t₀ t = a t₀ * (a t₀ / a t) * transverse K (∫ s in t..t₀, 1 / a s) := by
  unfold lumDist redshift comoving; ring

lemma angDist_eq' (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) (h1 : a t ≠ 0) (h0 : a t₀ ≠ 0) :
    angDist K a t₀ t = a t * transverse K (∫ s in t..t₀, 1 / a s) := by
  unfold angDist
  rw [lumDist_eq']
  unfold redshift
  rw [show 1 + (a t₀ / a t - 1) = a t₀ / a t by ring]
  field_simp

lemma ends_pos {a : ℝ → ℝ} {t₀ t : ℝ} (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) :
    a t ≠ 0 ∧ a t₀ ≠ 0 :=
  ⟨(hpos t ⟨le_refl t, htt⟩).ne', (hpos t₀ ⟨htt, le_refl t₀⟩).ne'⟩

theorem meets_lumDist_C : LumDistSpecC lumDist where
  closed K a t₀ t hK _ _ _ := by rw [lumDist_eq', transverse_pos hK]
  flat a t₀ t _ _ _ := by rw [lumDist_eq', transverse_zero]
  open_ K a t₀ t hK _ _ _ := by rw [lumDist_eq', transverse_neg hK]

theorem pins_lumDist_C (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpecC D) (K : ℝ) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hc : ContinuousOn a (Set.Icc t t₀))
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) : D K a t₀ t = lumDist K a t₀ t := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [h.open_ K a t₀ t hK htt hc hpos, meets_lumDist_C.open_ K a t₀ t hK htt hc hpos]
  · rw [h.flat a t₀ t htt hc hpos, meets_lumDist_C.flat a t₀ t htt hc hpos]
  · rw [h.closed K a t₀ t hK htt hc hpos, meets_lumDist_C.closed K a t₀ t hK htt hc hpos]

theorem meets_lumDist_D : LumDistSpecD lumDist where
  closed K a t₀ t hK _ _ _ := by rw [lumDist_eq', transverse_pos hK]; ring
  flat a t₀ t _ _ _ := by rw [lumDist_eq', transverse_zero]; ring
  open_ K a t₀ t hK _ _ _ := by rw [lumDist_eq', transverse_neg hK]; ring

theorem pins_lumDist_D (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistSpecD D) (K : ℝ) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hc : ContinuousOn a (Set.Icc t t₀))
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) : D K a t₀ t = lumDist K a t₀ t := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [h.open_ K a t₀ t hK htt hc hpos, meets_lumDist_D.open_ K a t₀ t hK htt hc hpos]
  · rw [h.flat a t₀ t htt hc hpos, meets_lumDist_D.flat a t₀ t htt hc hpos]
  · rw [h.closed K a t₀ t hK htt hc hpos, meets_lumDist_D.closed K a t₀ t hK htt hc hpos]

theorem meets_angDist_C : AngDistSpecC angDist where
  closed K a t₀ t hK htt _ hp := by
    obtain ⟨h1, h0⟩ := ends_pos htt hp; rw [angDist_eq' K a t₀ t h1 h0, transverse_pos hK]
  flat a t₀ t htt _ hp := by
    obtain ⟨h1, h0⟩ := ends_pos htt hp; rw [angDist_eq' 0 a t₀ t h1 h0, transverse_zero]
  open_ K a t₀ t hK htt _ hp := by
    obtain ⟨h1, h0⟩ := ends_pos htt hp; rw [angDist_eq' K a t₀ t h1 h0, transverse_neg hK]

theorem pins_angDist_C (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : AngDistSpecC D) (K : ℝ) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hc : ContinuousOn a (Set.Icc t t₀))
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) : D K a t₀ t = angDist K a t₀ t := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [h.open_ K a t₀ t hK htt hc hpos, meets_angDist_C.open_ K a t₀ t hK htt hc hpos]
  · rw [h.flat a t₀ t htt hc hpos, meets_angDist_C.flat a t₀ t htt hc hpos]
  · rw [h.closed K a t₀ t hK htt hc hpos, meets_angDist_C.closed K a t₀ t hK htt hc hpos]

theorem meets_angDist_D : AngDistSpecD angDist where
  closed K a t₀ t hK htt _ hp := by
    obtain ⟨h1, h0⟩ := ends_pos htt hp; rw [angDist_eq' K a t₀ t h1 h0, transverse_pos hK]
  flat a t₀ t htt _ hp := by
    obtain ⟨h1, h0⟩ := ends_pos htt hp; rw [angDist_eq' 0 a t₀ t h1 h0, transverse_zero]
  open_ K a t₀ t hK htt _ hp := by
    obtain ⟨h1, h0⟩ := ends_pos htt hp; rw [angDist_eq' K a t₀ t h1 h0, transverse_neg hK]

theorem pins_angDist_D (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : AngDistSpecD D) (K : ℝ) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hc : ContinuousOn a (Set.Icc t t₀))
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) : D K a t₀ t = angDist K a t₀ t := by
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · rw [h.open_ K a t₀ t hK htt hc hpos, meets_angDist_D.open_ K a t₀ t hK htt hc hpos]
  · rw [h.flat a t₀ t htt hc hpos, meets_angDist_D.flat a t₀ t htt hc hpos]
  · rw [h.closed K a t₀ t hK htt hc hpos, meets_angDist_D.closed K a t₀ t hK htt hc hpos]

/-! ## Curvature parameter -/

theorem meets_curvK_C : CurvParamSpecC curvK :=
  ⟨fun K a t₀ a1 hd _ _ => by unfold curvK hubble; rw [hd.deriv]; ring⟩

theorem pins_curvK_C (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : CurvParamSpecC k) (K : ℝ) (a : ℝ → ℝ) (t₀ a1 : ℝ)
    (hd : HasDerivAt a a1 t₀) (ha : a t₀ ≠ 0) (h1 : a1 ≠ 0) : k K a t₀ = curvK K a t₀ := by
  rw [h.formula K a t₀ a1 hd ha h1, meets_curvK_C.formula K a t₀ a1 hd ha h1]

theorem meets_curvK_D : CurvParamSpecD curvK :=
  ⟨fun K a t₀ _ _ _ => by unfold curvK hubble hubbleD; ring⟩

theorem pins_curvK_D (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : CurvParamSpecD k) (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : a t₀ ≠ 0) (hd : DifferentiableAt ℝ a t₀) (hH : hubbleD a t₀ ≠ 0) :
    k K a t₀ = curvK K a t₀ := by
  rw [h.formula K a t₀ ha hd hH, meets_curvK_D.formula K a t₀ ha hd hH]

/-! ## Ricci scalar: the readers' sign is the opposite of the program's -/

lemma hubble_exp : hubble Real.exp = fun _ => 1 := by
  funext s; simp [hubble, Real.deriv_exp, (Real.exp_pos s).ne']

lemma curv_exp (t : ℝ) : curv Real.exp t = -12 := by
  unfold curv; rw [hubble_exp]; simp; norm_num

theorem not_meets_curv_C : ¬ RicciFlatSpecC curv := by
  intro h
  have e := h.formula Real.exp 0 (Real.exp 0) (Real.exp 0) (Real.hasDerivAt_exp 0)
    (by rw [Real.deriv_exp]; exact Real.hasDerivAt_exp 0) (Real.exp_pos 0).ne'
  rw [curv_exp] at e
  norm_num at e

theorem not_meets_curv_D : ¬ RicciFlatSpecD curv := by
  intro h
  have e := h.scale_form Real.exp 0 (Real.exp_pos 0).ne'
    (Eventually.of_forall fun s => Real.differentiableAt_exp)
    (by rw [Real.deriv_exp]; exact Real.differentiableAt_exp)
  rw [curv_exp, Real.deriv_exp, Real.deriv_exp] at e
  norm_num at e

/-- Reader C's specification determines minus the program's Ricci scalar. -/
theorem pins_neg_curv_C (R : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatSpecC R) (a : ℝ → ℝ) (t a1 a2 : ℝ)
    (h1 : HasDerivAt a a1 t) (h2 : HasDerivAt (deriv a) a2 t) (ha : a t ≠ 0) :
    R a t = -curv a t := by
  rw [h.formula a t a1 a2 h1 h2 ha]
  have hq : HasDerivAt (fun s => deriv a s / a s)
      ((a2 * a t - deriv a t * a1) / a t ^ 2) t := h2.div h1 ha
  have hh : hubble a = fun s => deriv a s / a s := rfl
  unfold curv
  rw [hh, hq.deriv]
  simp only [h1.deriv]
  field_simp
  ring

/-- Reader D's specification determines minus the program's Ricci scalar. -/
theorem pins_neg_curv_D (R : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatSpecD R) (a : ℝ → ℝ) (t : ℝ)
    (ha : a t ≠ 0) (h1 : ∀ᶠ s in nhds t, DifferentiableAt ℝ a s)
    (h2 : DifferentiableAt ℝ (deriv a) t) : R a t = -curv a t := by
  rw [h.hubble_form a t ha h1 h2]
  have hh : hubble a = hubbleD a := rfl
  unfold curv; rw [hh]; ring

/-! ## Flat ΛCDM and flat CPL model conditions -/

lemma hasDerivAt_expNeg (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by
  have := (hasDerivAt_neg t).exp
  convert this using 1; ring

lemma hubble_expNeg (t : ℝ) : deriv (fun s => Real.exp (-s)) t / Real.exp (-t) = -1 := by
  rw [(hasDerivAt_expNeg t).deriv]; field_simp

/-- **Disagreement (proved):** the contracting de Sitter universe `a = e^{−t}` with `Ω = 0` meets reader
C's flat ΛCDM condition at `t₀ = 0`, not the program's (which requires expansion at `t₀`). -/
theorem not_meets_IsFlatLCDM_C : ¬ FlatLCDMSpecC IsFlatLCDM := by
  intro h
  have hc := (h.iff_expansion 0 (fun s => Real.exp (-s)) 0).2 ⟨Real.exp_pos _,
    Eventually.of_forall fun t => ⟨Real.exp_pos _, (hasDerivAt_expNeg t).differentiableAt, by
      rw [hubble_expNeg, hubble_expNeg]; simp⟩⟩
  have := hc.1
  unfold hubble at this
  rw [hubble_expNeg] at this
  norm_num at this

theorem pins_IsFlatLCDM_C (P : ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatLCDMSpecC P) (Ω : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) (hH : 0 < deriv a t₀ / a t₀) : P Ω a t₀ ↔ IsFlatLCDM Ω a t₀ := by
  rw [h.iff_expansion]
  unfold IsFlatLCDM hubble redshift
  have e : ∀ t, Ω * (1 + (a t₀ / a t - 1)) ^ 3 + 1 - Ω = Ω * (a t₀ / a t) ^ 3 + (1 - Ω) :=
    fun t => by ring
  constructor
  · rintro ⟨_, ev⟩
    exact ⟨hH, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by rw [e]; exact q⟩⟩
  · rintro ⟨_, ev⟩
    exact ⟨ev.self_of_nhds.1, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by rw [← e]; exact q⟩⟩

theorem not_meets_IsFlatCPL_C : ¬ FlatCPLSpecC IsFlatCPL := by
  intro h
  have hc := (h.iff_expansion 0 (-1) 0 (fun s => Real.exp (-s)) 0).2 ⟨Real.exp_pos _,
    Eventually.of_forall fun t => ⟨Real.exp_pos _, (hasDerivAt_expNeg t).differentiableAt, by
      rw [hubble_expNeg, hubble_expNeg]; norm_num⟩⟩
  have := hc.1
  unfold hubble at this
  rw [hubble_expNeg] at this
  norm_num at this

theorem pins_IsFlatCPL_C (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatCPLSpecC P) (Ω w₀ wₐ : ℝ)
    (a : ℝ → ℝ) (t₀ : ℝ) (hH : 0 < deriv a t₀ / a t₀) :
    P Ω w₀ wₐ a t₀ ↔ IsFlatCPL Ω w₀ wₐ a t₀ := by
  rw [h.iff_expansion]
  unfold IsFlatCPL hubble redshift
  have e : ∀ t, a t ≠ 0 → a t₀ ≠ 0 →
      Ω * (1 + (a t₀ / a t - 1)) ^ 3 + (1 - Ω) * (1 + (a t₀ / a t - 1)) ^ (3 * (1 + w₀ + wₐ)) *
        Real.exp (-(3 * wₐ * (a t₀ / a t - 1)) / (1 + (a t₀ / a t - 1))) =
      Ω * (a t₀ / a t) ^ 3 + (1 - Ω) * (a t₀ / a t) ^ (3 * (1 + w₀ + wₐ)) *
        Real.exp (-3 * wₐ * (1 - a t / a t₀)) := by
    intro t h1 h0
    rw [show 1 + (a t₀ / a t - 1) = a t₀ / a t by ring]
    congr 3
    field_simp
  constructor
  · rintro ⟨h0, ev⟩
    exact ⟨hH, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by rw [e t p.ne' h0.ne']; exact q⟩⟩
  · rintro ⟨_, ev⟩
    have h0 := ev.self_of_nhds.1
    exact ⟨h0, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by rw [← e t p.ne' h0.ne']; exact q⟩⟩

lemma lam_zero : lam 0 = 0 := by
  simp [lam, Real.zero_rpow (show (2 / 3 : ℝ) ≠ 0 by norm_num)]

/-- **Disagreement (proved):** the matter + Λ model `lam = sinh^{2/3}` (a big bang at `t = 0`) meets the
program's flat ΛCDM condition at `t₀ = 1`, not reader D's (which requires a positive scale factor and the law
at every time). -/
theorem not_meets_IsFlatLCDM_D : ¬ FlatLCDMSpecD IsFlatLCDM := by
  intro h
  have hd := (h.iff_ (1 / Real.cosh 1 ^ 2) lam 1).1 (lam_isFlatLCDM one_pos)
  have := (hd.1 0).1
  rw [lam_zero] at this
  exact lt_irrefl 0 this

lemma lam_isFlatCPL : IsFlatCPL (1 / Real.cosh 1 ^ 2) (-1) 0 lam 1 := by
  obtain ⟨h1, h2⟩ := lam_isFlatLCDM one_pos
  refine ⟨h1, h2.mono fun t ⟨p, d, q⟩ => ⟨p, d, ?_⟩⟩
  rw [q]
  congr 2
  norm_num
  ring

theorem not_meets_IsFlatCPL_D : ¬ FlatCPLSpecD IsFlatCPL := by
  intro h
  have hd := (h.iff_ (1 / Real.cosh 1 ^ 2) (-1) 0 lam 1).1 lam_isFlatCPL
  have := (hd.1 0).1
  rw [lam_zero] at this
  exact lt_irrefl 0 this

end Checked.Trust.SpecAgreement
