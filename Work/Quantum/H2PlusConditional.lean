import Work.Quantum.AngularAssembly
import Work.Quantum.H2Events
import Work.Quantum.H2PlusBlindClosed
import Mathlib.Analysis.Calculus.Deriv.Shift
/-!
# H₂⁺ at R = 2: the frozen statement from the certificate facts (run 2026-11-26T2228Z)

Route of `runs/2026-11-26T1628Z/README.md`, steps 1–3 assembled. `freeze_of_certificate` proves the frozen statement
`H2PlusBlindClosed.Freeze` (the H₂⁺ separated problem at R = 2 with total energy in
[−0.6026342144950, −0.6026342144949]) from exactly the facts route step 4 (the certificate) must supply, with
k = −2(E − 1/2) ∈ [k₁, k₂], k₁ = 2.2052684289898, k₂ = 2.2052684289900, and an angular bracket [a, b] ⊆ [0, 3]:
* `hM`: the angular series M_{k,A} (`AngularAssembly.M`, M(s = 0) = 1) is positive on s ∈ [0, 1] (η ∈ [0, 1]) for
  every (k, A) in the box;
* `hlo`, `hhi`: g(k, a) < 0 < g(k, b) for every k (g = dM/ds at s = 1, η = 0);
* `hunder`: at k₁, for every A ∈ [a, b], every radial solution regular through ξ = 1 with L(1) = 1 (L and
  (ξ² − 1)L′ differentiable on ξ > −1/4) becomes negative somewhere on [1, ∞) (`UnderAll`);
* `hover`: at k₂, for every A ∈ [a, b], every such solution is positive on [1, b′] with L′(b′) > 0 for some b′ ≥ 5/2
  (`OverAll`).
The rest is proved here: the even extension of the angular solution to η ∈ [−1, 1] (`angular_eta`), the angular
root A(k) continuous in k (`AngularAssembly.angular_root`), the global radial solution continuous in k
(`RadialGlobal.radial_global`), and the shooting argument (`H2Events.shoot`). The sign condition of the tail
(4ξ − kξ² + A ≤ −ξ²/10 for ξ ≥ 5/2) holds on the whole box (`neg_tail`).
-/

namespace Work.Quantum.H2PlusConditional
open Set Filter Topology MeasureTheory
open Work.Quantum.AngularAssembly (M Ms g Box angular_ode angular_root)

/-! ## The angular solution on η ∈ [−1, 1] -/

/-- M(η) = M_s(1 − |η|), the even extension. -/
noncomputable def Mη (k A η : ℝ) : ℝ := M k A (1 - |η|)
/-- dM/dη. -/
noncomputable def M'η (k A η : ℝ) : ℝ := if 0 ≤ η then -Ms k A (1 - η) else Ms k A (1 + η)

theorem angular_eta {k A : ℝ} (hb : Box k A) (hg : g k A = 0) :
    ContinuousOn (Mη k A) (Icc (-1) 1) ∧
    (∀ η ∈ Ioo (-1 : ℝ) 1, HasDerivAt (Mη k A) (M'η k A η) η) ∧
    (∀ η ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun x => (1 - x ^ 2) * M'η k A x) ((-k * η ^ 2 + A) * Mη k A η) η) := by
  have hg' : Ms k A 1 = 0 := hg
  have hin : ∀ s, 0 ≤ s → s ≤ 1 → s ∈ Ioo (-(5 / 4 : ℝ)) (5 / 4) := fun s h0 h1 => ⟨by linarith, by linarith⟩
  -- the s-derivatives composed with s = 1 − η and s = 1 + η
  have dR : ∀ η, 0 ≤ η → η ≤ 1 → HasDerivAt (fun y => M k A (1 - y)) (-Ms k A (1 - η)) η ∧
      HasDerivAt (fun y => -((0 + 2 * (1 - y) + (-1) * (1 - y) ^ 2) * Ms k A (1 - y)))
        ((-k * η ^ 2 + A) * M k A (1 - η)) η := by
    intro η h0 h1
    obtain ⟨a1, a2⟩ := angular_ode hb (hin (1 - η) (by linarith) (by linarith))
    refine ⟨HasDerivAt.comp_const_sub 1 η a1, ?_⟩
    have := (HasDerivAt.comp_const_sub 1 η a2).neg
    convert this using 1
    ring
  have dL : ∀ η, -1 ≤ η → η ≤ 0 → HasDerivAt (fun y => M k A (1 + y)) (Ms k A (1 + η)) η ∧
      HasDerivAt (fun y => (0 + 2 * (1 + y) + (-1) * (1 + y) ^ 2) * Ms k A (1 + y))
        ((-k * η ^ 2 + A) * M k A (1 + η)) η := by
    intro η h0 h1
    obtain ⟨a1, a2⟩ := angular_ode hb (hin (1 + η) (by linarith) (by linarith))
    refine ⟨HasDerivAt.comp_const_add 1 η a1, ?_⟩
    have := HasDerivAt.comp_const_add 1 η a2
    convert this using 1
    ring
  refine ⟨?_, fun η hη => ?_, fun η hη => ?_⟩
  · -- continuity
    intro η hη
    have hs : 1 - |η| ∈ Ioo (-(5 / 4 : ℝ)) (5 / 4) :=
      hin _ (by linarith [abs_le.mpr ⟨hη.1, hη.2⟩]) (by linarith [abs_nonneg η])
    have hM := (angular_ode hb hs).1.continuousAt
    have hc : ContinuousAt (fun y : ℝ => 1 - |y|) η := by fun_prop
    exact (ContinuousAt.comp (f := fun y : ℝ => 1 - |y|) hM hc).continuousWithinAt
  · -- dM/dη
    rcases lt_trichotomy η 0 with h | h | h
    · have hd := (dL η hη.1.le h.le).1
      refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards [Iio_mem_nhds h] with y hy
        simp only [Mη, abs_of_neg (show y < 0 from hy)]; ring_nf
      · simp only [M'η, if_neg (not_le.mpr h)]
    · subst h
      have hr : HasDerivWithinAt (Mη k A) (M'η k A 0) (Ici 0) 0 := by
        have hd := (dR 0 le_rfl zero_le_one).1.hasDerivWithinAt (s := Ici 0)
        refine (hd.congr (fun y hy => ?_) ?_).congr_deriv ?_
        · simp only [Mη, abs_of_nonneg (show 0 ≤ y from hy)]
        · simp [Mη]
        · simp [M'η]
      have hl : HasDerivWithinAt (Mη k A) (M'η k A 0) (Iic 0) 0 := by
        have hd := (dL 0 (by norm_num) le_rfl).1.hasDerivWithinAt (s := Iic 0)
        refine (hd.congr (fun y hy => ?_) ?_).congr_deriv ?_
        · simp only [Mη, abs_of_nonpos (show y ≤ 0 from hy)]; ring_nf
        · simp [Mη]
        · simp [M'η, hg']
      have := hl.union hr
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · have hd := (dR η h.le hη.2.le).1
      refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards [Ioi_mem_nhds h] with y hy
        simp only [Mη, abs_of_pos (show 0 < y from hy)]
      · simp only [M'η, if_pos h.le]
  · -- the flux form
    rcases lt_trichotomy η 0 with h | h | h
    · have hd := (dL η hη.1.le h.le).2
      refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards [Iio_mem_nhds h] with y hy
        simp only [M'η, if_neg (not_le.mpr (show y < 0 from hy))]; ring
      · simp only [Mη, abs_of_neg h]; ring_nf
    · subst h
      have hr : HasDerivWithinAt (fun x => (1 - x ^ 2) * M'η k A x) ((-k * 0 ^ 2 + A) * Mη k A 0) (Ici 0) 0 := by
        have hd := (dR 0 le_rfl zero_le_one).2.hasDerivWithinAt (s := Ici 0)
        refine (hd.congr (fun y hy => ?_) ?_).congr_deriv ?_
        · simp only [M'η, if_pos (show 0 ≤ y from hy)]; ring
        · simp [M'η]; ring
        · simp [Mη]
      have hl : HasDerivWithinAt (fun x => (1 - x ^ 2) * M'η k A x) ((-k * 0 ^ 2 + A) * Mη k A 0) (Iic 0) 0 := by
        have hd := (dL 0 (by norm_num) le_rfl).2.hasDerivWithinAt (s := Iic 0)
        refine (hd.congr (fun y hy => ?_) ?_).congr_deriv ?_
        · rcases (show y ≤ 0 from hy).lt_or_eq with h' | h'
          · simp only [M'η, if_neg (not_le.mpr h')]; ring
          · subst h'; simp [M'η, hg']
        · simp [M'η, hg']
        · simp [Mη]
      have := hl.union hr
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · have hd := (dR η h.le hη.2.le).2
      refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards [Ioi_mem_nhds h] with y hy
        simp only [M'η, if_pos (show 0 ≤ y from le_of_lt hy)]; ring
      · simp only [Mη, abs_of_pos h]

/-! ## The certificate facts and the assembly -/

/-- Every radial solution regular through ξ = 1 with L(1) = 1 becomes negative on [1, ∞). -/
def UnderAll (k A : ℝ) : Prop :=
  ∀ L L' : ℝ → ℝ, L 1 = 1 → (∀ x, -(1 / 4 : ℝ) < x → HasDerivAt L (L' x) x ∧
    HasDerivAt (fun y => (y ^ 2 - 1) * L' y) (-((4 * x - k * x ^ 2 + A) * L x)) x) →
  ∃ ξ, 1 ≤ ξ ∧ L ξ < 0

/-- Every radial solution regular through ξ = 1 with L(1) = 1 is positive on [1, b] with L′(b) > 0, some b ≥ 5/2. -/
def OverAll (k A : ℝ) : Prop :=
  ∀ L L' : ℝ → ℝ, L 1 = 1 → (∀ x, -(1 / 4 : ℝ) < x → HasDerivAt L (L' x) x ∧
    HasDerivAt (fun y => (y ^ 2 - 1) * L' y) (-((4 * x - k * x ^ 2 + A) * L x)) x) →
  ∃ b, 5 / 2 ≤ b ∧ (∀ ξ ∈ Icc 1 b, 0 < L ξ) ∧ 0 < L' b

/-- The bracket of k = 1 − 2E. -/
noncomputable def k₁ : ℝ := 22052684289898 / 10 ^ 13
noncomputable def k₂ : ℝ := 22052684289900 / 10 ^ 13

theorem neg_tail {k A x : ℝ} (hk : 11 / 5 ≤ k) (hA : A ≤ 3) (hx : 5 / 2 ≤ x) :
    4 * x - k * x ^ 2 + A ≤ -(1 / 10 * x ^ 2) := by
  nlinarith

/-- **The frozen H₂⁺ statement from the certificate facts** (route step 4 supplies the hypotheses). -/
theorem freeze_of_certificate {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 3)
    (hM : ∀ k ∈ Icc k₁ k₂, ∀ A ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, 0 < M k A s)
    (hlo : ∀ k ∈ Icc k₁ k₂, g k a < 0) (hhi : ∀ k ∈ Icc k₁ k₂, 0 < g k b)
    (hunder : ∀ A ∈ Icc a b, UnderAll k₁ A) (hover : ∀ A ∈ Icc a b, OverAll k₂ A) :
    H2PlusBlindClosed.Freeze := by
  have hk₁ : (0 : ℝ) ≤ k₁ := by unfold k₁; norm_num
  have hk₂ : k₂ ≤ (3 : ℝ) := by unfold k₂; norm_num
  have hk12 : k₁ ≤ k₂ := by unfold k₁ k₂; norm_num
  have hk11 : (11 / 5 : ℝ) ≤ k₁ := by unfold k₁; norm_num
  -- step 1: the angular root
  obtain ⟨R, hRc, hR⟩ := angular_root hk₁ hk₂ ha hab hb
    (fun k hk A hA s hs => hM k hk A hA s (Ioo_subset_Icc_self hs)) hlo hhi
  have hR3 : ∀ k ∈ Icc k₁ k₂, R k ∈ Icc (0 : ℝ) 3 := fun k hk =>
    ⟨ha.trans (hR k hk).1.1.le, ((hR k hk).1.2.le).trans hb⟩
  -- step 2: the global radial solution
  obtain ⟨L, L', hLd, hLc, hLj⟩ := Work.Quantum.RadialGlobal.radial_global hk₁ hk₂ hRc hR3
  -- step 3: shooting
  have S : H2Events.Setup k₁ k₂ (1 / 10) R L L' :=
    { le := hk12
      bnd := fun k hk => ⟨abs_le.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩,
        abs_le.mpr ⟨by linarith [(hR3 k hk).1], (hR3 k hk).2⟩⟩
      one := fun k hk => (hLd k hk).1
      dL := fun k hk x hx => ((hLd k hk).2 x hx).1
      dP := fun k hk x hx => ((hLd k hk).2 x hx).2
      cL := fun x hx => (hLc x hx).1
      cL' := fun x hx => (hLc x hx).2
      joint := hLj
      pos_κ := by norm_num
      neg := fun k hk x hx => neg_tail (hk11.trans hk.1) (hR3 k hk).2 hx }
  have hk₁I : k₁ ∈ Icc k₁ k₂ := ⟨le_rfl, hk12⟩
  have hk₂I : k₂ ∈ Icc k₁ k₂ := ⟨hk12, le_rfl⟩
  have hU : H2Events.Under L k₁ :=
    hunder (R k₁) (Ioo_subset_Icc_self (hR k₁ hk₁I).1) (L k₁) (L' k₁) (hLd k₁ hk₁I).1 (hLd k₁ hk₁I).2
  have hO : H2Events.Over L L' k₂ :=
    hover (R k₂) (Ioo_subset_Icc_self (hR k₂ hk₂I).1) (L k₂) (L' k₂) (hLd k₂ hk₂I).1 (hLd k₂ hk₂I).2
  obtain ⟨ks, hks, hpos, -, htend, hint⟩ := H2Events.shoot S hU hO
  -- the angular solution at (ks, R ks) on η ∈ [−1, 1]
  have hbox : Box ks (R ks) := ⟨abs_le.mpr ⟨by linarith [hks.1, hk11], by linarith [hks.2, hk₂]⟩,
    abs_le.mpr ⟨by linarith [hks.2, hk₂, (hR3 ks hks).1], by linarith [hks.1, hk11, (hR3 ks hks).2]⟩⟩
  obtain ⟨cM, dM, fM⟩ := angular_eta hbox (hR ks hks).2.1
  have hRab : R ks ∈ Icc a b := Ioo_subset_Icc_self (hR ks hks).1
  -- the energy
  refine ⟨(1 - ks) / 2, ⟨?_, ?_⟩, R ks, L ks, L' ks, Mη ks (R ks), M'η ks (R ks), ?_, ?_, ?_, ?_, htend, hint,
    cM, dM, ?_, ?_⟩
  · have := hks.2; unfold k₂ at this; norm_num at this ⊢; linarith
  · have := hks.1; unfold k₁ at this; norm_num at this ⊢; linarith
  · exact fun x hx => ((S.dL ks hks x (by linarith [mem_Ici.mp hx])).continuousAt).continuousWithinAt
  · exact fun x hx => S.dL ks hks x (by linarith [mem_Ioi.mp hx])
  · intro x hx
    have := S.dP ks hks x (by linarith [mem_Ioi.mp hx])
    convert this using 2
    ring
  · exact fun x hx => hpos x hx
  · intro η hη
    have := fM η hη
    convert this using 2
    ring
  · intro η hη
    simp only [Mη]
    exact hM ks hks (R ks) hRab _ ⟨by linarith [abs_le.mpr ⟨hη.1, hη.2⟩], by linarith [abs_nonneg η]⟩

end Work.Quantum.H2PlusConditional
