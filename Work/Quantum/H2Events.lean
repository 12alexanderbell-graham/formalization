import Work.Quantum.H2Tail
import Work.Quantum.RadialGlobal
import Mathlib.Topology.UniformSpace.HeineCantor
/-!
# H₂⁺ route step 3: the shooting events and the bound state at the supremum (run 2026-11-26T2228Z)

Route of `runs/2026-11-26T1628Z/README.md`, step 3, generic (no numerics). `Setup` collects what route steps 1–2
give (`AngularAssembly.angular_root`, `RadialGlobal.radial_global`): for k in [k₁, k₂] a radial solution L(k, ·) with
L(k, 1) = 1 solving ((ξ² − 1)L′)′ = −(4ξ − kξ² + A(k))L on ξ > −1/4, continuous in k at each ξ and jointly on
[k₁, k₂] × [1, B], and the sign condition 4ξ − kξ² + A(k) ≤ −κξ² for ξ ≥ 5/2 (κ > 0).

Events: `Under k` — L(k, ξ) < 0 at some ξ ≥ 1; `Over k` — L(k, ·) > 0 on [1, b] and L′(k, b) > 0 at some b ≥ 5/2.
* `over_pos`: Over k ⇒ L(k, ξ) > 0 for every ξ ≥ 1 (`H2Tail.stays_above`), so the events are disjoint;
* `under_open`, `over_open`: both are open in k relative to [k₁, k₂] (pointwise continuity; uniform continuity on
  the compact [k₁, k₂] × [1, b] for the positivity on [1, b]);
* `no_double_zero`: L(k, ·) ≥ 0 on [1, ∞) ⇒ L(k, ·) > 0 there (a zero would be a double zero, and backward
  uniqueness for the linear system on [c, ξ₀], c > 1, with continuity at 1, contradicts L(k, 1) = 1);
* `shoot`: Under k₁ and Over k₂ ⇒ at k* = sup {k ∈ [k₁, k₂] : Under k} neither event holds, so L(k*, ·) > 0 on
  [1, ∞), L′(k*, ·) ≤ 0 on [5/2, ∞), and by `H2Tail.tail_of_nonincreasing` L(k*, ξ) → 0 and
  ∫₁^∞ L² ξ² < ∞ — the bound-state conditions of the freeze.
The two certificate facts (Under k₁, Over k₂) are route step 4.
-/

namespace Work.Quantum.H2Events
open Set Filter Topology MeasureTheory
open Work.Quantum.RadialGlobal (vf)

/-- What route steps 1–2 provide on [k₁, k₂]. -/
structure Setup (k₁ k₂ κ : ℝ) (A : ℝ → ℝ) (L L' : ℝ → ℝ → ℝ) : Prop where
  le : k₁ ≤ k₂
  bnd : ∀ k ∈ Icc k₁ k₂, |k| ≤ 3 ∧ |A k| ≤ 3
  one : ∀ k ∈ Icc k₁ k₂, L k 1 = 1
  dL : ∀ k ∈ Icc k₁ k₂, ∀ x, -(1 / 4 : ℝ) < x → HasDerivAt (L k) (L' k x) x
  dP : ∀ k ∈ Icc k₁ k₂, ∀ x, -(1 / 4 : ℝ) < x →
    HasDerivAt (fun y => (y ^ 2 - 1) * L' k y) (-((4 * x - k * x ^ 2 + A k) * L k x)) x
  cL : ∀ x, -(1 / 4 : ℝ) < x → ContinuousOn (fun k => L k x) (Icc k₁ k₂)
  cL' : ∀ x, -(1 / 4 : ℝ) < x → ContinuousOn (fun k => L' k x) (Icc k₁ k₂)
  joint : ∀ B, 2 ≤ B → ContinuousOn (fun z : ℝ × ℝ => L z.1 z.2) (Icc k₁ k₂ ×ˢ Icc 1 B)
  pos_κ : 0 < κ
  neg : ∀ k ∈ Icc k₁ k₂, ∀ x, 5 / 2 ≤ x → 4 * x - k * x ^ 2 + A k ≤ -(κ * x ^ 2)

def Under (L : ℝ → ℝ → ℝ) (k : ℝ) : Prop := ∃ ξ, 1 ≤ ξ ∧ L k ξ < 0

def Over (L L' : ℝ → ℝ → ℝ) (k : ℝ) : Prop := ∃ b, 5 / 2 ≤ b ∧ (∀ ξ ∈ Icc 1 b, 0 < L k ξ) ∧ 0 < L' k b

variable {k₁ k₂ κ : ℝ} {A : ℝ → ℝ} {L L' : ℝ → ℝ → ℝ}

theorem over_pos (S : Setup k₁ k₂ κ A L L') {k : ℝ} (hk : k ∈ Icc k₁ k₂) (ho : Over L L' k) :
    ∀ ξ, 1 ≤ ξ → 0 < L k ξ := by
  obtain ⟨b, hb, hpos, hd⟩ := ho
  intro ξ hξ
  by_cases hξb : ξ ≤ b
  · exact hpos ξ ⟨hξ, hξb⟩
  · push Not at hξb
    have hLb := hpos b ⟨by linarith, le_rfl⟩
    have := H2Tail.stays_above (L := L k) (L' := L' k) (N := fun x => 4 * x - k * x ^ 2 + A k)
      (a := 5 / 2) (by norm_num) (fun x hx => S.dL k hk x (by linarith [mem_Ici.mp hx]))
      (fun x hx => S.dP k hk x (by linarith [mem_Ici.mp hx]))
      (fun x hx => by
        have := S.neg k hk x hx
        nlinarith [S.pos_κ, sq_nonneg x]) hb hLb hd ξ (mem_Ici.mpr hξb.le)
    linarith

theorem under_not_over (S : Setup k₁ k₂ κ A L L') {k : ℝ} (hk : k ∈ Icc k₁ k₂) (ho : Over L L' k) :
    ¬ Under L k := by
  rintro ⟨ξ, hξ, hneg⟩
  linarith [over_pos S hk ho ξ hξ]

theorem under_open (S : Setup k₁ k₂ κ A L L') {k : ℝ} (hk : k ∈ Icc k₁ k₂) (hu : Under L k) :
    ∃ δ > 0, ∀ k' ∈ Icc k₁ k₂, |k' - k| < δ → Under L k' := by
  obtain ⟨ξ, hξ, hneg⟩ := hu
  have hc := S.cL ξ (by linarith) k hk
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc (-L k ξ) (by linarith)
  refine ⟨δ, hδ, fun k' hk' hd => ⟨ξ, hξ, ?_⟩⟩
  have := h hk' (by rwa [Real.dist_eq])
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.2]

theorem over_open (S : Setup k₁ k₂ κ A L L') {k : ℝ} (hk : k ∈ Icc k₁ k₂) (ho : Over L L' k) :
    ∃ δ > 0, ∀ k' ∈ Icc k₁ k₂, |k' - k| < δ → Over L L' k' := by
  obtain ⟨b, hb, hpos, hd⟩ := ho
  -- the minimum of L(k, ·) on [1, b]
  have hcont : ContinuousOn (L k) (Icc 1 b) := fun x hx =>
    (S.dL k hk x (by linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨ξm, hξm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by linarith)) hcont
  set m := L k ξm with hm
  have hm0 : 0 < m := hpos ξm hξm
  -- uniform continuity on [k₁, k₂] × [1, max b 2]
  set B := max b 2
  have hB : 2 ≤ B := le_max_right _ _
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous (S.joint B hB)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₁, hδ₁, h₁⟩ := huc m hm0
  -- the derivative at b
  have hc' := S.cL' b (by linarith) k hk
  rw [Metric.continuousWithinAt_iff] at hc'
  obtain ⟨δ₂, hδ₂, h₂⟩ := hc' (L' k b) hd
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun k' hk' hkk => ⟨b, hb, fun ξ hξ => ?_, ?_⟩⟩
  · have hξB : ξ ∈ Icc (1 : ℝ) B := ⟨hξ.1, hξ.2.trans (le_max_left _ _)⟩
    have hdist : dist (k', ξ) (k, ξ) < δ₁ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      exact lt_of_lt_of_le hkk (min_le_left _ _)
    have e1 := h₁ (k', ξ) ⟨hk', hξB⟩ (k, ξ) ⟨hk, hξB⟩ hdist
    rw [Real.dist_eq, abs_lt] at e1
    simp only at e1
    have e2 : L k ξm ≤ L k ξ := hmin hξ
    linarith [e1.1]
  · have := h₂ hk' (by rw [Real.dist_eq]; exact lt_of_lt_of_le hkk (min_le_right _ _))
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]

/-- The linear system is Lipschitz for t ∈ [c, T], 1 < c. -/
theorem lip_sys {k a c T t : ℝ} (hk : |k| ≤ 3) (ha : |a| ≤ 3) (hc : 1 < c) (ht : t ∈ Icc c T) :
    LipschitzWith (Real.toNNReal (1 / (c ^ 2 - 1) + (4 * T + 3 * T ^ 2 + 3))) (vf k a t) := by
  have hc2 : 0 < c ^ 2 - 1 := by nlinarith
  have ht2 : c ^ 2 - 1 ≤ t ^ 2 - 1 := by nlinarith [ht.1]
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hT : 0 ≤ T := ht0.trans ht.2
  have hK0 : 0 ≤ 1 / (c ^ 2 - 1) := by positivity
  have hN0 : 0 ≤ 4 * T + 3 * T ^ 2 + 3 := by positivity
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [vf, Prod.dist_eq, Real.dist_eq]
  have d1 : |x.1 - y.1| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_left _ _
  have d2 : |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
  have hd0 : 0 ≤ max |x.1 - y.1| |x.2 - y.2| := (abs_nonneg _).trans d1
  refine max_le ?_ ?_
  · rw [← _root_.sub_div, abs_div, abs_of_pos (show (0 : ℝ) < t ^ 2 - 1 by linarith)]
    calc |x.2 - y.2| / (t ^ 2 - 1) ≤ |x.2 - y.2| / (c ^ 2 - 1) :=
          div_le_div_of_nonneg_left (abs_nonneg _) hc2 ht2
      _ = 1 / (c ^ 2 - 1) * |x.2 - y.2| := by ring
      _ ≤ 1 / (c ^ 2 - 1) * max |x.1 - y.1| |x.2 - y.2| := by gcongr
      _ ≤ _ := by nlinarith
  · have e : -((4 * t - k * t ^ 2 + a) * x.1) - -((4 * t - k * t ^ 2 + a) * y.1)
        = -((4 * t - k * t ^ 2 + a) * (x.1 - y.1)) := by ring
    rw [e, abs_neg, abs_mul]
    have hN : |4 * t - k * t ^ 2 + a| ≤ 4 * T + 3 * T ^ 2 + 3 := by
      have h1 : |k * t ^ 2| ≤ 3 * T ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ t ^ 2)]
        have : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht0 ht.2 2
        nlinarith [abs_nonneg k]
      have h2 : |4 * t| ≤ 4 * T := by rw [abs_of_nonneg (by positivity)]; linarith [ht.2]
      calc |4 * t - k * t ^ 2 + a| ≤ |4 * t - k * t ^ 2| + |a| := abs_add_le _ _
        _ ≤ |4 * t| + |k * t ^ 2| + |a| := by gcongr; exact abs_sub _ _
        _ ≤ _ := by linarith
    calc |4 * t - k * t ^ 2 + a| * |x.1 - y.1| ≤ (4 * T + 3 * T ^ 2 + 3) * max |x.1 - y.1| |x.2 - y.2| :=
          mul_le_mul hN d1 (abs_nonneg _) hN0
      _ ≤ _ := by nlinarith

theorem no_double_zero (S : Setup k₁ k₂ κ A L L') {k : ℝ} (hk : k ∈ Icc k₁ k₂)
    (hnn : ∀ ξ, 1 ≤ ξ → 0 ≤ L k ξ) : ∀ ξ, 1 ≤ ξ → 0 < L k ξ := by
  intro ξ₀ hξ₀
  by_contra hcon
  push Not at hcon
  have hz : L k ξ₀ = 0 := le_antisymm hcon (hnn ξ₀ hξ₀)
  have h1 : 1 < ξ₀ := by
    rcases hξ₀.lt_or_eq with h | h
    · exact h
    · rw [← h, S.one k hk] at hz; norm_num at hz
  -- a local minimum: L′ = 0 at ξ₀
  have hmin : IsLocalMin (L k) ξ₀ := by
    filter_upwards [Ioi_mem_nhds h1] with y hy
    rw [hz]; exact hnn y (le_of_lt hy)
  have hd0 : L' k ξ₀ = 0 := hmin.hasDerivAt_eq_zero (S.dL k hk ξ₀ (by linarith))
  obtain ⟨hk3, hA3⟩ := S.bnd k hk
  -- backward uniqueness on [c, ξ₀] for every 1 < c < ξ₀
  set f : ℝ → ℝ × ℝ := fun t => (L k t, (t ^ 2 - 1) * L' k t) with hf
  have hfd : ∀ t, 1 < t → HasDerivAt f (vf k (A k) t (f t)) t := by
    intro t ht
    have hne : t ^ 2 - 1 ≠ 0 := by nlinarith
    have := (S.dL k hk t (by linarith)).prodMk (S.dP k hk t (by linarith))
    refine this.congr_deriv ?_
    simp only [vf, hf]
    congr 1
    field_simp
  have hzero : ∀ c, 1 < c → c ≤ ξ₀ → L k c = 0 := by
    intro c hc hcξ
    have heq := ODE_solution_unique_of_mem_Icc_left (v := vf k (A k)) (s := fun _ => univ)
      (K := Real.toNNReal (1 / (c ^ 2 - 1) + (4 * ξ₀ + 3 * ξ₀ ^ 2 + 3))) (f := f) (g := fun _ => (0, 0))
      (a := c) (b := ξ₀)
      (fun t ht => (lip_sys hk3 hA3 hc (Ioc_subset_Icc_self ht)).lipschitzOnWith)
      (fun t ht => (hfd t (by linarith [ht.1])).continuousAt.continuousWithinAt)
      (fun t ht => (hfd t (by linarith [ht.1])).hasDerivWithinAt) (fun _ _ => mem_univ _)
      continuousOn_const (fun t _ => by
        have : vf k (A k) t ((fun _ : ℝ => ((0 : ℝ), (0 : ℝ))) t) = (0, 0) := by simp [vf]
        rw [this]
        exact (hasDerivAt_const t ((0 : ℝ), (0 : ℝ))).hasDerivWithinAt.congr_deriv Prod.mk_zero_zero.symm)
      (fun _ _ => mem_univ _) (by simp [hf, hz, hd0])
    have := heq ⟨le_rfl, hcξ⟩
    simp only [hf, Prod.mk.injEq] at this
    exact this.1
  -- continuity at 1 forces L(k, 1) = 0
  have hcont : ContinuousAt (L k) 1 := (S.dL k hk 1 (by norm_num)).continuousAt
  have ht1 : Tendsto (L k) (𝓝[>] 1) (𝓝 (L k 1)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht0 : Tendsto (L k) (𝓝[>] 1) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT h1] with c hc
    exact (hzero c hc.1 hc.2.le).symm
  have := tendsto_nhds_unique ht1 ht0
  rw [S.one k hk] at this
  norm_num at this

/-- **Route step 3.** Under at k₁ and Over at k₂ give a k ∈ [k₁, k₂] whose radial solution is a bound state. -/
theorem shoot (S : Setup k₁ k₂ κ A L L') (hu : Under L k₁) (ho : Over L L' k₂) :
    ∃ k ∈ Icc k₁ k₂, (∀ ξ, 1 ≤ ξ → 0 < L k ξ) ∧ (∀ ξ, 5 / 2 ≤ ξ → L' k ξ ≤ 0) ∧
      Tendsto (L k) atTop (𝓝 0) ∧ IntegrableOn (fun x => L k x ^ 2 * x ^ 2) (Ici 1) := by
  have hk₁ : k₁ ∈ Icc k₁ k₂ := ⟨le_rfl, S.le⟩
  have hk₂ : k₂ ∈ Icc k₁ k₂ := ⟨S.le, le_rfl⟩
  set U := {k | k ∈ Icc k₁ k₂ ∧ Under L k} with hU
  have hne : U.Nonempty := ⟨k₁, hk₁, hu⟩
  have hbdd : BddAbove U := ⟨k₂, fun k hk => hk.1.2⟩
  set ks := sSup U with hks
  have hks1 : k₁ ≤ ks := le_csSup hbdd ⟨hk₁, hu⟩
  have hks2 : ks ≤ k₂ := csSup_le hne (fun k hk => hk.1.2)
  have hksI : ks ∈ Icc k₁ k₂ := ⟨hks1, hks2⟩
  -- not Under at the supremum
  have hnu : ¬ Under L ks := by
    intro h
    have hlt : ks < k₂ := by
      rcases hks2.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (h' ▸ h) (under_not_over S hk₂ ho)
    obtain ⟨δ, hδ, hδu⟩ := under_open S hksI h
    set k' := min (ks + δ / 2) k₂
    have hk'I : k' ∈ Icc k₁ k₂ := ⟨by
      have : k₁ ≤ ks + δ / 2 := by linarith
      exact le_min this S.le, min_le_right _ _⟩
    have hk'gt : ks < k' := lt_min (by linarith) hlt
    have hk'd : |k' - ks| < δ := by
      rw [abs_of_pos (by linarith)]
      have : k' ≤ ks + δ / 2 := min_le_left _ _
      linarith
    have := le_csSup hbdd ⟨hk'I, hδu k' hk'I hk'd⟩
    linarith
  -- not Over at the supremum
  have hno : ¬ Over L L' ks := by
    intro h
    obtain ⟨δ, hδ, hδo⟩ := over_open S hksI h
    obtain ⟨u, ⟨huI, huU⟩, hu'⟩ := exists_lt_of_lt_csSup hne (show ks - δ < ks by linarith)
    have hule : u ≤ ks := le_csSup hbdd ⟨huI, huU⟩
    have hd : |u - ks| < δ := by rw [abs_lt]; constructor <;> linarith
    exact under_not_over S huI (hδo u huI hd) huU
  -- positivity, monotonicity, tail
  have hnn : ∀ ξ, 1 ≤ ξ → 0 ≤ L ks ξ := by
    intro ξ hξ
    by_contra h
    push Not at h
    exact hnu ⟨ξ, hξ, h⟩
  have hpos := no_double_zero S hksI hnn
  have hdec : ∀ ξ, 5 / 2 ≤ ξ → L' ks ξ ≤ 0 := by
    intro b hb
    by_contra h
    push Not at h
    exact hno ⟨b, hb, fun ξ hξ => hpos ξ hξ.1, h⟩
  obtain ⟨htend, hint⟩ := H2Tail.tail_of_nonincreasing (L := L ks) (L' := L' ks)
    (N := fun x => 4 * x - ks * x ^ 2 + A ks) (a := 5 / 2) (κ := κ) (by norm_num) S.pos_κ
    (fun x hx => S.dL ks hksI x (by linarith [mem_Ici.mp hx]))
    (fun x hx => S.dP ks hksI x (by linarith [mem_Ici.mp hx]))
    (fun x hx => S.neg ks hksI x hx) (fun x hx => hpos x (by linarith [mem_Ici.mp hx]))
    (fun x hx => hdec x hx)
  refine ⟨ks, hksI, hpos, hdec, htend, ?_⟩
  have hcomp : IntegrableOn (fun x => L ks x ^ 2 * x ^ 2) (Icc 1 (5 / 2)) := by
    refine ContinuousOn.integrableOn_Icc ?_
    intro x hx
    exact (((S.dL ks hksI x (by linarith [hx.1])).continuousAt.pow 2).mul
      (continuousAt_id.pow 2)).continuousWithinAt
  have hu : Icc (1 : ℝ) (5 / 2) ∪ Ici (5 / 2) = Ici 1 := Icc_union_Ici_eq_Ici (by norm_num)
  rw [← hu]
  exact hcomp.union hint

end Work.Quantum.H2Events
