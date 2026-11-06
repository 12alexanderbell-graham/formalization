import Mathlib
import Work.Math.TFExFlow
import Work.Math.TFExEvents
import Work.Math.TFExConvert

/-!
# Thomas–Fermi existence: the shooting argument

For each n the clamped flow on [0, n + 1] (`Work.Math.TFExFlow.exists_flow`) is continuous in the
initial slope s ∈ [−10, 0]. A(s): u goes negative; C(s): Φ goes positive. Both are open, they
exclude each other (`Work.Math.TFExEvents.excl`), A(−10) and C(0) hold. For s₀ = sup {s : A s}
neither holds, so u ≥ 0 and Φ ≤ 0 on [0, ∞); a zero of u would be a zero of the state (local
minimum), excluded by backward uniqueness; u decreases, and a positive limit would push Φ above 0.
-/

namespace Work.Math.TFExAssemble
open Set Filter Topology Work.Math.TFExBase

theorem g_mono {a b : ℝ} (h : a ≤ b) : g a ≤ g b := by
  unfold g
  have h1 : max a 0 ≤ max b 0 := max_le_max h le_rfl
  exact mul_le_mul h1 (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _) ((le_max_right _ _).trans h1)

theorem fst_deriv {T t : ℝ} {f : ℝ → ℝ × ℝ} {p : ℝ × ℝ} (h : HasDerivWithinAt f p (Icc 0 T) t) :
    HasDerivWithinAt (fun τ => (f τ).1) p.1 (Icc 0 T) t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

theorem snd_deriv {T t : ℝ} {f : ℝ → ℝ × ℝ} {p : ℝ × ℝ} (h : HasDerivWithinAt f p (Icc 0 T) t) :
    HasDerivWithinAt (fun τ => (f τ).2) p.2 (Icc 0 T) t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

/-- A solution of the clamped field on [0, T] with initial slope s. -/
structure Sol (T s : ℝ) (f : ℝ → ℝ × ℝ) : Prop where
  init : f 0 = (1, s)
  deriv : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (F T t (f t)) (Icc 0 T) t

theorem Sol.u {T s : ℝ} {f : ℝ → ℝ × ℝ} (h : Sol T s f) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun τ => (f τ).1) (2 * t * cl 10 (f t).2) (Icc 0 T) t :=
  fun t ht => by have := fst_deriv (h.deriv t ht); rwa [F_fst ht] at this

theorem Sol.phi {T s : ℝ} {f : ℝ → ℝ × ℝ} (h : Sol T s f) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun τ => (f τ).2) (2 * g (min (f t).1 2)) (Icc 0 T) t :=
  fun t ht => snd_deriv (h.deriv t ht)

theorem Sol.u0 {T s : ℝ} {f : ℝ → ℝ × ℝ} (h : Sol T s f) : (fun τ => (f τ).1) 0 = 1 := by
  show (f 0).1 = 1; rw [h.init]

theorem Sol.phi0 {T s : ℝ} {f : ℝ → ℝ × ℝ} (h : Sol T s f) : (fun τ => (f τ).2) 0 = s := by
  show (f 0).2 = s; rw [h.init]

theorem cast_le_cast {n m : ℕ} (h : n ≤ m) : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
  have := (Nat.cast_le (α := ℝ)).2 h; linarith

theorem main : ∃ U P : ℝ → ℝ,
    (∀ t, 0 ≤ t → HasDerivWithinAt U (2 * t * P t) (Ici 0) t) ∧
    (∀ t, 0 ≤ t → HasDerivWithinAt P (2 * g (U t)) (Ici 0) t) ∧
    U 0 = 1 ∧ (∀ t, 0 ≤ t → 0 < U t) ∧ Tendsto U atTop (𝓝 0) := by
  choose α hα hcont using
    fun n : ℕ => Work.Math.TFExFlow.exists_flow ((n : ℝ) + 1) (by positivity)
  have hsol : ∀ (n : ℕ) (s : ℝ), s ∈ Icc (-10 : ℝ) 0 → Sol ((n : ℝ) + 1) s (α n s) :=
    fun n s hs => ⟨(hα n s hs).1, (hα n s hs).2⟩
  have agree : ∀ (n m : ℕ) (s : ℝ), s ∈ Icc (-10 : ℝ) 0 → ∀ t, t ∈ Icc 0 ((n : ℝ) + 1) →
      t ∈ Icc 0 ((m : ℝ) + 1) → α n s t = α m s t := by
    intro n m s hs t htn htm
    rcases le_total n m with h | h
    · exact Work.Math.TFExFlow.consistent (by positivity) (cast_le_cast h) _ _
        (by rw [(hα n s hs).1, (hα m s hs).1]) (hα n s hs).2 (hα m s hs).2 htn
    · exact (Work.Math.TFExFlow.consistent (by positivity) (cast_le_cast h) _ _
        (by rw [(hα n s hs).1, (hα m s hs).1]) (hα m s hs).2 (hα n s hs).2 htm).symm
  -- the two events
  let A : ℝ → Prop := fun s => ∃ n : ℕ, ∃ t ∈ Icc 0 ((n : ℝ) + 1), (α n s t).1 < 0
  let C : ℝ → Prop := fun s => ∃ n : ℕ, ∃ t ∈ Icc 0 ((n : ℝ) + 1), 0 < (α n s t).2
  have excl : ∀ s ∈ Icc (-10 : ℝ) 0, A s → C s → False := by
    rintro s hs ⟨n, t₁, ht₁, h₁⟩ ⟨m, t₂, ht₂, h₂⟩
    have hN : ∀ k, k ≤ max n m → ∀ t ∈ Icc 0 ((k : ℝ) + 1), t ∈ Icc 0 (((max n m : ℕ) : ℝ) + 1) :=
      fun k hk t ht => ⟨ht.1, ht.2.trans (cast_le_cast hk)⟩
    have ht₁' := hN n (le_max_left _ _) t₁ ht₁
    have ht₂' := hN m (le_max_right _ _) t₂ ht₂
    rw [agree n (max n m) s hs t₁ ht₁ ht₁'] at h₁
    rw [agree m (max n m) s hs t₂ ht₂ ht₂'] at h₂
    have hS := hsol (max n m) s hs
    have := Work.Math.TFExEvents.excl hS.u hS.phi hS.u0 ⟨t₁, ht₁', h₁⟩ t₂ ht₂'
    linarith
  have openA : ∀ s ∈ Icc (-10 : ℝ) 0, A s →
      ∃ ε > 0, ∀ s' ∈ Icc (-10 : ℝ) 0, |s' - s| < ε → A s' := by
    rintro s hs ⟨n, t, ht, h⟩
    have hc : ContinuousWithinAt (fun s => (α n s t).1) (Icc (-10 : ℝ) 0) s :=
      continuous_fst.continuousAt.comp_continuousWithinAt (hcont n t ht s hs)
    rw [Metric.continuousWithinAt_iff] at hc
    obtain ⟨ε, hε, hδ⟩ := hc (-(α n s t).1) (by linarith)
    refine ⟨ε, hε, fun s' hs' hd => ⟨n, t, ht, ?_⟩⟩
    have := hδ hs' (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).2]
  have openC : ∀ s ∈ Icc (-10 : ℝ) 0, C s →
      ∃ ε > 0, ∀ s' ∈ Icc (-10 : ℝ) 0, |s' - s| < ε → C s' := by
    rintro s hs ⟨n, t, ht, h⟩
    have hc : ContinuousWithinAt (fun s => (α n s t).2) (Icc (-10 : ℝ) 0) s :=
      continuous_snd.continuousAt.comp_continuousWithinAt (hcont n t ht s hs)
    rw [Metric.continuousWithinAt_iff] at hc
    obtain ⟨ε, hε, hδ⟩ := hc ((α n s t).2) h
    refine ⟨ε, hε, fun s' hs' hd => ⟨n, t, ht, ?_⟩⟩
    have := hδ hs' (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).1]
  have hA10 : A (-10) := by
    have hS := hsol 0 (-10) ⟨le_rfl, by norm_num⟩
    refine ⟨0, 1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    exact Work.Math.TFExEvents.low_event hS.u hS.phi (by norm_num) hS.u0 hS.phi0
  have hC0 : C 0 := by
    have hS := hsol 0 0 ⟨by norm_num, le_rfl⟩
    obtain ⟨t, ht, h⟩ := Work.Math.TFExEvents.high_event hS.u hS.phi (by positivity) hS.u0 hS.phi0
    exact ⟨0, t, ht, h⟩
  -- the critical slope
  let S : Set ℝ := {s | s ∈ Icc (-10 : ℝ) 0 ∧ A s}
  have hne : S.Nonempty := ⟨-10, ⟨le_rfl, by norm_num⟩, hA10⟩
  have hbdd : BddAbove S := ⟨0, fun s hs => hs.1.2⟩
  obtain ⟨s₀, hs₀def⟩ : ∃ s₀, s₀ = sSup S := ⟨_, rfl⟩
  have hs₀ : s₀ ∈ Icc (-10 : ℝ) 0 := by
    rw [hs₀def]
    exact ⟨le_csSup hbdd ⟨⟨le_rfl, by norm_num⟩, hA10⟩, csSup_le hne (fun s hs => hs.1.2)⟩
  have notA : ¬ A s₀ := by
    intro hA
    have hlt : s₀ < 0 := by
      rcases hs₀.2.lt_or_eq with h | h
      · exact h
      · exfalso; rw [h] at hA; exact excl 0 ⟨by norm_num, le_rfl⟩ hA hC0
    obtain ⟨ε, hε, hε'⟩ := openA s₀ hs₀ hA
    have hpos : 0 < min (ε / 2) (-s₀) := lt_min (by linarith) (by linarith)
    have hs' : s₀ + min (ε / 2) (-s₀) ∈ Icc (-10 : ℝ) 0 :=
      ⟨by linarith [hs₀.1], by linarith [min_le_right (ε / 2) (-s₀)]⟩
    have hA' := hε' _ hs' (by
      rw [show s₀ + min (ε / 2) (-s₀) - s₀ = min (ε / 2) (-s₀) by ring, abs_of_pos hpos]
      linarith [min_le_left (ε / 2) (-s₀)])
    have := le_csSup hbdd (show s₀ + min (ε / 2) (-s₀) ∈ S from ⟨hs', hA'⟩)
    rw [← hs₀def] at this
    linarith
  have notC : ¬ C s₀ := by
    intro hC
    obtain ⟨ε, hε, hε'⟩ := openC s₀ hs₀ hC
    obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup hne (show s₀ - ε < sSup S by rw [← hs₀def]; linarith)
    have hle : s ≤ s₀ := by rw [hs₀def]; exact le_csSup hbdd hsS
    exact excl s hsS.1 hsS.2 (hε' s hsS.1 (by rw [abs_lt]; constructor <;> linarith))
  -- bounds along the critical solution
  have bounds : ∀ n : ℕ, ∀ t ∈ Icc 0 ((n : ℝ) + 1),
      0 ≤ (α n s₀ t).1 ∧ (α n s₀ t).2 ≤ 0 ∧ s₀ ≤ (α n s₀ t).2 ∧ (α n s₀ t).1 ≤ 1 := by
    intro n t ht
    have hS := hsol n s₀ hs₀
    have h1 : 0 ≤ (α n s₀ t).1 := by
      by_contra h; push Not at h; exact notA ⟨n, t, ht, h⟩
    have hP : ∀ τ ∈ Icc 0 ((n : ℝ) + 1), (α n s₀ τ).2 ≤ 0 := by
      intro τ hτ; by_contra h; push Not at h; exact notC ⟨n, τ, hτ, h⟩
    have h3 : s₀ ≤ (α n s₀ t).2 := by
      have := Work.Math.TFExEvents.phi_mono hS.phi ⟨le_rfl, by positivity⟩ ht ht.1
      simpa [hS.init] using this
    have h4 : (α n s₀ t).1 ≤ 1 := by
      have hanti : AntitoneOn (fun τ => (α n s₀ τ).1) (Icc 0 ((n : ℝ) + 1)) := by
        refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
          (fun τ hτ => (hS.u τ hτ).continuousWithinAt)
          (fun τ hτ => (hS.u τ (interior_subset hτ)).mono interior_subset) (fun τ hτ => ?_)
        have hτ' := interior_subset hτ
        have hcl : cl 10 (α n s₀ τ).2 ≤ 0 := by
          by_contra h; push Not at h; have := cl_pos_iff.1 h; linarith [hP τ hτ']
        have : 0 ≤ 2 * τ := by linarith [hτ'.1]
        exact mul_nonpos_of_nonneg_of_nonpos this hcl
      have := hanti ⟨le_rfl, by positivity⟩ ht ht.1
      simpa [hS.init] using this
    exact ⟨h1, hP t ht, h3, h4⟩
  -- the global solution
  have hmemidx : ∀ t : ℝ, 0 ≤ t → t ∈ Icc 0 (((⌈t⌉₊ : ℕ) : ℝ) + 1) :=
    fun t ht => ⟨ht, by linarith [Nat.le_ceil t]⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ → ℝ, U = fun t => (α ⌈t⌉₊ s₀ t).1 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ → ℝ, P = fun t => (α ⌈t⌉₊ s₀ t).2 := ⟨_, rfl⟩
  have hUeq : ∀ n : ℕ, ∀ t ∈ Icc 0 ((n : ℝ) + 1), U t = (α n s₀ t).1 ∧ P t = (α n s₀ t).2 := by
    intro n t ht
    have := agree ⌈t⌉₊ n s₀ hs₀ t (hmemidx t ht.1) ht
    subst hUdef hPdef
    simp only [this]; exact ⟨trivial, trivial⟩
  have gbounds : ∀ t, 0 ≤ t → 0 ≤ U t ∧ P t ≤ 0 ∧ s₀ ≤ P t ∧ U t ≤ 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hUeq _ t (hmemidx t ht)
    rw [h1, h2]; exact bounds _ t (hmemidx t ht)
  have hderiv : ∀ t, 0 ≤ t →
      HasDerivWithinAt U (2 * t * P t) (Ici 0) t ∧ HasDerivWithinAt P (2 * g (U t)) (Ici 0) t := by
    intro t ht
    have htn : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith [Nat.le_ceil t]
    have htm : t ∈ Icc 0 (((⌈t⌉₊ + 1 : ℕ) : ℝ) + 1) := ⟨ht, htn.le⟩
    have hS := hsol (⌈t⌉₊ + 1) s₀ hs₀
    have hnhds : Icc 0 (((⌈t⌉₊ + 1 : ℕ) : ℝ) + 1) ∈ 𝓝[Ici 0] t := by
      have := inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iic_mem_nhds htn)
      rwa [Ici_inter_Iic] at this
    have heqU : U =ᶠ[𝓝[Ici 0] t] (fun τ => (α (⌈t⌉₊ + 1) s₀ τ).1) :=
      Filter.mem_of_superset hnhds (fun τ hτ => (hUeq _ τ hτ).1)
    have heqP : P =ᶠ[𝓝[Ici 0] t] (fun τ => (α (⌈t⌉₊ + 1) s₀ τ).2) :=
      Filter.mem_of_superset hnhds (fun τ hτ => (hUeq _ τ hτ).2)
    obtain ⟨hUt, hPt⟩ := hUeq _ t htm
    obtain ⟨b1, b2, b3, b4⟩ := gbounds t ht
    have habs : |P t| ≤ 10 := by rw [abs_le]; constructor <;> linarith [hs₀.1]
    constructor
    · have h1 := ((hS.u t htm).mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq heqU hUt
      rwa [← hPt, cl_of_abs_le habs] at h1
    · have h1 := ((hS.phi t htm).mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq heqP hPt
      rwa [← hUt, min_eq_left (by linarith)] at h1
  have hU0 : U 0 = 1 := by
    rw [(hUeq 0 0 ⟨le_rfl, by positivity⟩).1, (hsol 0 s₀ hs₀).init]
  have hpos : ∀ t, 0 ≤ t → 0 < U t := by
    intro t ht
    rcases (gbounds t ht).1.lt_or_eq with h | h
    · exact h
    exfalso
    have ht0 : 0 < t := by
      rcases ht.lt_or_eq with h' | h'
      · exact h'
      · subst h'; rw [hU0] at h; norm_num at h
    have htn : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith [Nat.le_ceil t]
    have htm : t ∈ Icc 0 (((⌈t⌉₊ + 1 : ℕ) : ℝ) + 1) := ⟨ht, htn.le⟩
    have hS := hsol (⌈t⌉₊ + 1) s₀ hs₀
    have hu0 : (α (⌈t⌉₊ + 1) s₀ t).1 = 0 := by rw [← (hUeq _ t htm).1]; exact h.symm
    have hnh : Icc 0 (((⌈t⌉₊ + 1 : ℕ) : ℝ) + 1) ∈ 𝓝 t := Icc_mem_nhds ht0 htn
    have hloc : IsLocalMin (fun τ => (α (⌈t⌉₊ + 1) s₀ τ).1) t := by
      filter_upwards [hnh] with τ hτ
      show (α (⌈t⌉₊ + 1) s₀ t).1 ≤ (α (⌈t⌉₊ + 1) s₀ τ).1
      rw [hu0]; exact (bounds _ τ hτ).1
    have hz := hloc.hasDerivAt_eq_zero ((hS.u t htm).hasDerivAt hnh)
    have hcl : cl 10 (α (⌈t⌉₊ + 1) s₀ t).2 = 0 := by
      rcases mul_eq_zero.1 hz with h2 | h2
      · linarith
      · exact h2
    have hf0 : α (⌈t⌉₊ + 1) s₀ t = 0 := Prod.ext hu0 (cl_eq_zero_iff.1 hcl)
    have := Work.Math.TFExFlow.zero_backward (by positivity) ⟨ht0, htn.le⟩ _ hS.deriv hf0
    rw [hS.init] at this
    have := congrArg Prod.fst this
    norm_num at this
  have hanti : AntitoneOn U (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht => (hderiv t ht).1.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).1.mono interior_subset) (fun t ht => ?_)
    have ht' : (0 : ℝ) ≤ t := interior_subset ht
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (gbounds t ht').2.1
  have hlim : Tendsto U atTop (𝓝 0) := by
    rw [tendsto_order]; constructor
    · intro a ha
      filter_upwards [eventually_ge_atTop 0] with t ht
      linarith [hpos t ht]
    · intro a ha
      have hex : ∃ T, 0 ≤ T ∧ U T < a := by
        by_contra hno
        push Not at hno
        have hga : 0 < g a := g_pos ha
        have hmono : MonotoneOn (fun t => P t - 2 * g a * t) (Ici 0) := by
          refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => 2 * g (U t) - 2 * g a * 1)
            (convex_Ici 0)
            (fun t ht => ((hderiv t ht).2.sub
              (((hasDerivAt_id t).const_mul (2 * g a)).hasDerivWithinAt)).continuousWithinAt)
            (fun t ht => ((hderiv t (interior_subset ht)).2.sub
              (((hasDerivAt_id t).const_mul (2 * g a)).hasDerivWithinAt)).mono interior_subset)
            (fun t ht => ?_)
          have := g_mono (hno t (interior_subset ht))
          linarith
        set t₁ := (1 - s₀) / (2 * g a)
        have ht₁ : 0 ≤ t₁ := div_nonneg (by linarith [hs₀.2]) (by positivity)
        have h1 := hmono (show (0 : ℝ) ∈ Ici 0 from mem_Ici.2 le_rfl) (show t₁ ∈ Ici 0 from ht₁) ht₁
        have hP0 : P 0 = s₀ := by
          rw [(hUeq 0 0 ⟨le_rfl, by positivity⟩).2, (hsol 0 s₀ hs₀).init]
        simp only [hP0, mul_zero, sub_zero] at h1
        have h2 : 2 * g a * t₁ = 1 - s₀ := by
          simp only [t₁]; field_simp
        linarith [(gbounds t₁ ht₁).2.1]
      obtain ⟨T, hT0, hTa⟩ := hex
      filter_upwards [eventually_ge_atTop T] with t ht
      exact lt_of_le_of_lt (hanti (show T ∈ Ici 0 from hT0)
        (show t ∈ Ici 0 from hT0.trans ht) ht) hTa
  exact ⟨U, P, fun t ht => (hderiv t ht).1, fun t ht => (hderiv t ht).2, hU0, hpos, hlim⟩

end Work.Math.TFExAssemble
