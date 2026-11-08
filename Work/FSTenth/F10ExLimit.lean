import Mathlib
import Work.FSTenth.F10ExBase

/-!
# K = 10 (Falkner–Skan β = 1/10, scaled) existence: no shooting event ⇒ a solution of the boundary-value problem (run 2026-11-07T2028Z)

`no_event`: a trajectory `Y = (f, p, q)` of the clamped field `vH` from `(0, 0, α)`, `0 < α < 2`,
along which neither shooting event (`Under`, `Over`) happens, keeps `p < 1` and `q > 0` for all
times (first exit time: an exit with `q = 0`, `p < 1` is an undershoot, an exit with `p = 1`,
`q > 0` an overshoot, and an exit at `(·, 1, 0)` is excluded by backward uniqueness against the
exact line `(f(τ) + t − τ, 1, 0)`). Then every clamp is inactive, `Y` solves the K = 10 (Falkner–Skan β = 1/10, scaled) system
on `[0, ∞)`, and `p → 1` (if `p → L < 1`, `q' ≤ L² − 1 < 0` would drive `q` negative).
-/

namespace Work.FSTenth.F10ExLimit
open Set Filter Topology Work.FSTenth.F10ExBase

theorem fst_derivW {Y : ℝ → ℝ × ℝ × ℝ} {d : ℝ × ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt Y d s t) : HasDerivWithinAt (fun r => (Y r).1) d.1 s t := by
  have := h.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa using this

theorem snd_derivW {Y : ℝ → ℝ × ℝ × ℝ} {d : ℝ × ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt Y d s t) : HasDerivWithinAt (fun r => (Y r).2) d.2 s t := by
  have := h.hasFDerivWithinAt.snd.hasDerivWithinAt
  simpa using this

theorem snd1_derivW {Y : ℝ → ℝ × ℝ × ℝ} {d : ℝ × ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt Y d s t) : HasDerivWithinAt (fun r => (Y r).2.1) d.2.1 s t := by
  have h2 := snd_derivW h
  have := h2.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa using this

theorem snd2_derivW {Y : ℝ → ℝ × ℝ × ℝ} {d : ℝ × ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt Y d s t) : HasDerivWithinAt (fun r => (Y r).2.2) d.2.2 s t := by
  have h2 := snd_derivW h
  have := h2.hasFDerivWithinAt.snd.hasDerivWithinAt
  simpa using this

theorem cl_pos {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : 0 < cl c y := by
  unfold cl
  exact lt_max_of_lt_right (lt_min hc hy)

theorem cl_zero (c : ℝ) (hc : 0 ≤ c) : cl c 0 = 0 := cl_of_abs_le (by simpa using hc)

/-- A positive right derivative: the function increases just to the right. -/
theorem eventually_gt_of_deriv_pos {g : ℝ → ℝ} {v τ : ℝ} {s : Set ℝ} (hs : Ici τ ⊆ s)
    (h : HasDerivWithinAt g v s τ) (hv : 0 < v) : ∀ᶠ x in 𝓝[>] τ, g τ < g x := by
  have h' := (h.mono hs)
  rw [hasDerivWithinAt_iff_tendsto_slope] at h'
  have h'' : Tendsto (slope g τ) (𝓝[>] τ) (𝓝 v) :=
    h'.mono_left (nhdsWithin_mono _ fun x (hx : τ < x) => ⟨show τ ≤ x from le_of_lt hx, show x ≠ τ from ne_of_gt hx⟩)
  filter_upwards [(tendsto_order.1 h'').1 0 hv, self_mem_nhdsWithin] with x hx hxτ
  rw [slope_def_field] at hx
  have hpos : 0 < x - τ := sub_pos.2 hxτ
  have := (div_pos_iff_of_pos_right hpos).1 hx
  linarith

/-- A negative right derivative: the function decreases just to the right. -/
theorem eventually_lt_of_deriv_neg {g : ℝ → ℝ} {v τ : ℝ} {s : Set ℝ} (hs : Ici τ ⊆ s)
    (h : HasDerivWithinAt g v s τ) (hv : v < 0) : ∀ᶠ x in 𝓝[>] τ, g x < g τ := by
  have := eventually_gt_of_deriv_pos hs h.neg (by linarith)
  filter_upwards [this] with x hx
  have h2 : -g τ < -g x := hx
  linarith

/-- An open condition at τ ≥ 0 holds on some [τ, τ + ε). -/
theorem Ico_of_cont {g : ℝ → ℝ} {τ c : ℝ} (hτ : 0 ≤ τ) (hg : ContinuousWithinAt g (Ici 0) τ)
    (hlt : g τ < c) : ∃ ε > 0, ∀ s ∈ Ico τ (τ + ε), g s < c := by
  have h1 : ∀ᶠ s in 𝓝[Ici 0] τ, g s < c := hg.eventually (gt_mem_nhds hlt)
  have h2 : ∀ᶠ s in 𝓝[≥] τ, g s < c :=
    (nhdsWithin_mono _ (fun x (hx : τ ≤ x) => show (0 : ℝ) ≤ x from hτ.trans hx)) h1
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h2
  refine ⟨u - τ, by linarith [hu.out], fun s hs => hsub ⟨hs.1, by linarith [hs.2]⟩⟩

theorem Ico_of_cont' {g : ℝ → ℝ} {τ c : ℝ} (hτ : 0 ≤ τ) (hg : ContinuousWithinAt g (Ici 0) τ)
    (hlt : c < g τ) : ∃ ε > 0, ∀ s ∈ Ico τ (τ + ε), c < g s := by
  obtain ⟨ε, hε, h⟩ := Ico_of_cont (g := fun x => -g x) (c := -c) hτ hg.neg (by linarith)
  exact ⟨ε, hε, fun s hs => by have h2 : -g s < -c := h s hs; linarith⟩

/-- Limit from the left of a strict bound on [0, τ). -/
theorem le_of_left {g : ℝ → ℝ} {τ c : ℝ} (hτ : 0 < τ) (hg : ContinuousWithinAt g (Ici 0) τ)
    (hb : ∀ s ∈ Ico 0 τ, g s ≤ c) : g τ ≤ c := by
  have hle : 𝓝[<] τ ≤ 𝓝[Ici 0] τ := by
    refine (nhdsWithin_le_of_mem (Ico_mem_nhdsLT hτ)).trans (nhdsWithin_mono _ ?_)
    exact fun x hx => hx.1
  have ht : Tendsto g (𝓝[<] τ) (𝓝 (g τ)) := hg.tendsto.mono_left hle
  apply le_of_tendsto ht
  filter_upwards [Ico_mem_nhdsLT hτ] with s hs using hb s hs

theorem cl_nonneg {c y : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) : 0 ≤ cl c y := by
  unfold cl
  exact le_max_of_le_right (le_min hc hy)

/-- No shooting event: the trajectory solves the K = 10 (Falkner–Skan β = 1/10, scaled) system on [0, ∞) and p → 1. -/
theorem no_event {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (Y : ℝ → ℝ × ℝ × ℝ) (h0 : Y 0 = (0, 0, α))
    (hY : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vH t (Y t)) (Ici 0) t)
    (hback : ∀ τ, 0 ≤ τ → ∀ Z : ℝ → ℝ × ℝ × ℝ,
      (∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vH t (Z t)) (Icc 0 τ) t) → Z τ = Y τ → Z 0 = Y 0)
    (hU : ¬ Under Y) (hO : ¬ Over Y) :
    (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).1) (Y t).2.1 (Ici 0) t) ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).2.1) (Y t).2.2 (Ici 0) t) ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).2.2)
      (-(10 * (Y t).1 * (Y t).2.2) - 1 + (Y t).2.1 ^ 2) (Ici 0) t) ∧
    Filter.Tendsto (fun s => (Y s).2.1) Filter.atTop (nhds 1) := by
  have hf' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).1) (cl 2 (Y t).2.1) (Ici 0) t :=
    fun t ht => fst_derivW (hY t ht)
  have hp' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).2.1) (cl 2 (Y t).2.2) (Ici 0) t :=
    fun t ht => snd1_derivW (hY t ht)
  have hq' : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (Y s).2.2)
      (-(10 * cl (max t 0 + 2) (Y t).1 * cl 2 (Y t).2.2) - 1 + cl 2 (Y t).2.1 ^ 2) (Ici 0) t :=
    fun t ht => snd2_derivW (hY t ht)
  have cf : ∀ t ∈ Ici (0 : ℝ), ContinuousWithinAt (fun s => (Y s).1) (Ici 0) t :=
    fun t ht => (hf' t ht).continuousWithinAt
  have cp : ∀ t ∈ Ici (0 : ℝ), ContinuousWithinAt (fun s => (Y s).2.1) (Ici 0) t :=
    fun t ht => (hp' t ht).continuousWithinAt
  have cq : ∀ t ∈ Ici (0 : ℝ), ContinuousWithinAt (fun s => (Y s).2.2) (Ici 0) t :=
    fun t ht => (hq' t ht).continuousWithinAt
  have f0 : (Y 0).1 = 0 := by rw [h0]
  have p0 : (Y 0).2.1 = 0 := by rw [h0]
  have q0 : (Y 0).2.2 = α := by rw [h0]
  have c2 : (0 : ℝ) ≤ 2 := by norm_num
  -- p < 1 and q > 0 for all times (first exit time)
  have key : ∀ t, 0 ≤ t → (Y t).2.1 < 1 ∧ 0 < (Y t).2.2 := by
    by_contra hcon
    push Not at hcon
    set S := {t : ℝ | 0 ≤ t ∧ ¬ ((Y t).2.1 < 1 ∧ 0 < (Y t).2.2)} with hS
    have hSne : S.Nonempty := by
      obtain ⟨t, ht, h⟩ := hcon
      exact ⟨t, ht, fun hh => absurd (h hh.1) (not_le.2 hh.2)⟩
    have hSbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
    set τ := sInf S with hτdef
    have hτ0 : 0 ≤ τ := le_csInf hSne (fun x hx => hx.1)
    have below : ∀ s ∈ Ico 0 τ, (Y s).2.1 < 1 ∧ 0 < (Y s).2.2 := by
      intro s hs
      by_contra hn
      exact absurd (csInf_le hSbdd ⟨hs.1, hn⟩) (not_le.2 hs.2)
    have notG : ¬ ((Y τ).2.1 < 1 ∧ 0 < (Y τ).2.2) := by
      rintro ⟨h1, h2⟩
      obtain ⟨ε1, hε1, k1⟩ := Ico_of_cont hτ0 (cp τ hτ0) h1
      obtain ⟨ε2, hε2, k2⟩ := Ico_of_cont' hτ0 (cq τ hτ0) h2
      have hm := lt_min hε1 hε2
      obtain ⟨s, hsS, hs⟩ := exists_lt_of_csInf_lt hSne (show τ < τ + min ε1 ε2 by linarith)
      have hτs : τ ≤ s := csInf_le hSbdd hsS
      exact hsS.2 ⟨k1 s ⟨hτs, by linarith [min_le_left ε1 ε2]⟩,
        k2 s ⟨hτs, by linarith [min_le_right ε1 ε2]⟩⟩
    have hτpos : 0 < τ := by
      rcases hτ0.lt_or_eq with h | h
      · exact h
      · exfalso; apply notG; rw [← h, p0, q0]; exact ⟨by norm_num, hα0⟩
    have pτ : (Y τ).2.1 ≤ 1 := le_of_left hτpos (cp τ hτ0) (fun s hs => (below s hs).1.le)
    have qτ : 0 ≤ (Y τ).2.2 := by
      have h := le_of_left (g := fun s => -(Y s).2.2) (c := 0) hτpos (cq τ hτ0).neg
        (fun s hs => by have := (below s hs).2; show -(Y s).2.2 ≤ 0; linarith)
      have h' : -(Y τ).2.2 ≤ 0 := h
      linarith
    have hsubI : interior (Icc (0 : ℝ) τ) ⊆ Ici 0 := by
      intro y hy; rw [interior_Icc] at hy; exact le_of_lt hy.1
    have pmono : MonotoneOn (fun s => (Y s).2.1) (Icc 0 τ) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => cl 2 (Y x).2.2) (convex_Icc 0 τ)
        (fun x hx => (cp x hx.1).mono Icc_subset_Ici_self) ?_ ?_
      · intro x hx
        exact (hp' x (hsubI hx)).mono (hsubI)
      · intro x hx
        rw [interior_Icc] at hx
        exact (cl_pos (c := 2) (by norm_num) (below x ⟨hx.1.le, hx.2⟩).2).le
    have pτ0 : 0 ≤ (Y τ).2.1 := by
      have h1 : (Y 0).2.1 ≤ (Y τ).2.1 := pmono ⟨le_rfl, hτ0⟩ ⟨hτ0, le_rfl⟩ hτ0
      rw [p0] at h1; exact h1
    have hsplit : (Y τ).2.1 = 1 ∨ (Y τ).2.2 = 0 := by
      by_contra hc
      push Not at hc
      exact notG ⟨lt_of_le_of_ne pτ hc.1, lt_of_le_of_ne qτ (Ne.symm hc.2)⟩
    have hIci : Ici τ ⊆ Ici (0 : ℝ) := fun x (hx : τ ≤ x) => show (0 : ℝ) ≤ x from hτ0.trans hx
    have case3 : (Y τ).2.1 = 1 → (Y τ).2.2 = 0 → False := by
      intro e1 e2
      set Z : ℝ → ℝ × ℝ × ℝ := fun t => ((Y τ).1 + (t - τ), 1, 0) with hZ
      have c1 : cl 2 (1 : ℝ) = 1 := cl_of_abs_le (by norm_num)
      have c0 : cl 2 (0 : ℝ) = 0 := cl_zero 2 c2
      have hZd : ∀ t ∈ Icc 0 τ, HasDerivWithinAt Z (vH t (Z t)) (Icc 0 τ) t := by
        intro t _
        have hv : vH t (Z t) = ((1 : ℝ), (0 : ℝ), (0 : ℝ)) := by
          show (cl 2 (1 : ℝ), cl 2 (0 : ℝ),
            -(10 * cl (max t 0 + 2) ((Y τ).1 + (t - τ)) * cl 2 (0 : ℝ)) - 1 + cl 2 (1 : ℝ) ^ 2) = _
          rw [c1, c0]; norm_num
        rw [hv]
        have h1 : HasDerivAt (fun t : ℝ => (Y τ).1 + (t - τ)) 1 t := by
          simpa using ((hasDerivAt_id t).sub_const τ).const_add ((Y τ).1)
        exact (h1.prodMk ((hasDerivAt_const t (1 : ℝ)).prodMk
          (hasDerivAt_const t (0 : ℝ)))).hasDerivWithinAt
      have hZτ : Z τ = Y τ := by
        simp only [hZ, sub_self, add_zero]
        ext
        · rfl
        · exact e1.symm
        · exact e2.symm
      have h := hback τ hτ0 Z hZd hZτ
      have h2 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) h
      simp only [hZ, p0] at h2
      norm_num at h2
    rcases hsplit with e1 | e2
    · rcases qτ.lt_or_eq with hq | hq
      · apply hO
        have ev := eventually_gt_of_deriv_pos hIci (hp' τ hτ0) (cl_pos (c := 2) (by norm_num) hq)
        obtain ⟨ε, hε, k⟩ := Ico_of_cont' hτ0 (cq τ hτ0) hq
        obtain ⟨η, hη1, hη2⟩ := (ev.and (Ioo_mem_nhdsGT (by linarith : τ < τ + ε))).exists
        refine ⟨η, by linarith [hη2.1], ?_, ?_⟩
        · have : (Y τ).2.1 < (Y η).2.1 := hη1
          linarith
        · intro s hs
          rcases lt_or_ge s τ with h | h
          · exact (below s ⟨hs.1, h⟩).2
          · exact k s ⟨h, by linarith [hs.2, hη2.2]⟩
      · exact case3 e1 hq.symm
    · rcases pτ.lt_or_eq with hp | hp
      · apply hU
        have hv : -(10 * cl (max τ 0 + 2) (Y τ).1 * cl 2 (Y τ).2.2) - 1 + cl 2 (Y τ).2.1 ^ 2 < 0 := by
          rw [e2, cl_zero 2 c2, cl_of_abs_le (c := 2) (y := (Y τ).2.1) (abs_le.2 ⟨by linarith, by linarith⟩)]
          nlinarith
        have ev := eventually_lt_of_deriv_neg hIci (hq' τ hτ0) hv
        obtain ⟨ε, hε, k⟩ := Ico_of_cont hτ0 (cp τ hτ0) hp
        obtain ⟨η, hη1, hη2⟩ := (ev.and (Ioo_mem_nhdsGT (by linarith : τ < τ + ε))).exists
        refine ⟨η, by linarith [hη2.1], ?_, ?_⟩
        · have : (Y η).2.2 < (Y τ).2.2 := hη1
          linarith
        · intro s hs
          rcases lt_or_ge s τ with h | h
          · exact (below s ⟨hs.1, h⟩).1
          · exact k s ⟨h, by linarith [hs.2, hη2.2]⟩
      · exact case3 hp e2
  -- global consequences
  have hsubI : interior (Ici (0 : ℝ)) ⊆ Ici 0 := interior_subset
  have pmono : MonotoneOn (fun s => (Y s).2.1) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => cl 2 (Y x).2.2) (convex_Ici 0)
      (fun x hx => cp x hx) (fun x hx => (hp' x (hsubI hx)).mono hsubI) ?_
    intro x hx
    exact (cl_pos (c := 2) (by norm_num) (key x (hsubI hx)).2).le
  have pnn : ∀ t, 0 ≤ t → 0 ≤ (Y t).2.1 := by
    intro t ht
    have h1 : (Y 0).2.1 ≤ (Y t).2.1 := pmono (mem_Ici.2 le_rfl) ht ht
    rw [p0] at h1; exact h1
  have clp : ∀ t, 0 ≤ t → cl 2 (Y t).2.1 = (Y t).2.1 := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [pnn t ht], by linarith [(key t ht).1]⟩)
  have fmono : MonotoneOn (fun s => (Y s).1) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => cl 2 (Y x).2.1) (convex_Ici 0)
      (fun x hx => cf x hx) (fun x hx => (hf' x (hsubI hx)).mono hsubI) ?_
    intro x hx
    exact cl_nonneg (pnn x (hsubI hx)) c2
  have fnn : ∀ t, 0 ≤ t → 0 ≤ (Y t).1 := by
    intro t ht
    have h1 : (Y 0).1 ≤ (Y t).1 := fmono (mem_Ici.2 le_rfl) ht ht
    rw [f0] at h1; exact h1
  have fle : ∀ t, 0 ≤ t → (Y t).1 ≤ t := by
    have gmono : MonotoneOn (fun s => s - (Y s).1) (Ici 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => 1 - cl 2 (Y x).2.1)
        (convex_Ici 0) (fun x hx => (continuousWithinAt_id.sub (cf x hx))) ?_ ?_
      · intro x hx
        exact ((hasDerivWithinAt_id x _).sub ((hf' x (hsubI hx)).mono hsubI))
      · intro x hx
        rw [clp x (hsubI hx)]
        linarith [(key x (hsubI hx)).1]
    intro t ht
    have h1 : 0 - (Y 0).1 ≤ t - (Y t).1 := gmono (mem_Ici.2 le_rfl) ht ht
    rw [f0] at h1; linarith
  have qder : ∀ t, 0 ≤ t →
      -(10 * cl (max t 0 + 2) (Y t).1 * cl 2 (Y t).2.2) - 1 + cl 2 (Y t).2.1 ^ 2 ≤ -1 + (Y t).2.1 ^ 2 := by
    intro t ht
    rw [clp t ht]
    have := mul_nonneg (cl_nonneg (fnn t ht) (by positivity : (0 : ℝ) ≤ max t 0 + 2))
      (cl_pos (c := 2) (by norm_num) (key t ht).2).le
    linarith
  have qmono : AntitoneOn (fun s => (Y s).2.2) (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (fun x hx => cq x hx)
      (fun x hx => (hq' x (hsubI hx)).mono hsubI) ?_
    intro x hx
    have h1 := qder x (hsubI hx)
    have h2 := (key x (hsubI hx)).1
    have h3 := pnn x (hsubI hx)
    nlinarith
  have qle : ∀ t, 0 ≤ t → (Y t).2.2 ≤ α := by
    intro t ht
    have h1 : (Y t).2.2 ≤ (Y 0).2.2 := qmono (mem_Ici.2 le_rfl) ht ht
    rw [q0] at h1; exact h1
  have clq : ∀ t, 0 ≤ t → cl 2 (Y t).2.2 = (Y t).2.2 := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [(key t ht).2], by linarith [qle t ht]⟩)
  have clf : ∀ t, 0 ≤ t → cl (max t 0 + 2) (Y t).1 = (Y t).1 := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [fnn t ht, le_max_right t 0],
      by linarith [fle t ht, le_max_left t 0]⟩)
  refine ⟨fun t ht => (hf' t ht).congr_deriv (clp t ht), fun t ht => (hp' t ht).congr_deriv (clq t ht),
    fun t ht => (hq' t ht).congr_deriv (by rw [clf t ht, clq t ht, clp t ht]), ?_⟩
  -- the limit
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hreach : ∃ T, 0 ≤ T ∧ 1 - ε' < (Y T).2.1 := by
    by_contra hno
    push Not at hno
    set c := 1 - (1 - ε') ^ 2 with hc
    have hc0 : 0 < c := by nlinarith
    have hmono : AntitoneOn (fun s => (Y s).2.2 + c * s) (Ici 0) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x =>
          (-(10 * cl (max x 0 + 2) (Y x).1 * cl 2 (Y x).2.2) - 1 + cl 2 (Y x).2.1 ^ 2) + c * 1)
        (convex_Ici 0) (fun x hx => (cq x hx).add (continuousWithinAt_id.const_mul c)) ?_ ?_
      · intro x hx
        exact ((hq' x (hsubI hx)).mono hsubI).add ((hasDerivWithinAt_id x _).const_mul c)
      · intro x hx
        have h1 := qder x (hsubI hx)
        have h2 := hno x (hsubI hx)
        have h3 := pnn x (hsubI hx)
        have h4 : (Y x).2.1 ^ 2 ≤ (1 - ε') ^ 2 := by nlinarith
        show -(10 * cl (max x 0 + 2) (Y x).1 * cl 2 (Y x).2.2) - 1 + cl 2 (Y x).2.1 ^ 2 + c * 1 ≤ 0
        linarith
    set T := α / c + 1 with hT
    have hT0 : 0 ≤ T := by positivity
    have h1 : (Y T).2.2 + c * T ≤ (Y 0).2.2 + c * 0 := hmono (mem_Ici.2 le_rfl) hT0 hT0
    rw [q0] at h1
    have h2 : c * T = α + c := by rw [hT]; field_simp
    have := (key T hT0).2
    linarith
  obtain ⟨T, hT0, hT⟩ := hreach
  refine ⟨T, fun n hn => ?_⟩
  have hn0 : 0 ≤ n := hT0.trans hn
  have h1 : (Y T).2.1 ≤ (Y n).2.1 := pmono hT0 hn0 hn
  have h2 := (key n hn0).1
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [min_le_left ε 1]

end Work.FSTenth.F10ExLimit
