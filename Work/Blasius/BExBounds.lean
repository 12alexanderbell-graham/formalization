import Mathlib
import Work.Blasius.BExBase
import Work.Blasius.BTail

/-!
# Blasius existence: the clamps of `vF` are inactive along the flow from (0, 0, 1)
(run 2026-11-07T1228Z)

Along any solution Y of Y' = vF t Y on [0, ∞) with Y(0) = (0, 0, 1): q > 0 (a zero of q would
propagate back to t = 0 by uniqueness for the clamped linear equation), p and g increase, q
decreases, g ≤ 4t, and p < 4 (on [0, T] with the true equations, g ≥ t² q/2, so
(1/q − t³/12)' ≥ 0, q ≤ 12/t³ and p + 6/t² decreases past 5/2: p ≤ 173/50). So every clamp is
inactive, the components solve the Blasius system (`BTail.IsSol`), and p increases to a limit
α > 0.
-/

namespace Work.Blasius.BExBounds
open Set Filter Topology Work.Blasius.BExBase

theorem fst_derivW {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ → E × F} {d : E × F} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α d s t) : HasDerivWithinAt (fun r => (α r).1) d.1 s t := by
  have := h.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa using this

theorem snd_derivW {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ → E × F} {d : E × F} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α d s t) : HasDerivWithinAt (fun r => (α r).2) d.2 s t := by
  have := h.hasFDerivWithinAt.snd.hasDerivWithinAt
  simpa using this

theorem cl_sub (c y z : ℝ) : |cl c y - cl c z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem cl_abs {c y : ℝ} (hc : 0 ≤ c) : |cl c y| ≤ c := by
  unfold cl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem cl_nonneg {c y : ℝ} (hc : 0 ≤ c) (hy : 0 ≤ y) : 0 ≤ cl c y := by
  unfold cl; exact le_max_of_le_right (le_min hc hy)

theorem cl_pos {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : 0 < cl c y := by
  unfold cl; exact lt_max_of_lt_right (lt_min hc hy)

theorem cl_le {c y : ℝ} (hc : 0 ≤ c) : cl c y ≤ c := (le_abs_self _).trans (cl_abs hc)

theorem lipcl {k M : ℝ} (hk : |k| ≤ M) :
    LipschitzOnWith (Real.toNNReal (M / 2)) (fun y : ℝ => -(k * cl 2 y / 2)) univ := by
  have hM : 0 ≤ M := (abs_nonneg k).trans hk
  refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
  rw [Real.coe_toNNReal _ (by linarith)]
  simp only [Real.dist_eq]
  have e : -(k * cl 2 x / 2) - -(k * cl 2 y / 2) = -(k / 2) * (cl 2 x - cl 2 y) := by ring
  rw [e, abs_mul, abs_neg, abs_div, abs_two]
  exact mul_le_mul (by linarith) (cl_sub 2 x y) (abs_nonneg _) (by linarith)

theorem monoIcc {u u' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn u (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x) (hn : ∀ x ∈ Ioo a b, 0 ≤ u' x) :
    MonotoneOn u (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (f' := u') hc ?_ ?_
  · intro x hx; rw [interior_Icc] at hx ⊢; exact (hd x hx).hasDerivWithinAt
  · intro x hx; rw [interior_Icc] at hx; exact hn x hx

theorem antiIcc {u u' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn u (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x) (hn : ∀ x ∈ Ioo a b, u' x ≤ 0) :
    AntitoneOn u (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) (f' := u') hc ?_ ?_
  · intro x hx; rw [interior_Icc] at hx ⊢; exact (hd x hx).hasDerivWithinAt
  · intro x hx; rw [interior_Icc] at hx; exact hn x hx

/-- The a-priori bound on p for the true Blasius system on [0, T]. -/
theorem pbound {g p q : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (cg : ContinuousOn g (Icc 0 T)) (cp : ContinuousOn p (Icc 0 T))
    (cq : ContinuousOn q (Icc 0 T))
    (hg : ∀ s ∈ Ioo 0 T, HasDerivAt g (p s) s) (hp : ∀ s ∈ Ioo 0 T, HasDerivAt p (q s) s)
    (hq : ∀ s ∈ Ioo 0 T, HasDerivAt q (-(g s * q s / 2)) s)
    (g0 : g 0 = 0) (p0 : p 0 = 0) (q0 : q 0 = 1)
    (qpos : ∀ s ∈ Icc 0 T, 0 < q s) (gnn : ∀ s ∈ Icc 0 T, 0 ≤ g s) :
    p T ≤ 173 / 50 := by
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have qanti : AntitoneOn q (Icc 0 T) := antiIcc cq hq (fun s hs => by
    have h1 := qpos s (Ioo_subset_Icc_self hs)
    have h2 := gnn s (Ioo_subset_Icc_self hs)
    have : 0 ≤ g s * q s := mul_nonneg h2 h1.le
    linarith)
  have qle1 : ∀ s ∈ Icc 0 T, q s ≤ 1 := fun s hs => q0 ▸ qanti hT0 hs hs.1
  have ple : ∀ s ∈ Icc 0 T, p s ≤ s := by
    have hA : AntitoneOn (fun s => p s - s) (Icc 0 T) :=
      antiIcc (cp.sub (by fun_prop)) (fun s hs => (hp s hs).sub (hasDerivAt_id' s))
        (fun s hs => by linarith [qle1 s (Ioo_subset_Icc_self hs)])
    intro s hs
    have := hA hT0 hs hs.1
    simp only [p0] at this
    linarith
  have gge : ∀ t ∈ Icc 0 T, t ^ 2 * q t / 2 ≤ g t := by
    intro t ht
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hIoo : ∀ s ∈ Ioo 0 t, s ∈ Ioo 0 T := fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
    have m1 : MonotoneOn (fun s => p s - s * q t) (Icc 0 t) :=
      monoIcc ((cp.mono hsub).sub (by fun_prop))
        (fun s hs => (hp s (hIoo s hs)).sub ((hasDerivAt_id' s).mul_const (q t)))
        (fun s hs => by
          have := qanti (Ioo_subset_Icc_self (hIoo s hs)) ht hs.2.le
          linarith)
    have p_ge : ∀ s ∈ Icc 0 t, s * q t ≤ p s := fun s hs => by
      have := m1 ⟨le_rfl, ht.1⟩ hs hs.1
      simp only [p0] at this
      linarith
    have m2 : MonotoneOn (fun s => g s - s ^ 2 * q t / 2) (Icc 0 t) :=
      monoIcc ((cg.mono hsub).sub (by fun_prop))
        (fun s hs => (hg s (hIoo s hs)).sub (((hasDerivAt_pow 2 s).mul_const (q t)).div_const 2))
        (fun s hs => by
          have := p_ge s (Ioo_subset_Icc_self hs)
          norm_num
          linarith)
    have := m2 ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
    norm_num [g0] at this
    linarith
  have rmono : MonotoneOn (fun s => (q s)⁻¹ - s ^ 3 / 12) (Icc 0 T) :=
    monoIcc ((cq.inv₀ (fun s hs => (qpos s hs).ne')).sub (by fun_prop))
      (fun s hs => ((hq s hs).inv (qpos s (Ioo_subset_Icc_self hs)).ne').sub
        ((hasDerivAt_pow 3 s).div_const 12))
      (fun s hs => by
        have hqs := qpos s (Ioo_subset_Icc_self hs)
        have hgs := gge s (Ioo_subset_Icc_self hs)
        have key : -(-(g s * q s / 2)) / q s ^ 2 - ((3 : ℕ) : ℝ) * s ^ (3 - 1) / 12 =
            (g s - s ^ 2 * q s / 2) / (2 * q s) := by
          norm_num
          field_simp
          ring
        rw [key]
        exact div_nonneg (by linarith) (by positivity))
  have q12 : ∀ s ∈ Icc 0 T, q s * s ^ 3 ≤ 12 := by
    intro s hs
    have h := rmono hT0 hs hs.1
    simp only [q0] at h
    norm_num at h
    have hqs := qpos s hs
    have h1 : 1 + s ^ 3 / 12 ≤ (q s)⁻¹ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hqs.le
    rw [mul_inv_cancel₀ hqs.ne'] at h2
    nlinarith
  by_cases hT52 : T ≤ 5 / 2
  · linarith [ple T ⟨hT, le_rfl⟩]
  · push Not at hT52
    have h52 : (5 / 2 : ℝ) ∈ Icc 0 T := ⟨by norm_num, hT52.le⟩
    have hsub : Icc (5 / 2 : ℝ) T ⊆ Icc 0 T := Icc_subset_Icc (by norm_num) le_rfl
    have W : AntitoneOn (fun s => p s + 6 / s ^ 2) (Icc (5 / 2) T) :=
      antiIcc ((cp.mono hsub).add (ContinuousOn.div continuousOn_const (by fun_prop)
          (fun s hs => by have : (0 : ℝ) < s := by linarith [hs.1]
                          positivity)))
        (fun s hs => (hp s ⟨by linarith [hs.1], hs.2⟩).add
          ((hasDerivAt_const s (6 : ℝ)).div (hasDerivAt_pow 2 s)
            (by have : (0 : ℝ) < s := by linarith [hs.1]
                positivity)))
        (fun s hs => by
          have hs0 : (0 : ℝ) < s := by linarith [hs.1]
          have h := q12 s ⟨hs0.le, hs.2.le⟩
          have key : q s + (0 * s ^ 2 - 6 * (((2 : ℕ) : ℝ) * s ^ (2 - 1))) / (s ^ 2) ^ 2 =
              (q s * s ^ 3 - 12) / s ^ 3 := by
            norm_num
            field_simp
            ring
          rw [key]
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    have hW := W ⟨le_rfl, hT52.le⟩ ⟨hT52.le, le_rfl⟩ hT52.le
    simp only at hW
    have h1 := ple (5 / 2) h52
    have h2 : 0 ≤ 6 / T ^ 2 := by positivity
    have e : (6 : ℝ) / (5 / 2) ^ 2 = 24 / 25 := by norm_num
    linarith

theorem inactive (Y : ℝ → ℝ × ℝ × ℝ) (h0 : Y 0 = (0, 0, 1))
    (hY : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (Work.Blasius.BExBase.vF t (Y t)) (Ici 0) t) :
    Work.Blasius.BTail.IsSol (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) ∧
    ∃ α : ℝ, 0 < α ∧ Tendsto (fun t => (Y t).2.1) atTop (𝓝 α) := by
  set g : ℝ → ℝ := fun t => (Y t).1 with hgdef
  set p : ℝ → ℝ := fun t => (Y t).2.1 with hpdef
  set q : ℝ → ℝ := fun t => (Y t).2.2 with hqdef
  have dg : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt g (cl 4 (p t)) (Ici 0) t :=
    fun t ht => fst_derivW (hY t ht)
  have dp : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q t)) (Ici 0) t :=
    fun t ht => fst_derivW (snd_derivW (hY t ht))
  have dq : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt q (-(cl (4 * max t 0 + 1) (g t) * cl 2 (q t) / 2)) (Ici 0) t :=
    fun t ht => snd_derivW (snd_derivW (hY t ht))
  have g0 : g 0 = 0 := by simp [hgdef, h0]
  have p0 : p 0 = 0 := by simp [hpdef, h0]
  have q0 : q 0 = 1 := by simp [hqdef, h0]
  have cg : ContinuousOn g (Ici 0) := fun t ht => (dg t ht).continuousWithinAt
  have cp : ContinuousOn p (Ici 0) := fun t ht => (dp t ht).continuousWithinAt
  have cq : ContinuousOn q (Ici 0) := fun t ht => (dq t ht).continuousWithinAt
  have mx : ∀ t : ℝ, 0 ≤ 4 * max t 0 + 1 := fun t => by
    have := le_max_right t 0; linarith
  -- q > 0
  have zb : ∀ t₁ : ℝ, 0 ≤ t₁ → q t₁ = 0 → q 0 = 0 := by
    intro t₁ ht₁ hz
    have h := ODE_solution_unique_of_mem_Icc_left
      (v := fun t y => -(cl (4 * max t 0 + 1) (g t) * cl 2 y / 2))
      (s := fun _ => univ) (K := Real.toNNReal ((4 * t₁ + 1) / 2)) (a := 0) (b := t₁) (f := q)
      (g := fun _ => 0)
      (fun t ht => lipcl ((cl_abs (mx t)).trans (by
        have := max_le ht.2 ht₁; linarith)))
      (cq.mono Icc_subset_Ici_self)
      (fun t ht => ((dq t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) continuousOn_const
      (fun t _ => by
        rw [show cl 2 (0 : ℝ) = 0 from cl_of_abs_le (by norm_num)]
        simp only [mul_zero, zero_div, neg_zero]
        exact hasDerivWithinAt_const _ _ _)
      (fun _ _ => mem_univ _) hz
    exact h ⟨le_rfl, ht₁⟩
  have qpos : ∀ t ∈ Ici (0 : ℝ), 0 < q t := by
    intro t ht
    by_contra hn
    push Not at hn
    obtain ⟨u, hu, hqu⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ t from ht)
      (cq.mono Icc_subset_Ici_self) (show (0 : ℝ) ∈ Icc (q t) (q 0) from ⟨hn, by rw [q0]; norm_num⟩)
    have := zb u hu.1 hqu
    rw [q0] at this
    norm_num at this
  -- monotonicity facts
  have pmono : MonotoneOn p (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => cl 2 (q t)) cp ?_ ?_
    · intro x hx; rw [interior_Ici] at hx ⊢
      exact ((dp x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx
      exact cl_nonneg (by norm_num) (qpos x (mem_Ici.2 (le_of_lt hx))).le
  have z0 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.2 le_rfl
  have pnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ p t := fun t ht => p0 ▸ pmono z0 ht ht
  have gmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => cl 4 (p t)) cg ?_ ?_
    · intro x hx; rw [interior_Ici] at hx ⊢
      exact ((dg x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx
      exact cl_nonneg (by norm_num) (pnn x (mem_Ici.2 (le_of_lt hx)))
  have gnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ g t := fun t ht => g0 ▸ gmono z0 ht ht
  have qanti : AntitoneOn q (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (f' := fun t => -(cl (4 * max t 0 + 1) (g t) * cl 2 (q t) / 2)) cq ?_ ?_
    · intro x hx; rw [interior_Ici] at hx ⊢
      exact ((dq x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx
      have h1 := cl_nonneg (mx x) (gnn x (mem_Ici.2 (le_of_lt hx)))
      have h2 := cl_nonneg (by norm_num : (0 : ℝ) ≤ 2) (qpos x (mem_Ici.2 (le_of_lt hx))).le
      have := mul_nonneg h1 h2
      linarith
  have qle1 : ∀ t ∈ Ici (0 : ℝ), q t ≤ 1 := fun t ht => q0 ▸ qanti z0 ht ht
  have gle : ∀ t ∈ Ici (0 : ℝ), g t ≤ 4 * t := by
    have hA : AntitoneOn (fun t => g t - 4 * t) (Ici 0) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
        (f' := fun t => cl 4 (p t) - 4 * 1) (cg.sub (by fun_prop)) ?_ ?_
      · intro x hx; rw [interior_Ici] at hx ⊢
        exact (((dg x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).sub
          ((hasDerivAt_id' x).const_mul 4)).hasDerivWithinAt
      · intro x hx
        have := cl_le (c := 4) (y := p x) (by norm_num)
        linarith
    intro t ht
    have := hA z0 ht ht
    simp only [g0] at this
    linarith
  have clq : ∀ t ∈ Ici (0 : ℝ), cl 2 (q t) = q t := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [qpos t ht], by linarith [qle1 t ht]⟩)
  have clg : ∀ t ∈ Ici (0 : ℝ), cl (4 * max t 0 + 1) (g t) = g t := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [gnn t ht, mx t], by
      have := gle t ht; have := le_max_left t 0; linarith⟩)
  -- the a-priori bound on [0, T] whenever p ≤ 4 there
  have pb : ∀ T ∈ Ici (0 : ℝ), (∀ s ∈ Icc 0 T, p s ≤ 4) → p T ≤ 173 / 50 := by
    intro T hT hp4
    have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := Icc_subset_Ici_self
    refine pbound hT (cg.mono hsub) (cp.mono hsub) (cq.mono hsub) (fun s hs => ?_) (fun s hs => ?_)
      (fun s hs => ?_) g0 p0 q0 (fun s hs => qpos s (hsub hs)) (fun s hs => gnn s (hsub hs))
    · have h := (dg s (le_of_lt hs.1)).hasDerivAt (Ici_mem_nhds hs.1)
      rwa [cl_of_abs_le (abs_le.2 ⟨by linarith [pnn s (mem_Ici.2 (le_of_lt hs.1))],
        hp4 s (Ioo_subset_Icc_self hs)⟩)] at h
    · have h := (dp s (le_of_lt hs.1)).hasDerivAt (Ici_mem_nhds hs.1)
      rwa [clq s (mem_Ici.2 (le_of_lt hs.1))] at h
    · have h := (dq s (le_of_lt hs.1)).hasDerivAt (Ici_mem_nhds hs.1)
      rwa [clq s (mem_Ici.2 (le_of_lt hs.1)), clg s (mem_Ici.2 (le_of_lt hs.1))] at h
  have plt : ∀ t ∈ Ici (0 : ℝ), p t < 4 := by
    intro t₁ ht₁
    by_contra hn
    push Not at hn
    obtain ⟨T, hT, hpT⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ t₁ from ht₁)
      (cp.mono Icc_subset_Ici_self) (show (4 : ℝ) ∈ Icc (p 0) (p t₁) from ⟨by rw [p0]; norm_num, hn⟩)
    have := pb T hT.1 (fun s hs => hpT ▸ pmono (mem_Ici.2 hs.1) (mem_Ici.2 hT.1) hs.2)
    linarith
  have clp : ∀ t ∈ Ici (0 : ℝ), cl 4 (p t) = p t := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [pnn t ht], (plt t ht).le⟩)
  have pball : ∀ t ∈ Ici (0 : ℝ), p t ≤ 173 / 50 := fun t ht =>
    pb t ht (fun s hs => (plt s (mem_Ici.2 hs.1)).le)
  refine ⟨⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩, ?_⟩
  · have h := dg η hη; rwa [clp η hη] at h
  · have h := dp η hη; rwa [clq η hη] at h
  · have h := dq η hη; rwa [clq η hη, clg η hη] at h
  · set pt : ℝ → ℝ := fun t => p (max t 0) with hpt
    have hmono : Monotone pt := fun a b hab =>
      pmono (mem_Ici.2 (le_max_right a 0)) (mem_Ici.2 (le_max_right b 0)) (max_le_max hab le_rfl)
    have hbdd : BddAbove (range pt) :=
      ⟨173 / 50, by rintro _ ⟨t, rfl⟩; exact pball (max t 0) (mem_Ici.2 (le_max_right _ _))⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    refine ⟨⨆ i, pt i, ?_, hlim.congr' ((eventually_ge_atTop 0).mono fun t ht => ?_)⟩
    · have hsm : StrictMonoOn p (Ici 0) := by
        refine strictMonoOn_of_deriv_pos (convex_Ici 0) cp (fun x hx => ?_)
        rw [interior_Ici] at hx
        rw [((dp x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).deriv]
        exact cl_pos (by norm_num) (qpos x (mem_Ici.2 (le_of_lt hx)))
      have h1 : p 0 < p 1 := hsm z0 (mem_Ici.2 (by norm_num)) (by norm_num)
      have h2 : pt 1 ≤ ⨆ i, pt i := le_ciSup hbdd 1
      have h3 : pt 1 = p 1 := by simp [hpt]
      linarith
    · simp [hpt, max_eq_left ht]

end Work.Blasius.BExBounds
