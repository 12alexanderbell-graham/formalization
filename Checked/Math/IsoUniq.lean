import Checked.Math.BEGlobalExists

/-! Isothermal sphere and radial Gelfand equation, `IsoUniq`: uniqueness of the regular solution of the singular initial-value problem w'' + (2/s) w' + e^w = 0 with given centre value, in the class of `Checked.Math.BEGlobalExists.exists_global` (w differentiable on [0, T] with derivative φ, φ continuous at the centre, the equation for s > 0; no value of φ at the centre assumed). Near the centre, with D the largest gap of the two solutions on a short interval [0, h], u = s²(φ₁ − φ₂) has derivative −s²(e^{w₁} − e^{w₂}), which bounds the gap of φ by a multiple of D h and the gap of w by a multiple of D h², so D vanishes when h is small; away from the centre the field is Lipschitz and Mathlib's `ODE_solution_unique_of_mem_Icc_right` applies. Promoted from `Work/Math/IsoUniq.lean` (run 2026-11-18T0428Z). -/

namespace Checked.Math.IsoUniq
open Set Filter Topology

/-- The field in (w, φ), Lipschitz in the half-plane w ≤ M for t ≥ h > 0. -/
theorem lipG {M h t : ℝ} (hh : 0 < h) (ht : h ≤ t) :
    LipschitzOnWith (Real.toNNReal (1 + 2 / h + Real.exp M))
      (Checked.Math.BEGlobalExists.G t) {p : ℝ × ℝ | p.1 ≤ M} := by
  have ht0 : 0 < t := lt_of_lt_of_le hh ht
  have h2h : 0 ≤ 2 / h := by positivity
  have hK : (0 : ℝ) ≤ 1 + 2 / h + Real.exp M := by positivity
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [Real.coe_toNNReal _ hK]
  simp only [Checked.Math.BEGlobalExists.G, Prod.dist_eq, Real.dist_eq]
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hm0 : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := (abs_nonneg _).trans hd1
  have hE := Real.exp_pos M
  refine max_le ?_ ?_
  · nlinarith
  · have e : -(2 / t * p.2) - Real.exp p.1 - (-(2 / t * q.2) - Real.exp q.1) =
        -(2 / t * (p.2 - q.2)) - (Real.exp p.1 - Real.exp q.1) := by ring
    rw [e]
    have h1 := Checked.Math.GExistsRight.exp_sub_le_of_le (m := M) hp hq
    have h2 : |2 / t * (p.2 - q.2)| ≤ 2 / h * |p.2 - q.2| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / t)]
      have : 2 / t ≤ 2 / h := div_le_div_of_nonneg_left (by norm_num) hh ht
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    calc |-(2 / t * (p.2 - q.2)) - (Real.exp p.1 - Real.exp q.1)|
        ≤ |2 / t * (p.2 - q.2)| + |Real.exp p.1 - Real.exp q.1| := by
          rw [sub_eq_add_neg]
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg, abs_neg]
      _ ≤ 2 / h * max |p.1 - q.1| |p.2 - q.2| + Real.exp M * max |p.1 - q.1| |p.2 - q.2| := by
          exact add_le_add (h2.trans (mul_le_mul_of_nonneg_left hd2 h2h))
            (h1.trans (mul_le_mul_of_nonneg_left hd1 hE.le))
      _ ≤ (1 + 2 / h + Real.exp M) * max |p.1 - q.1| |p.2 - q.2| := by nlinarith

/-- Uniqueness away from the centre, on [h, T]. -/
theorem uniq_right {h T : ℝ} (hh : 0 < h) {w1 φ1 w2 φ2 : ℝ → ℝ}
    (h1 : ∀ t ∈ Icc h T, HasDerivWithinAt w1 (φ1 t) (Icc h T) t ∧
        HasDerivWithinAt φ1 (-(2 / t * φ1 t) - Real.exp (w1 t)) (Icc h T) t)
    (h2 : ∀ t ∈ Icc h T, HasDerivWithinAt w2 (φ2 t) (Icc h T) t ∧
        HasDerivWithinAt φ2 (-(2 / t * φ2 t) - Real.exp (w2 t)) (Icc h T) t)
    (hw : w1 h = w2 h) (hφ : φ1 h = φ2 h) :
    ∀ t ∈ Icc h T, w1 t = w2 t ∧ φ1 t = φ2 t := by
  set f : ℝ → ℝ × ℝ := fun t => (w1 t, φ1 t) with hf
  set g : ℝ → ℝ × ℝ := fun t => (w2 t, φ2 t) with hg
  have df : ∀ t ∈ Icc h T, HasDerivWithinAt f (Checked.Math.BEGlobalExists.G t (f t)) (Icc h T) t :=
    fun t ht => (h1 t ht).1.prodMk (h1 t ht).2
  have dg : ∀ t ∈ Icc h T, HasDerivWithinAt g (Checked.Math.BEGlobalExists.G t (g t)) (Icc h T) t :=
    fun t ht => (h2 t ht).1.prodMk (h2 t ht).2
  have cf : ContinuousOn f (Icc h T) := fun t ht => (df t ht).continuousWithinAt
  have cg : ContinuousOn g (Icc h T) := fun t ht => (dg t ht).continuousWithinAt
  have c1 : ContinuousOn w1 (Icc h T) := fun t ht => (h1 t ht).1.continuousWithinAt
  have c2 : ContinuousOn w2 (Icc h T) := fun t ht => (h2 t ht).1.continuousWithinAt
  obtain ⟨M1, hM1⟩ := (isCompact_Icc.bddAbove_image c1)
  obtain ⟨M2, hM2⟩ := (isCompact_Icc.bddAbove_image c2)
  set M := max M1 M2
  have hv : ∀ t ∈ Ico h T,
      LipschitzOnWith (Real.toNNReal (1 + 2 / h + Real.exp M)) (Checked.Math.BEGlobalExists.G t)
        {p : ℝ × ℝ | p.1 ≤ M} :=
    fun t ht => lipG hh ht.1
  have toIci : ∀ {F : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {t : ℝ}, t ∈ Ico h T →
      HasDerivWithinAt F d (Icc h T) t → HasDerivWithinAt F d (Ici t) t := by
    intro F d t ht hd
    refine hd.mono_of_mem_nhdsWithin (mem_nhdsWithin.2 ⟨Iio T, isOpen_Iio, ht.2, ?_⟩)
    intro y hy; exact ⟨le_trans ht.1 hy.2, le_of_lt hy.1⟩
  have e := ODE_solution_unique_of_mem_Icc_right (v := Checked.Math.BEGlobalExists.G)
    (s := fun _ => {p : ℝ × ℝ | p.1 ≤ M})
    (f := f) (g := g) (a := h) (b := T) hv cf
    (fun t ht => toIci ht (df t (Ico_subset_Icc_self ht)))
    (fun t ht => le_trans (hM1 ⟨t, Ico_subset_Icc_self ht, rfl⟩) (le_max_left _ _)) cg
    (fun t ht => toIci ht (dg t (Ico_subset_Icc_self ht)))
    (fun t ht => le_trans (hM2 ⟨t, Ico_subset_Icc_self ht, rfl⟩) (le_max_right _ _))
    (by simp only [hf, hg, hw, hφ])
  intro t ht
  have := e ht
  simp only [hf, hg, Prod.mk.injEq] at this
  exact this

/-- Uniqueness of the regular solution on [0, T], T > 0: two solutions with the same value at the centre
agree on [0, T], derivatives included. -/
theorem uniq_Icc {T : ℝ} (hT : 0 < T) {w1 φ1 w2 φ2 : ℝ → ℝ}
    (hw1 : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt w1 (φ1 s) (Icc 0 T) s)
    (hc1 : ContinuousWithinAt φ1 (Icc 0 T) 0)
    (hφ1 : ∀ s ∈ Ioc (0 : ℝ) T,
      HasDerivWithinAt φ1 (-(2 / s * φ1 s) - Real.exp (w1 s)) (Icc 0 T) s)
    (hw2 : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt w2 (φ2 s) (Icc 0 T) s)
    (hc2 : ContinuousWithinAt φ2 (Icc 0 T) 0)
    (hφ2 : ∀ s ∈ Ioc (0 : ℝ) T,
      HasDerivWithinAt φ2 (-(2 / s * φ2 s) - Real.exp (w2 s)) (Icc 0 T) s)
    (h0 : w1 0 = w2 0) :
    ∀ s ∈ Icc (0 : ℝ) T, w1 s = w2 s ∧ φ1 s = φ2 s := by
  -- bounds
  have cw1 : ContinuousOn w1 (Icc 0 T) := fun t ht => (hw1 t ht).continuousWithinAt
  have cw2 : ContinuousOn w2 (Icc 0 T) := fun t ht => (hw2 t ht).continuousWithinAt
  obtain ⟨M1, hM1⟩ := isCompact_Icc.bddAbove_image cw1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.bddAbove_image cw2
  set M := max M1 M2 with hMdef
  have bw1 : ∀ t ∈ Icc (0 : ℝ) T, w1 t ≤ M := fun t ht =>
    le_trans (hM1 ⟨t, ht, rfl⟩) (le_max_left _ _)
  have bw2 : ∀ t ∈ Icc (0 : ℝ) T, w2 t ≤ M := fun t ht =>
    le_trans (hM2 ⟨t, ht, rfl⟩) (le_max_right _ _)
  set L := Real.exp M with hL
  have hL0 : 0 < L := Real.exp_pos M
  set h := min T (1 / (L + 1)) with hhdef
  have hh0 : 0 < h := lt_min hT (by positivity)
  have hhT : h ≤ T := min_le_left _ _
  have hhL : h ≤ 1 / (L + 1) := min_le_right _ _
  have hLh : L * h ^ 2 < 1 := by
    have h1 : h * (L + 1) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hhL; exact hhL
    have h2 : h ≤ 1 := by nlinarith
    nlinarith
  have sub : Icc (0 : ℝ) h ⊆ Icc 0 T := Icc_subset_Icc le_rfl hhT
  -- the largest gap on [0, h]
  set dw : ℝ → ℝ := fun t => w1 t - w2 t with hdw
  set dφ : ℝ → ℝ := fun t => φ1 t - φ2 t with hdφ
  have cdw : ContinuousOn dw (Icc 0 h) := (cw1.mono sub).sub (cw2.mono sub)
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hh0.le) cdw.abs
  set D := |dw s0| with hD
  have hD0 : 0 ≤ D := abs_nonneg _
  have gap : ∀ t ∈ Icc (0 : ℝ) h, |dw t| ≤ D := fun t ht => hmax ht
  -- derivative facts on the open interval (0, h)
  have ddw : ∀ t ∈ Ioo (0 : ℝ) h, HasDerivWithinAt dw (dφ t) (Ioo 0 h) t := fun t ht =>
    ((hw1 t (sub (Ioo_subset_Icc_self ht))).sub (hw2 t (sub (Ioo_subset_Icc_self ht)))).mono
      (Ioo_subset_Icc_self.trans sub)
  have ddφ : ∀ t ∈ Ioo (0 : ℝ) h, HasDerivWithinAt dφ
      ((-(2 / t * φ1 t) - Real.exp (w1 t)) - (-(2 / t * φ2 t) - Real.exp (w2 t))) (Ioo 0 h) t :=
    fun t ht => ((hφ1 t ⟨ht.1, ht.2.le.trans hhT⟩).sub (hφ2 t ⟨ht.1, ht.2.le.trans hhT⟩)).mono
      (Ioo_subset_Icc_self.trans sub)
  -- continuity of dφ on [0, h]
  have cdφ : ContinuousOn dφ (Icc 0 h) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0t | h0t
    · subst h0t
      exact (hc1.sub hc2).mono sub
    · exact (((hφ1 t ⟨h0t, ht.2.trans hhT⟩).sub
        (hφ2 t ⟨h0t, ht.2.trans hhT⟩)).continuousWithinAt).mono sub
  -- u = t² dφ
  set u : ℝ → ℝ := fun t => t ^ 2 * dφ t with hu
  have cu : ContinuousOn u (Icc 0 h) := (continuousOn_id.pow 2).mul cdφ
  have du : ∀ t ∈ Ioo (0 : ℝ) h,
      HasDerivWithinAt u (-(t ^ 2 * (Real.exp (w1 t) - Real.exp (w2 t)))) (Ioo 0 h) t := by
    intro t ht
    have hd := ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := Ioo 0 h)).mul (ddφ t ht)
    convert hd using 1
    have : t ≠ 0 := ht.1.ne'
    simp only [hdφ]
    field_simp
    ring
  have bu : ∀ t ∈ Ioo (0 : ℝ) h, |t ^ 2 * (Real.exp (w1 t) - Real.exp (w2 t))| ≤ L * D * t ^ 2 := by
    intro t ht
    have htT : t ∈ Icc (0 : ℝ) T := sub (Ioo_subset_Icc_self ht)
    have e1 := Checked.Math.GExistsRight.exp_sub_le_of_le (bw1 t htT) (bw2 t htT)
    have g1 := gap t (Ioo_subset_Icc_self ht)
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    have : |Real.exp (w1 t) - Real.exp (w2 t)| ≤ L * D :=
      e1.trans (mul_le_mul_of_nonneg_left g1 hL0.le)
    nlinarith [sq_nonneg t]
  -- |u t| ≤ L D t³/3 on [0, h]
  have uB : ∀ t ∈ Icc (0 : ℝ) h, |u t| ≤ L * D * t ^ 3 / 3 := by
    have mono : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
        MonotoneOn (fun t => L * D * t ^ 3 / 3 + σ * u t) (Icc 0 h) := by
      intro σ hσ
      have hσ1 : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 h)
        (f' := fun t => L * D * t ^ 2 + σ * (-(t ^ 2 * (Real.exp (w1 t) - Real.exp (w2 t)))))
      · exact ((continuousOn_const.mul (continuousOn_id.pow 3)).div_const 3).add
          (continuousOn_const.mul cu)
      · intro t ht
        rw [interior_Icc] at ht
        have h3 : HasDerivWithinAt (fun t : ℝ => L * D * t ^ 3 / 3) (L * D * t ^ 2) (Ioo 0 h) t := by
          have := (((hasDerivAt_pow 3 t).const_mul (L * D)).div_const 3).hasDerivWithinAt
            (s := Ioo 0 h)
          convert this using 1
          push_cast; ring
        rw [interior_Icc]
        exact h3.add ((du t ht).const_mul σ)
      · intro t ht
        rw [interior_Icc] at ht
        have b := bu t ht
        have : |σ * (-(t ^ 2 * (Real.exp (w1 t) - Real.exp (w2 t))))| ≤ L * D * t ^ 2 := by
          rw [abs_mul, hσ1, one_mul, abs_neg]; exact b
        have := neg_abs_le (σ * (-(t ^ 2 * (Real.exp (w1 t) - Real.exp (w2 t)))))
        linarith
    intro t ht
    have h0I : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, hh0.le⟩
    have u0 : u 0 = 0 := by simp [hu]
    have m1 := mono 1 (Or.inl rfl) h0I ht ht.1
    have m2 := mono (-1) (Or.inr rfl) h0I ht ht.1
    simp only [u0, mul_zero, add_zero] at m1 m2
    norm_num at m1 m2
    rw [abs_le]
    constructor <;> nlinarith
  -- |dφ t| ≤ L D h on (0, h)
  have φB : ∀ t ∈ Ioo (0 : ℝ) h, |dφ t| ≤ L * D * h := by
    intro t ht
    have b := uB t (Ioo_subset_Icc_self ht)
    have ht2 : 0 < t ^ 2 := by have := ht.1; positivity
    have e : |u t| = t ^ 2 * |dφ t| := by
      simp only [hu]; rw [abs_mul, abs_of_pos ht2]
    rw [e] at b
    have : t ^ 2 * |dφ t| ≤ t ^ 2 * (L * D * h) := by
      have hLD : 0 ≤ L * D := mul_nonneg hL0.le hD0
      have : L * D * t ^ 3 / 3 ≤ t ^ 2 * (L * D * h) := by
        have e3 : L * D * t ^ 3 / 3 = (L * D * t ^ 2) * t / 3 := by ring
        have m := mul_le_mul_of_nonneg_left ht.2.le (mul_nonneg hLD ht2.le)
        have p0 : 0 ≤ (L * D * t ^ 2) * t := mul_nonneg (mul_nonneg hLD ht2.le) ht.1.le
        rw [e3]
        have e4 : t ^ 2 * (L * D * h) = (L * D * t ^ 2) * h := by ring
        rw [e4]
        linarith
      linarith
    exact le_of_mul_le_mul_left this ht2
  -- |dw t| ≤ L D h · t ≤ L D h² on [0, h]
  have wB : ∀ t ∈ Icc (0 : ℝ) h, |dw t| ≤ L * D * h * t := by
    have mono : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
        MonotoneOn (fun t => L * D * h * t + σ * dw t) (Icc 0 h) := by
      intro σ hσ
      have hσ1 : |σ| = 1 := by rcases hσ with h | h <;> simp [h]
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 h)
        (f' := fun t => L * D * h + σ * dφ t)
      · exact (continuousOn_const.mul continuousOn_id).add (continuousOn_const.mul cdw)
      · intro t ht
        rw [interior_Icc] at ht
        rw [interior_Icc]
        have h1 : HasDerivWithinAt (fun t : ℝ => L * D * h * t) (L * D * h) (Ioo 0 h) t := by
          have := ((hasDerivAt_id t).const_mul (L * D * h)).hasDerivWithinAt (s := Ioo 0 h)
          simpa using this
        exact h1.add ((ddw t ht).const_mul σ)
      · intro t ht
        rw [interior_Icc] at ht
        have b := φB t ht
        have : |σ * dφ t| ≤ L * D * h := by rw [abs_mul, hσ1, one_mul]; exact b
        have := neg_abs_le (σ * dφ t)
        linarith
    intro t ht
    have h0I : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, hh0.le⟩
    have d0 : dw 0 = 0 := by simp [hdw, h0]
    have m1 := mono 1 (Or.inl rfl) h0I ht ht.1
    have m2 := mono (-1) (Or.inr rfl) h0I ht ht.1
    simp only [d0, mul_zero, add_zero] at m1 m2
    rw [abs_le]
    constructor <;> nlinarith
  -- D = 0
  have hDz : D = 0 := by
    have b := wB s0 hs0
    have : L * D * h * s0 ≤ L * h ^ 2 * D := by
      have hLD : 0 ≤ L * D * h := by positivity
      have := mul_le_mul_of_nonneg_left hs0.2 hLD
      nlinarith
    have hDle : D ≤ L * h ^ 2 * D := le_trans b this
    by_contra hne
    have hpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hne)
    nlinarith
  have wz : ∀ t ∈ Icc (0 : ℝ) h, w1 t = w2 t := fun t ht => by
    have := gap t ht
    rw [hDz] at this
    have : dw t = 0 := abs_nonpos_iff.1 this
    simp only [hdw] at this; linarith
  have φz : ∀ t ∈ Ioo (0 : ℝ) h, φ1 t = φ2 t := fun t ht => by
    have := φB t ht
    rw [hDz, mul_zero, zero_mul] at this
    have : dφ t = 0 := abs_nonpos_iff.1 this
    simp only [hdφ] at this; linarith
  -- at the centre, by continuity
  have φz0 : φ1 0 = φ2 0 := by
    have hc : ContinuousWithinAt dφ (Ioo 0 h) 0 :=
      (cdφ 0 ⟨le_rfl, hh0.le⟩).mono Ioo_subset_Icc_self
    have hm : Ioo (0 : ℝ) h ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hh0
    have t1 : Tendsto dφ (𝓝[>] 0) (𝓝 (dφ 0)) :=
      (hc.mono_of_mem_nhdsWithin (by simpa using hm)) |>.tendsto
    have t2 : Tendsto dφ (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hm] with t ht
      simp only [hdφ, φz t ht, sub_self]
    have := tendsto_nhds_unique t1 t2
    simp only [hdφ] at this; linarith
  -- at h, by continuity from the left
  have φzh : φ1 h = φ2 h := by
    have hc : ContinuousWithinAt dφ (Ioo 0 h) h :=
      (cdφ h ⟨hh0.le, le_rfl⟩).mono Ioo_subset_Icc_self
    have hm : Ioo (0 : ℝ) h ∈ 𝓝[<] h := Ioo_mem_nhdsLT hh0
    have t1 : Tendsto dφ (𝓝[<] h) (𝓝 (dφ h)) :=
      (hc.mono_of_mem_nhdsWithin (by simpa using hm)) |>.tendsto
    have t2 : Tendsto dφ (𝓝[<] h) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hm] with t ht
      simp only [hdφ, φz t ht, sub_self]
    have := tendsto_nhds_unique t1 t2
    simp only [hdφ] at this; linarith
  -- the right part
  have subR : Icc h T ⊆ Icc 0 T := Icc_subset_Icc hh0.le le_rfl
  have right := uniq_right (T := T) hh0
    (fun t ht => ⟨(hw1 t (subR ht)).mono subR,
      (hφ1 t ⟨lt_of_lt_of_le hh0 ht.1, ht.2⟩).mono subR⟩)
    (fun t ht => ⟨(hw2 t (subR ht)).mono subR,
      (hφ2 t ⟨lt_of_lt_of_le hh0 ht.1, ht.2⟩).mono subR⟩)
    (wz h ⟨hh0.le, le_rfl⟩) φzh
  intro s hs
  rcases le_or_gt s h with hsh | hsh
  · refine ⟨wz s ⟨hs.1, hsh⟩, ?_⟩
    rcases eq_or_lt_of_le hs.1 with h0s | h0s
    · rw [← h0s]; exact φz0
    · rcases eq_or_lt_of_le hsh with hse | hse
      · rw [hse]; exact φzh
      · exact φz s ⟨h0s, hse⟩
  · exact right s ⟨hsh.le, hs.2⟩

/-- Uniqueness of the regular solution on the half-line, in the class of
`Checked.Math.BEGlobalExists.exists_global`. -/
theorem uniq_global {w1 φ1 w2 φ2 : ℝ → ℝ}
    (hw1 : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w1 (φ1 s) (Ici 0) s)
    (hc1 : ContinuousWithinAt φ1 (Ici 0) 0)
    (hφ1 : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt φ1 (-(2 / s * φ1 s) - Real.exp (w1 s)) (Ici 0) s)
    (hw2 : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w2 (φ2 s) (Ici 0) s)
    (hc2 : ContinuousWithinAt φ2 (Ici 0) 0)
    (hφ2 : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt φ2 (-(2 / s * φ2 s) - Real.exp (w2 s)) (Ici 0) s)
    (h0 : w1 0 = w2 0) :
    ∀ s, 0 ≤ s → w1 s = w2 s ∧ φ1 s = φ2 s := by
  intro s hs
  have hT : (0 : ℝ) < s + 1 := by linarith
  exact uniq_Icc hT (fun t ht => (hw1 t ht.1).mono Icc_subset_Ici_self) (hc1.mono Icc_subset_Ici_self)
    (fun t ht => (hφ1 t ht.1).mono Icc_subset_Ici_self)
    (fun t ht => (hw2 t ht.1).mono Icc_subset_Ici_self) (hc2.mono Icc_subset_Ici_self)
    (fun t ht => (hφ2 t ht.1).mono Icc_subset_Ici_self) h0 s ⟨hs, by linarith⟩

end Checked.Math.IsoUniq
