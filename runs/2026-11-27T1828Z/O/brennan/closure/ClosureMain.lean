import Readings.brennan
import ComparatorChallenges.Brennan

/-!
# Target O, family O64 (Brennan paper, main theorem): closure of readings A, B, C

Against OpenAI's frozen `OAI.Brennan.main_theorem : MainStatement` (used only through `type_of%`):

* Reader A (four separate theorems) and reader B (one conjunction): every conjunct is proved
  equivalent to the corresponding frozen conjunct. The uniform bound differs by `one_div` (A) and by
  `neg_add'` (B); the spectra are suprema over the schlicht class written as `iSup` over membership,
  equal to the frozen `sSup` of the set of exponents. Reader A's domain form is a lower integral of
  the `NNReal` norm power, equal to the integrability of the frozen real power (positive exponent,
  measurable derivative). Reader A's disk form is a lower integral of an `ENNReal` power whose
  exponent may be negative, where a zero of the derivative would give infinity; the derivative of an
  injective holomorphic map on the disk vanishes only on a codiscrete-complement set, hence almost
  nowhere, so the two agree. Reader B's boundary hypothesis `2 ≤ encard` is `Nontrivial`.
* Reader C: the uniform bound, domain form and disk form are equivalent conjunct by conjunct (with
  reassociated class membership, two explicit boundary points, and swapped or curried hypotheses).
  Reader C's spectrum uses a real `limsup` (junk value zero when not cobounded below) and a real
  `sSup`. The comparison with the frozen extended-real spectrum is made in the presence of the uniform
  bound (a conjunct on both sides): it makes every ratio eventually at most one plus any positive
  margin, so every real and every extended-real exponent is at most one, and a real exponent above a
  positive level is a genuine `limsup`. With it, reader C's real spectrum value equals one exactly when
  the frozen one does. Hence reader C's whole main theorem is equivalent to the frozen statement.
-/

namespace TargetO.BrennanMain

open OAI.Brennan MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ## Class, means, exponents, spectra -/

theorem A_Schlicht_iff (f : ℂ → ℂ) : f ∈ ReaderA.Schlicht ↔ Schlicht f := Iff.rfl

theorem B_Schlicht_iff (f : ℂ → ℂ) : f ∈ ReaderB.SSS ↔ Schlicht f := Iff.rfl

theorem C_Schlicht_iff (f : ℂ → ℂ) : f ∈ ReaderC.schlicht ↔ Schlicht f :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩, fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩⟩

theorem A_Mt_eq (t : ℝ) (f : ℂ → ℂ) (r : ℝ) : ReaderA.Mt t f r = integralMean f t r := by
  simp only [ReaderA.Mt, integralMean, one_div]

theorem B_M_eq (t : ℝ) (f : ℂ → ℂ) (r : ℝ) : ReaderB.M t f r = integralMean f t r := by
  simp only [ReaderB.M, integralMean, one_div]

theorem C_M_eq (f : ℂ → ℂ) (t r : ℝ) : ReaderC.meanMt f t r = integralMean f t r := by
  simp only [ReaderC.meanMt, integralMean, one_div]

theorem A_beta_eq (f : ℂ → ℂ) (t : ℝ) : ReaderA.betaF f t = beta f t := by
  simp only [ReaderA.betaF, beta, A_Mt_eq]

theorem B_beta_eq (f : ℂ → ℂ) (t : ℝ) : ReaderB.beta f t = beta f t := by
  simp only [ReaderB.beta, beta, B_M_eq]

theorem spectrum_eq_iSup (t : ℝ) : spectrum t = ⨆ f ∈ {f | Schlicht f}, beta f t := by
  rw [← sSup_image]; rfl

theorem A_BS_eq (t : ℝ) : ReaderA.BS t = spectrum t := by
  rw [spectrum_eq_iSup]; unfold ReaderA.BS
  exact iSup_congr fun f => iSup_congr_Prop (A_Schlicht_iff f) fun _ => A_beta_eq f t

theorem B_BS_eq (t : ℝ) : ReaderB.BS t = spectrum t := by
  rw [spectrum_eq_iSup]; unfold ReaderB.BS
  exact iSup_congr fun f => iSup_congr_Prop (B_Schlicht_iff f) fun _ => B_beta_eq f t

/-! ## Lower integrals of norm powers -/

theorem ofReal_rpow_norm_of_nonneg (x : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (‖x‖ ^ s) = (‖x‖₊ : ℝ≥0∞) ^ s := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

theorem ofReal_rpow_norm_of_ne (x : ℂ) (hx : x ≠ 0) (s : ℝ) :
    ENNReal.ofReal (‖x‖ ^ s) = (‖x‖₊ : ℝ≥0∞) ^ s := by
  rw [← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hx), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

/-- Integrability of a real norm power is finiteness of the lower integral of the `NNReal` norm
power, when the exponent is nonnegative or the base vanishes almost nowhere. -/
theorem integrableOn_iff_lintegral (g : ℂ → ℂ) (hg : Measurable g) (U : Set ℂ) (s : ℝ)
    (h : 0 ≤ s ∨ ∀ᵐ z ∂(volume.restrict U), g z ≠ 0) :
    IntegrableOn (fun z => ‖g z‖ ^ s) U volume ↔ ∫⁻ z in U, (‖g z‖₊ : ℝ≥0∞) ^ s < ∞ := by
  have hm : AEStronglyMeasurable (fun z => ‖g z‖ ^ s) (volume.restrict U) :=
    (hg.norm.pow_const s).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict U] fun z => ‖g z‖ ^ s :=
    ae_of_all _ fun z => Real.rpow_nonneg (norm_nonneg _) _
  have heq : (fun z => ENNReal.ofReal (‖g z‖ ^ s)) =ᵐ[volume.restrict U]
      fun z => (‖g z‖₊ : ℝ≥0∞) ^ s := by
    rcases h with hs | h
    · exact ae_of_all _ fun z => ofReal_rpow_norm_of_nonneg _ hs
    · filter_upwards [h] with z hz using ofReal_rpow_norm_of_ne _ hz s
  rw [← lintegral_congr_ae heq]
  exact ⟨fun hi => (hasFiniteIntegral_iff_ofReal hnn).1 hi.2,
    fun hl => ⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 hl⟩⟩

/-- The derivative of an injective holomorphic map on the disk vanishes almost nowhere there. -/
theorem ae_deriv_ne_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk) (hinj : InjOn f disk) :
    ∀ᵐ z ∂(volume.restrict disk), deriv f z ≠ 0 := by
  have hopen : IsOpen disk := Metric.isOpen_ball
  have han : AnalyticOnNhd ℂ f disk := hf.analyticOnNhd hopen
  have hconn : IsConnected disk :=
    (convex_ball (0 : ℂ) 1).isConnected (Metric.nonempty_ball.2 one_pos)
  have h0 : (0 : ℂ) ∈ disk := Metric.mem_ball_self one_pos
  have h1 : ((1 / 2 : ℝ) : ℂ) ∈ disk := by
    show _ ∈ Metric.ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; norm_num
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ disk, deriv f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hopen.is_const_of_deriv_eq_zero hconn.isPreconnected hf (fun z hz => hcon z hz) h0 h1
    have h01 := hinj h0 h1 this
    have : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; norm_num
    exact this h01.symm
  have hcd := han.deriv.preimage_zero_mem_codiscreteWithin hx0 hx hconn
  exact ae_restrict_le_codiscreteWithin hopen.measurableSet hcd

/-- `2 ≤ encard` is nontriviality. -/
theorem two_le_encard_iff {α : Type*} (s : Set α) : 2 ≤ s.encard ↔ s.Nontrivial := by
  rw [← Set.one_lt_encard_iff_nontrivial, show (2 : ℕ∞) = 1 + 1 by norm_num]
  exact ENat.add_one_le_iff ENat.one_ne_top

/-! ## Readers A and B: conjunct by conjunct -/

/-- Reader A's four assertions are, conjunct by conjunct, the frozen statement. -/
theorem closure_A :
    type_of% @OAI.Brennan.main_theorem ↔
      (type_of% @ReaderA.reading_thm_1_1_uniform) ∧ (type_of% @ReaderA.reading_thm_1_1_BS) ∧
      (type_of% @ReaderA.reading_thm_1_1_domain) ∧ (type_of% @ReaderA.reading_thm_1_1_disk) := by
  unfold MainStatement
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · simp only [A_Mt_eq]; exact Iff.rfl
  · rw [A_BS_eq]
  · constructor
    · intro h W hWo hWc hWsc hb φ hφ hbij s hs1 hs2
      exact (integrableOn_iff_lintegral (deriv φ) (measurable_deriv φ) W s
        (Or.inl (by linarith))).1 (h W hWo hWc hWsc hb φ hφ hbij s hs1 hs2)
    · intro h W hWo hWc hWsc hb φ hφ hbij s hs1 hs2
      exact (integrableOn_iff_lintegral (deriv φ) (measurable_deriv φ) W s
        (Or.inl (by linarith))).2 (h W hWo hWc hWsc hb φ hφ hbij s hs1 hs2)
  · constructor
    · intro h f hf t ht1 ht2
      exact (integrableOn_iff_lintegral (deriv f) (measurable_deriv f) disk t
        (Or.inr (ae_deriv_ne_zero hf.1 hf.2))).1 (h f hf t ht1 ht2)
    · intro h f hf t ht1 ht2
      exact (integrableOn_iff_lintegral (deriv f) (measurable_deriv f) disk t
        (Or.inr (ae_deriv_ne_zero hf.1 hf.2))).2 (h f hf t ht1 ht2)

/-- Reader B's main theorem is, conjunct by conjunct, the frozen statement. -/
theorem closure_B :
    type_of% @OAI.Brennan.main_theorem ↔ type_of% @ReaderB.readingBrennan := by
  unfold MainStatement
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl))
  · simp only [B_M_eq, neg_add']; exact Iff.rfl
  · rw [B_BS_eq]
  · simp only [two_le_encard_iff]; exact Iff.rfl

/-! ## Reader C -/

theorem mean_nonneg (f : ℂ → ℂ) (t r : ℝ) : 0 ≤ integralMean f t r := by
  unfold integralMean
  refine mul_nonneg (inv_nonneg.2 (by positivity)) ?_
  refine intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ => ?_
  exact Real.rpow_nonneg (norm_nonneg _) _

/-- The uniform bound with margin `ε` makes the ratio eventually at most one plus twice `ε`. -/
theorem eventually_ratio_le {f : ℂ → ℂ} {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε)) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ),
      Real.log (integralMean f (-2) r) / Real.log (1 / (1 - r)) ≤ 1 + 2 * ε := by
  set K := max 1 (|Real.log C| / ε) with hKdef
  have hmem : Set.Ioo (max (1 / 2) (1 - Real.exp (-K))) 1 ∈ 𝓝[<] (1 : ℝ) :=
    Ioo_mem_nhdsLT (max_lt (by norm_num) (by linarith [Real.exp_pos (-K)]))
  filter_upwards [hmem] with r hr
  obtain ⟨hr1, hr2⟩ := hr
  have hr12 : 1 / 2 ≤ r := (le_max_left _ _).trans hr1.le
  have hrK : 1 - Real.exp (-K) < r := lt_of_le_of_lt (le_max_right _ _) hr1
  have h1r : 0 < 1 - r := by linarith
  have hL : Real.log (1 / (1 - r)) = -Real.log (1 - r) := by rw [one_div, Real.log_inv]
  have hLK : K ≤ -Real.log (1 - r) := by
    rw [le_neg, Real.log_le_iff_le_exp h1r]; linarith
  have hK1 : 1 ≤ K := le_max_left _ _
  have hLpos : 0 < Real.log (1 / (1 - r)) := by rw [hL]; linarith
  rw [div_le_iff₀ hLpos]
  rcases (mean_nonneg f (-2) r).eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]; exact mul_nonneg (by linarith) hLpos.le
  · have hbd := hb r hr12 hr2
    have hp : 0 < (1 - r) ^ (-1 - ε) := Real.rpow_pos_of_pos h1r _
    have hC : 0 < C := by
      by_contra hC; push Not at hC
      have : C * (1 - r) ^ (-1 - ε) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC hp.le
      linarith
    have hlog : Real.log (integralMean f (-2) r) ≤ Real.log C + (-1 - ε) * Real.log (1 - r) := by
      calc Real.log (integralMean f (-2) r) ≤ Real.log (C * (1 - r) ^ (-1 - ε)) :=
            Real.log_le_log hpos hbd
        _ = _ := by rw [Real.log_mul hC.ne' hp.ne', Real.log_rpow h1r]
    have hCK : Real.log C ≤ ε * -Real.log (1 - r) := by
      have : |Real.log C| / ε ≤ -Real.log (1 - r) := (le_max_right _ _).trans hLK
      rw [div_le_iff₀ hε] at this
      linarith [le_abs_self (Real.log C)]
    rw [hL]
    nlinarith

/-- The uniform inverse-square bound for one map, with every positive margin. -/
def UniformBound (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
    integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε)

/-- The ratio whose `limsup` is the exponent at the inverse-square power. -/
noncomputable def ratio (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.log (integralMean f (-2) r) / Real.log (1 / (1 - r))

theorem ev_of_bound {f : ℂ → ℂ} (hb : UniformBound f) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), ratio f r ≤ 1 + δ := by
  obtain ⟨C, hC⟩ := hb (δ / 2) (by linarith)
  have := eventually_ratio_le (f := f) (C := C) (ε := δ / 2) (by linarith) hC
  filter_upwards [this] with r hr
  unfold ratio; linarith

theorem beta_eq (f : ℂ → ℂ) :
    beta f (-2) = limsup (fun r => (ratio f r : EReal)) (𝓝[<] (1 : ℝ)) := rfl

theorem C_betaExp_eq (f : ℂ → ℂ) : ReaderC.betaExp f (-2) = limsup (ratio f) (𝓝[<] (1 : ℝ)) := by
  simp only [ReaderC.betaExp, C_M_eq]; rfl

/-- A real `limsup` (junk value zero when not cobounded) is at most one when the function is
eventually at most `1 + δ` for every positive `δ`. -/
theorem real_limsup_le_one {u : ℝ → ℝ} {F : Filter ℝ}
    (hev : ∀ δ : ℝ, 0 < δ → ∀ᶠ x in F, u x ≤ 1 + δ) : limsup u F ≤ 1 := by
  by_cases hcb : IsCoboundedUnder (· ≤ ·) F u
  · exact le_of_forall_pos_le_add fun δ hδ => limsup_le_of_le hcb (hev δ hδ)
  · rw [limsup_eq, Real.sInf_of_not_bddBelow (s := {a | ∀ᶠ n in F, u n ≤ a}) (fun hb => hcb hb)]
    norm_num

theorem ereal_limsup_le_one {u : ℝ → ℝ} {F : Filter ℝ}
    (hev : ∀ δ : ℝ, 0 < δ → ∀ᶠ x in F, u x ≤ 1 + δ) :
    limsup (fun x => (u x : EReal)) F ≤ 1 := by
  by_contra hlt; push Not at hlt
  obtain ⟨y, h1y, hy⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have h1y' : (1 : ℝ) < y := by exact_mod_cast h1y
  have hle : limsup (fun x => (u x : EReal)) F ≤ ((1 + (y - 1) / 2 : ℝ) : EReal) :=
    limsup_le_of_le (h := (hev _ (by linarith)).mono fun x hx => EReal.coe_le_coe_iff.2 hx)
  have : ((1 + (y - 1) / 2 : ℝ) : EReal) < y := EReal.coe_lt_coe_iff.2 (by linarith)
  exact absurd (hle.trans_lt this) (not_lt.2 hy.le)

theorem le_real_limsup {u : ℝ → ℝ} {F : Filter ℝ} {b c : ℝ}
    (hb : (b : EReal) < limsup (fun x => (u x : EReal)) F) (hbd : ∀ᶠ x in F, u x ≤ c) :
    b ≤ limsup u F := by
  have hfr : ∃ᶠ x in F, (b : EReal) < (u x : EReal) := frequently_lt_of_lt_limsup (h := hb)
  exact le_limsup_of_frequently_le (hfr.mono fun x hx => (EReal.coe_lt_coe_iff.1 hx).le)
    (isBoundedUnder_of_eventually_le hbd)

theorem le_ereal_limsup {u : ℝ → ℝ} {F : Filter ℝ} {b : ℝ} (hb0 : 0 < b) (hb : b < limsup u F) :
    (b : EReal) ≤ limsup (fun x => (u x : EReal)) F := by
  have hcb : IsCoboundedUnder (· ≤ ·) F u := by
    by_contra hcb
    rw [limsup_eq, Real.sInf_of_not_bddBelow (s := {a | ∀ᶠ n in F, u n ≤ a}) (fun h => hcb h)] at hb
    linarith
  have hfr := frequently_lt_of_lt_limsup hcb hb
  exact le_limsup_of_frequently_le (hfr.mono fun x hx => EReal.coe_le_coe_iff.2 hx.le)

theorem id_schlicht : Schlicht id := ⟨⟨differentiableOn_id, injOn_id _⟩, rfl, deriv_id 0⟩

theorem C_betaExp_le_one (hb : ∀ f, Schlicht f → UniformBound f) :
    ∀ f ∈ ReaderC.schlicht, ReaderC.betaExp f (-2) ≤ 1 := fun f hf => by
  rw [C_betaExp_eq]; exact real_limsup_le_one (ev_of_bound (hb f ((C_Schlicht_iff f).1 hf)))

theorem C_image_nonempty : ((fun f => ReaderC.betaExp f (-2)) '' ReaderC.schlicht).Nonempty :=
  ⟨_, id, (C_Schlicht_iff id).2 id_schlicht, rfl⟩

theorem C_image_bdd (hb : ∀ f, Schlicht f → UniformBound f) :
    BddAbove ((fun f => ReaderC.betaExp f (-2)) '' ReaderC.schlicht) :=
  ⟨1, by rintro _ ⟨f, hf, rfl⟩; exact C_betaExp_le_one hb f hf⟩

/-- With the uniform bound, the frozen spectrum value gives reader C's real one. -/
theorem C_spectrum_of_frozen (hb : ∀ f, Schlicht f → UniformBound f) (hs : spectrum (-2) = 1) :
    ReaderC.bigB (-2) = 1 := by
  unfold ReaderC.bigB
  apply le_antisymm (csSup_le C_image_nonempty (by
    rintro _ ⟨f, hf, rfl⟩; exact C_betaExp_le_one hb f hf))
  by_contra hlt; push Not at hlt
  set S := (fun f => ReaderC.betaExp f (-2)) '' ReaderC.schlicht with hS
  have hb1 : (((sSup S + 1) / 2 : ℝ) : EReal) < spectrum (-2) := by
    rw [hs]; exact_mod_cast (by linarith : (sSup S + 1) / 2 < 1)
  obtain ⟨_, ⟨f, hf, rfl⟩, hfb⟩ := lt_sSup_iff.1 hb1
  have h1 := le_real_limsup (u := ratio f) (hfb.trans_le (beta_eq f).le) (ev_of_bound (hb f hf) 1 one_pos)
  rw [← C_betaExp_eq] at h1
  have h2 : ReaderC.betaExp f (-2) ≤ sSup S :=
    le_csSup (C_image_bdd hb) ⟨f, (C_Schlicht_iff f).2 hf, rfl⟩
  linarith

/-- With the uniform bound, reader C's real spectrum value gives the frozen one. -/
theorem frozen_spectrum_of_C (hb : ∀ f, Schlicht f → UniformBound f) (hs : ReaderC.bigB (-2) = 1) :
    spectrum (-2) = 1 := by
  have hle : ∀ f, Schlicht f → beta f (-2) ≤ 1 := fun f hf => by
    rw [beta_eq]; exact ereal_limsup_le_one (ev_of_bound (hb f hf))
  apply le_antisymm (sSup_le (by rintro _ ⟨f, hf, rfl⟩; exact hle f hf))
  by_contra hlt; push Not at hlt
  obtain ⟨y, hy1, hy2⟩ :=
    EReal.lt_iff_exists_real_btwn.1 (max_lt hlt (show (0 : EReal) < 1 from zero_lt_one))
  have hy0 : 0 < y := by exact_mod_cast (le_max_right _ _).trans_lt hy1
  have hys : spectrum (-2) < y := (le_max_left _ _).trans_lt hy1
  have hy1' : y < 1 := by exact_mod_cast hy2
  unfold ReaderC.bigB at hs
  obtain ⟨_, ⟨f, hf, rfl⟩, hfy⟩ := exists_lt_of_lt_csSup C_image_nonempty (by rw [hs]; exact hy1')
  change y < ReaderC.betaExp f (-2) at hfy
  rw [C_betaExp_eq] at hfy
  have h1 := le_ereal_limsup hy0 hfy
  have hfs : beta f (-2) ≤ spectrum (-2) := le_sSup ⟨f, (C_Schlicht_iff f).1 hf, rfl⟩
  rw [beta_eq] at hfs
  exact absurd (h1.trans hfs) (not_le.2 hys)

/-- Reader C's main theorem is equivalent to the frozen statement: the uniform bound, domain form and
disk form conjunct by conjunct, and the spectrum value in the presence of the uniform bound. -/
theorem closure_C :
    type_of% @OAI.Brennan.main_theorem ↔ type_of% @ReaderC.reading_thm_1_1 := by
  unfold MainStatement
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hb : ∀ f, Schlicht f → UniformBound f := fun f hf ε hε =>
      let ⟨C, hC⟩ := h1 ε hε; ⟨C, hC f hf⟩
    refine ⟨?_, C_spectrum_of_frozen hb h2, ?_, ?_⟩
    · intro ε hε
      obtain ⟨C, hC⟩ := h1 ε hε
      exact ⟨C, fun f hf r hr1 hr2 => by
        rw [C_M_eq]; exact hC f ((C_Schlicht_iff f).1 hf) r hr1 hr2⟩
    · rintro W hWo hWc hWsc ⟨x, y, hx, hy, hxy⟩ φ hbij hφ s hs1 hs2
      exact h3 W hWo hWc hWsc (by
        unfold SphericalBoundaryNontrivial Set.Nontrivial; exact ⟨x, hx, y, hy, hxy⟩)
        φ hφ hbij s hs1 hs2
    · intro f hf hinj t ht1 ht2; exact h4 f ⟨hf, hinj⟩ t ht1 ht2
  · rintro ⟨h1, h2, h3, h4⟩
    have hb : ∀ f, Schlicht f → UniformBound f := fun f hf ε hε =>
      let ⟨C, hC⟩ := h1 ε hε
      ⟨C, fun r hr1 hr2 => by rw [← C_M_eq]; exact hC f ((C_Schlicht_iff f).2 hf) r hr1 hr2⟩
    refine ⟨?_, frozen_spectrum_of_C hb h2, ?_, ?_⟩
    · intro ε hε
      obtain ⟨C, hC⟩ := h1 ε hε
      exact ⟨C, fun f hf r hr1 hr2 => by
        rw [← C_M_eq]; exact hC f ((C_Schlicht_iff f).2 hf) r hr1 hr2⟩
    · intro W hWo hWc hWsc hbd φ hφ hbij s hs1 hs2
      obtain ⟨x, hx, y, hy, hxy⟩ := hbd
      exact h3 W hWo hWc hWsc ⟨x, y, hx, hy, hxy⟩ φ hbij hφ s hs1 hs2
    · intro f hf t ht1 ht2; exact h4 f hf.1 hf.2 t ht1 ht2

end TargetO.BrennanMain

#print axioms TargetO.BrennanMain.closure_A
#print axioms TargetO.BrennanMain.closure_B
#print axioms TargetO.BrennanMain.closure_C
#print axioms TargetO.BrennanMain.C_spectrum_of_frozen
#print axioms TargetO.BrennanMain.frozen_spectrum_of_C
