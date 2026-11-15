import Checked.Math.Gelfand
import Checked.Math.BonnorEbertExtrema
import Checked.Math.BEAllMain

/-! Gelfand problem, `GelfandExtremaMain`: the proof route of `Checked.Math.GelfandExtrema.gelfand_extrema`, every turning point of the radial Gelfand branch in the three-dimensional ball. The turning points are the zeros of v − 2 in the homology variables u = s e^w / (−φ), v = −s φ (u v is the branch parameter); Volterra's function of (u, v) decreases along the solution and orders the extrema; the zeros of v − 2 are transversal and recur after every radius because the mass extrema of `Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema` recur; the first turning point and its value come from `Checked.Math.Gelfand.gelfand_ball_critical`. No new certificates. Promoted from `Work/Math/GelfandExtremaMain.lean`. -/

namespace Checked.Math.GelfandExtremaMain
open Set Filter Topology


theorem right_lt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (h : f' < 0) :
    ∀ᶠ t in 𝓝[>] x, f t < f x := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left
    (nhdsWithin_mono x (fun t (ht : t ∈ Ioi x) => (ne_of_gt ht : t ≠ x)))
  filter_upwards [h1.eventually (gt_mem_nhds h), self_mem_nhdsWithin] with t ht hx
  rw [slope_def_field] at ht
  have hx' : 0 < t - x := sub_pos.2 hx
  have := (div_neg_iff.1 ht)
  rcases this with ⟨_, h2⟩ | ⟨h2, _⟩
  · linarith
  · linarith

theorem right_gt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (h : 0 < f') :
    ∀ᶠ t in 𝓝[>] x, f x < f t := by
  have := right_lt hf.neg (by linarith)
  filter_upwards [this] with t ht
  simp only [Pi.neg_apply] at ht
  linarith

theorem left_gt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (h : f' < 0) :
    ∀ᶠ t in 𝓝[<] x, f x < f t := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hf).mono_left
    (nhdsWithin_mono x (fun t (ht : t ∈ Iio x) => (ne_of_lt ht : t ≠ x)))
  filter_upwards [h1.eventually (gt_mem_nhds h), self_mem_nhdsWithin] with t ht hx
  rw [slope_def_field] at ht
  have hx' : t - x < 0 := sub_neg.2 hx
  rcases (div_neg_iff.1 ht) with ⟨h2, _⟩ | ⟨_, h2⟩
  · linarith
  · linarith

theorem left_lt {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) (h : 0 < f') :
    ∀ᶠ t in 𝓝[<] x, f t < f x := by
  have := left_gt hf.neg (by linarith)
  filter_upwards [this] with t ht
  simp only [Pi.neg_apply] at ht
  linarith

/-- Constant sign on a preconnected set without zeros. -/
theorem pos_of_one {f : ℝ → ℝ} {S : Set ℝ} (hS : IsPreconnected S) (hc : ContinuousOn f S)
    (hz : ∀ t ∈ S, f t ≠ 0) {t0 : ℝ} (ht0 : t0 ∈ S) (hp : 0 < f t0) : ∀ t ∈ S, 0 < f t := by
  intro t ht
  by_contra hn
  push Not at hn
  obtain ⟨c, hcS, hc0⟩ := hS.intermediate_value ht ht0 hc ⟨hn, hp.le⟩
  exact hz c hcS hc0

theorem neg_of_one {f : ℝ → ℝ} {S : Set ℝ} (hS : IsPreconnected S) (hc : ContinuousOn f S)
    (hz : ∀ t ∈ S, f t ≠ 0) {t0 : ℝ} (ht0 : t0 ∈ S) (hp : f t0 < 0) : ∀ t ∈ S, f t < 0 := by
  have := pos_of_one (f := fun t => -f t) hS hc.neg (fun t ht h => hz t ht (by linarith))
    ht0 (by linarith)
  intro t ht
  have h2 : 0 < -f t := this t ht
  linarith

/-- Two zeros of f, every zero in between with negative derivative: impossible. -/
theorem no_two_neg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (fa : f a = 0) (fb : f b = 0)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (hs : ∀ t ∈ Icc a b, f t = 0 → f' t < 0) :
    False := by
  have ha := right_lt (hd a ⟨le_rfl, hab.le⟩) (hs a ⟨le_rfl, hab.le⟩ fa)
  have hb := left_gt (hd b ⟨hab.le, le_rfl⟩) (hs b ⟨hab.le, le_rfl⟩ fb)
  obtain ⟨c, hc, hca⟩ := (ha.and (Ioo_mem_nhdsGT hab)).exists
  rw [fa] at hc
  obtain ⟨e, he, hea⟩ := (hb.and (Ioo_mem_nhdsLT hca.2)).exists
  rw [fb] at he
  have hce : c < e := hea.1
  have hcont : ContinuousOn f (Icc c e) := fun t ht =>
    (hd t ⟨by linarith [hca.1, ht.1], by linarith [hea.2, ht.2]⟩).continuousAt.continuousWithinAt
  set S := Icc c e ∩ f ⁻¹' Ici 0 with hS
  have hcl : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hne : S.Nonempty := ⟨e, ⟨hce.le, le_rfl⟩, he.le⟩
  have hbdd : BddBelow S := ⟨c, fun t ht => ht.1.1⟩
  have hz := hcl.csInf_mem hne hbdd
  set z := sInf S
  have hzc : c ≤ z := hz.1.1
  have hz0 : 0 ≤ f z := hz.2
  have hcz : c < z := by
    rcases eq_or_lt_of_le hzc with h | h
    · rw [← h] at hz0; linarith
    · exact h
  have below : ∀ t ∈ Ico c z, f t < 0 := by
    intro t ht
    by_contra hn
    push Not at hn
    have : z ≤ t := csInf_le hbdd ⟨⟨ht.1, ht.2.le.trans hz.1.2⟩, hn⟩
    linarith [ht.2]
  have hzI : z ∈ Icc a b := ⟨by linarith [hca.1], by linarith [hz.1.2, hea.2]⟩
  have fz : f z = 0 := by
    by_contra hn
    have hpos : 0 < f z := lt_of_le_of_ne hz0 (Ne.symm hn)
    have hcz' := (hd z hzI).continuousAt
    have : ∀ᶠ t in 𝓝[<] z, 0 < f t :=
      (hcz'.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hpos)
    obtain ⟨t, ht, htI⟩ := (this.and (Ioo_mem_nhdsLT hcz)).exists
    linarith [below t ⟨htI.1.le, htI.2⟩]
  have hl := left_gt (hd z hzI) (hs z hzI fz)
  obtain ⟨t, ht, htI⟩ := (hl.and (Ioo_mem_nhdsLT hcz)).exists
  rw [fz] at ht
  linarith [below t ⟨htI.1.le, htI.2⟩]

theorem no_two_pos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (fa : f a = 0) (fb : f b = 0)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (hs : ∀ t ∈ Icc a b, f t = 0 → 0 < f' t) :
    False :=
  no_two_neg (f := fun t => -f t) (f' := fun t => -f' t) hab (by simp [fa]) (by simp [fb])
    (fun t ht => (hd t ht).neg) (fun t ht h => by
      have := hs t ht (by simp at h; linarith)
      linarith)

/-- x − log x comparison. -/
theorem g_ineq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b - a) * (1 - 1 / a) ≤ (b - Real.log b) - (a - Real.log a) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have : (b - a) * (1 - 1 / a) = (b - a) - (b / a - 1) := by field_simp
  rw [this]
  linarith


theorem g_ineq' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b - a) * (a - 1) ≤ a * ((b - Real.log b) - (a - Real.log a)) := by
  have h := g_ineq ha hb
  have e : (b - a) * (a - 1) = a * ((b - a) * (1 - 1 / a)) := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h ha.le

/-! ## The equation -/

noncomputable def lam (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)
noncomputable def Y (φ : ℝ → ℝ) (s : ℝ) : ℝ := -(s * φ s) - 2
noncomputable def Dd (w φ : ℝ → ℝ) (s : ℝ) : ℝ := 2 * Real.exp (w s) - φ s ^ 2
noncomputable def Mm (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)
noncomputable def U (w φ : ℝ → ℝ) (s : ℝ) : ℝ := s * Real.exp (w s) / -φ s
noncomputable def V (φ : ℝ → ℝ) (s : ℝ) : ℝ := -(s * φ s)
noncomputable def H (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  U w φ s - Real.log (U w φ s) + V φ s - 2 * Real.log (V φ s)

structure Hyp (w φ : ℝ → ℝ) : Prop where
  dw : ∀ s, 0 < s → HasDerivAt w (φ s) s
  dφ : ∀ s, 0 < s → HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s
  cw : ContinuousOn w (Ici 0)
  cφ : ContinuousOn φ (Ici 0)

theorem hyp_of {w φ : ℝ → ℝ}
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s) : Hyp w φ where
  dw s hs := (hw s (Set.mem_Ici.2 hs.le)).hasDerivAt (Ici_mem_nhds hs)
  dφ s hs := (hφ s hs).hasDerivAt (Ici_mem_nhds hs)
  cw s hs := (hw s hs).continuousWithinAt
  cφ s hs := by
    rcases eq_or_lt_of_le (Set.mem_Ici.1 hs) with h | h
    · subst h; exact hφ0
    · exact ((hφ s h).hasDerivAt (Ici_mem_nhds h)).continuousAt.continuousWithinAt

section
variable {w φ : ℝ → ℝ} (E : Hyp w φ)
include E

theorem phi_neg {s : ℝ} (hs : 0 < s) : φ s < 0 := by
  have hQ : ∀ x, 0 < x → HasDerivAt (fun s => s ^ 2 * φ s) (-(x ^ 2 * Real.exp (w x))) x := by
    intro x hx
    have := (hasDerivAt_pow 2 x).mul (E.dφ x hx)
    refine this.congr_deriv ?_
    norm_num
    field_simp
    ring
  have hcont : ContinuousOn (fun s => s ^ 2 * φ s) (Ici 0) :=
    (continuous_pow 2).continuousOn.mul E.cφ
  have hanti : StrictAntiOn (fun s => s ^ 2 * φ s) (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) hcont
    intro x hx
    rw [interior_Ici] at hx
    rw [(hQ x hx).deriv]
    exact neg_neg_of_pos (mul_pos (pow_pos hx 2) (Real.exp_pos _))
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs.le) hs
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
  exact neg_of_mul_neg_right this (by positivity)

theorem lam_cont : ContinuousOn (lam w) (Ici 0) :=
  (continuous_pow 2).continuousOn.mul (Real.continuous_exp.comp_continuousOn E.cw)

theorem lam_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt (lam w) (s * Real.exp (w s) * (2 + s * φ s)) s := by
  have := (hasDerivAt_pow 2 s).mul (E.dw s hs).exp
  refine this.congr_deriv ?_
  norm_num
  ring

theorem Y_cont : ContinuousOn (Y φ) (Ici 0) :=
  ((continuous_id.continuousOn.mul E.cφ).neg).sub continuousOn_const

theorem Y_deriv {s : ℝ} (hs : 0 < s) : HasDerivAt (Y φ) (φ s + s * Real.exp (w s)) s := by
  have := (((hasDerivAt_id s).mul (E.dφ s hs)).neg).sub_const 2
  refine this.congr_deriv ?_
  simp only [id, Pi.mul_apply, Pi.neg_apply]
  field_simp
  ring

theorem D_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Dd w φ) (4 * φ s * Real.exp (w s) + 4 * φ s ^ 2 / s) s := by
  have := ((E.dw s hs).exp.const_mul 2).sub ((E.dφ s hs).pow 2)
  refine this.congr_deriv ?_
  norm_num
  field_simp
  ring

theorem M_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt (Mm w φ)
      (s ^ 2 * Real.exp (w s / 2) * (Real.exp (w s) - φ s ^ 2 / 2) / Real.sqrt (4 * Real.pi)) s := by
  have := ((((hasDerivAt_pow 2 s).mul (E.dφ s hs).neg).mul
    ((E.dw s hs).div_const 2).exp).div_const (Real.sqrt (4 * Real.pi)))
  refine this.congr_deriv ?_
  norm_num
  field_simp
  ring

theorem U_pos {s : ℝ} (hs : 0 < s) : 0 < U w φ s :=
  div_pos (mul_pos hs (Real.exp_pos _)) (neg_pos.2 (phi_neg E hs))

theorem V_pos {s : ℝ} (hs : 0 < s) : 0 < V φ s := by
  unfold V; have := phi_neg E hs; nlinarith

theorem U_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt (U w φ) (U w φ s * (3 - U w φ s - V φ s) / s) s := by
  have hne : -φ s ≠ 0 := (neg_pos.2 (phi_neg E hs)).ne'
  have := ((hasDerivAt_id s).mul (E.dw s hs).exp).div (E.dφ s hs).neg hne
  refine this.congr_deriv ?_
  unfold U V
  simp only [id, Pi.mul_apply, Pi.neg_apply]
  have hφ : φ s ≠ 0 := (phi_neg E hs).ne
  field_simp
  ring

theorem V_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt (V φ) (V φ s * (U w φ s - 1) / s) s := by
  have := ((hasDerivAt_id s).mul (E.dφ s hs)).neg
  refine this.congr_deriv ?_
  unfold U V
  simp only [id, Pi.mul_apply, Pi.neg_apply]
  have hφ : φ s ≠ 0 := (phi_neg E hs).ne
  field_simp
  ring

omit E in
theorem H_alg {u v s : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (hs : s ≠ 0) :
    u * (3 - u - v) / s - u * (3 - u - v) / s / u + v * (u - 1) / s
      - 2 * (v * (u - 1) / s / v) = -(u - 1) ^ 2 / s := by
  field_simp
  ring

theorem H_deriv {s : ℝ} (hs : 0 < s) : HasDerivAt (H w φ) (-(U w φ s - 1) ^ 2 / s) s := by
  have hu := U_deriv E hs
  have hv := V_deriv E hs
  have := ((hu.sub (hu.log (U_pos E hs).ne')).add hv).sub ((hv.log (V_pos E hs).ne').const_mul 2)
  exact this.congr_deriv (H_alg (U_pos E hs).ne' (V_pos E hs).ne' hs.ne')

theorem lam_eq_UV {s : ℝ} (hs : 0 < s) : lam w s = U w φ s * V φ s := by
  have hφ : φ s ≠ 0 := (phi_neg E hs).ne
  unfold lam U V
  field_simp

theorem H_lower {s : ℝ} (hs : 0 < s) : 3 - 2 * Real.log 2 ≤ H w φ s := by
  have h1 := Real.log_le_sub_one_of_pos (U_pos E hs)
  have h2 := Real.log_le_sub_one_of_pos (half_pos (V_pos E hs))
  rw [Real.log_div (V_pos E hs).ne' two_ne_zero] at h2
  unfold H
  linarith

theorem H_eq {s : ℝ} (hs : 0 < s) (h : H w φ s ≤ 3 - 2 * Real.log 2) :
    U w φ s = 1 ∧ V φ s = 2 := by
  have h1 := Real.log_le_sub_one_of_pos (U_pos E hs)
  have h2 := Real.log_le_sub_one_of_pos (half_pos (V_pos E hs))
  rw [Real.log_div (V_pos E hs).ne' two_ne_zero] at h2
  unfold H at h
  constructor
  · by_contra hne
    have := Real.log_lt_sub_one_of_pos (U_pos E hs) hne
    linarith
  · by_contra hne
    have h3 := Real.log_lt_sub_one_of_pos (half_pos (V_pos E hs))
      (fun h => hne (by linarith))
    rw [Real.log_div (V_pos E hs).ne' two_ne_zero] at h3
    linarith

theorem H_anti : AntitoneOn (H w φ) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (H_deriv E hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; exact fun x hx => (H_deriv E hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(H_deriv E hx).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hx.le

/-! At a zero of Y = v − 2. -/

theorem at_zero_phi {s : ℝ} (hs : 0 < s) (hy : Y φ s = 0) : s * φ s = -2 := by
  unfold Y at hy; linarith

theorem at_zero_lam {s : ℝ} (hs : 0 < s) (hy : Y φ s = 0) :
    lam w s - 2 = s * (φ s + s * Real.exp (w s)) := by
  have := at_zero_phi E hs hy
  unfold lam
  linear_combination (-1 : ℝ) * this

theorem at_zero_U {s : ℝ} (hs : 0 < s) (hy : Y φ s = 0) : U w φ s = lam w s / 2 := by
  have := at_zero_phi E hs hy
  have hφ : φ s ≠ 0 := (phi_neg E hs).ne
  have hφ' : φ s = -2 / s := by field_simp; linarith
  unfold U lam
  rw [hφ']
  field_simp

theorem at_zero_V {s : ℝ} (hs : 0 < s) (hy : Y φ s = 0) : V φ s = 2 := by
  have := at_zero_phi E hs hy
  unfold V; linarith

theorem at_zero_H {s : ℝ} (hs : 0 < s) (hy : Y φ s = 0) :
    H w φ s = lam w s / 2 - Real.log (lam w s / 2) + 2 - 2 * Real.log 2 := by
  unfold H
  rw [at_zero_U E hs hy, at_zero_V E hs hy]

theorem at_zero_M {s : ℝ} (hs : 0 < s) (hy : Y φ s = 0) : Real.pi * Mm w φ s ^ 2 = lam w s := by
  have h := at_zero_phi E hs hy
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : Real.sqrt (4 * Real.pi) ^ 2 = 4 * Real.pi := Real.sq_sqrt (by positivity)
  have he : Real.exp (w s / 2) ^ 2 = Real.exp (w s) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hsq0 : Real.sqrt (4 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have key : (s ^ 2 * (-φ s) * Real.exp (w s / 2)) ^ 2 = 4 * (s ^ 2 * Real.exp (w s)) := by
    have h4 : (-φ s) ^ 2 * s ^ 2 = 4 := by nlinarith [h]
    calc (s ^ 2 * (-φ s) * Real.exp (w s / 2)) ^ 2
        = s ^ 2 * ((-φ s) ^ 2 * s ^ 2) * Real.exp (w s / 2) ^ 2 := by ring
      _ = 4 * (s ^ 2 * Real.exp (w s)) := by rw [h4, he]; ring
  unfold Mm lam
  rw [div_pow, key, hsq]
  field_simp

end

/-! ## Zeros of a function with transversal zeros -/

/-- A sign change at a transversal zero: negative on the left forces a positive derivative and
positivity on the right up to the next zero. -/
theorem flip_neg {y d : ℝ → ℝ} {a z b : ℝ} (haz : a < z) (hzb : z < b) (hyz : y z = 0)
    (hd : HasDerivAt y (d z) z) (hd0 : d z ≠ 0) (hc : ContinuousOn y (Ioo z b))
    (hnz : ∀ t ∈ Ioo z b, y t ≠ 0) (hl : ∀ t ∈ Ioo a z, y t < 0) :
    0 < d z ∧ ∀ t ∈ Ioo z b, 0 < y t := by
  have hpos : 0 < d z := by
    rcases lt_or_gt_of_ne hd0 with h | h
    · exfalso
      obtain ⟨t, ht, htI⟩ := ((left_gt hd h).and (Ioo_mem_nhdsLT haz)).exists
      rw [hyz] at ht
      linarith [hl t htI]
    · exact h
  refine ⟨hpos, ?_⟩
  obtain ⟨t0, ht0, ht0I⟩ := ((right_gt hd hpos).and (Ioo_mem_nhdsGT hzb)).exists
  rw [hyz] at ht0
  exact pos_of_one isPreconnected_Ioo hc hnz ht0I ht0

theorem flip_pos {y d : ℝ → ℝ} {a z b : ℝ} (haz : a < z) (hzb : z < b) (hyz : y z = 0)
    (hd : HasDerivAt y (d z) z) (hd0 : d z ≠ 0) (hc : ContinuousOn y (Ioo z b))
    (hnz : ∀ t ∈ Ioo z b, y t ≠ 0) (hl : ∀ t ∈ Ioo a z, 0 < y t) :
    d z < 0 ∧ ∀ t ∈ Ioo z b, y t < 0 := by
  have := flip_neg (y := fun t => -y t) (d := fun t => -d t) haz hzb (by simp [hyz]) hd.neg
    (by simpa using hd0) hc.neg (fun t ht h => hnz t ht (by simpa using h))
    (fun t ht => neg_neg_of_pos (hl t ht))
  refine ⟨by linarith [this.1], fun t ht => ?_⟩
  have h3 : 0 < -y t := this.2 t ht
  linarith

theorem zeros {y d : ℝ → ℝ} (hc : ContinuousOn y (Ici 0)) (h0 : y 0 < 0)
    (hd : ∀ z, 0 < z → y z = 0 → HasDerivAt y (d z) z ∧ d z ≠ 0)
    (hinf : ∀ T, ∃ z, T < z ∧ y z = 0) :
    ∃ ζ : ℕ → ℝ, StrictMono ζ ∧ Tendsto ζ atTop atTop ∧ 0 < ζ 0 ∧ (∀ n, y (ζ n) = 0) ∧
      (∀ t ∈ Ico 0 (ζ 0), y t < 0) ∧
      (∀ k, 0 < d (ζ (2 * k)) ∧ ∀ t ∈ Ioo (ζ (2 * k)) (ζ (2 * k + 1)), 0 < y t) ∧
      (∀ k, d (ζ (2 * k + 1)) < 0 ∧ ∀ t ∈ Ioo (ζ (2 * k + 1)) (ζ (2 * k + 2)), y t < 0) := by
  -- a zero-free interval to the right of every a ≥ 0
  have gap : ∀ a, 0 ≤ a → ∃ u, a < u ∧ ∀ t ∈ Ioo a u, y t ≠ 0 := by
    intro a ha
    have hev : ∀ᶠ t in 𝓝[>] a, y t ≠ 0 := by
      by_cases hya : y a = 0
      · have hapos : 0 < a := by
          rcases eq_or_lt_of_le ha with h | h
          · subst h; linarith
          · exact h
        obtain ⟨hda, hda0⟩ := hd a hapos hya
        have := hda.eventually_ne (c := 0) hda0
        exact this.filter_mono (nhdsWithin_mono a (fun t (ht : t ∈ Ioi a) => (ne_of_gt ht : t ≠ a)))
      · have hca : ContinuousWithinAt y (Ici 0) a := hc a (Set.mem_Ici.2 ha)
        have h1 : ∀ᶠ t in 𝓝[Ici 0] a, y t ≠ 0 := hca.eventually_ne hya
        exact h1.filter_mono (nhdsWithin_mono a (fun t (ht : t ∈ Ioi a) =>
          (Set.mem_Ici.2 (ha.trans ht.le))))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    exact ⟨u, hu, fun t ht => hsub ht⟩
  -- the next zero
  have next : ∀ a, 0 ≤ a → ∃ b, a < b ∧ y b = 0 ∧ ∀ t ∈ Ioo a b, y t ≠ 0 := by
    intro a ha
    obtain ⟨u, hau, hu⟩ := gap a ha
    have hu0 : 0 < u := lt_of_le_of_lt ha hau
    let S := Ici u ∩ y ⁻¹' {0}
    have hcl : IsClosed S :=
      (hc.mono (Ici_subset_Ici.2 hu0.le)).preimage_isClosed_of_isClosed isClosed_Ici
        isClosed_singleton
    obtain ⟨z, hz, hyz⟩ := hinf u
    have hne : S.Nonempty := ⟨z, Set.mem_Ici.2 hz.le, hyz⟩
    have hbdd : BddBelow S := ⟨u, fun t ht => ht.1⟩
    have hmem := hcl.csInf_mem hne hbdd
    refine ⟨sInf S, lt_of_lt_of_le hau hmem.1, hmem.2, fun t ht hyt => ?_⟩
    rcases lt_or_ge t u with htu | htu
    · exact hu t ⟨ht.1, htu⟩ hyt
    · have : sInf S ≤ t := csInf_le hbdd ⟨htu, hyt⟩
      linarith [ht.2]
  choose! nx hnx using next
  let ζ : ℕ → ℝ := fun n => Nat.rec (nx 0) (fun _ z => nx z) n
  have hζ0 : ζ 0 = nx 0 := rfl
  have hζs : ∀ n, ζ (n + 1) = nx (ζ n) := fun n => rfl
  have pos : ∀ n, 0 < ζ n := by
    intro n
    induction n with
    | zero => rw [hζ0]; exact (hnx 0 le_rfl).1
    | succ n ih => rw [hζs]; exact ih.trans (hnx _ ih.le).1
  have step : ∀ n, ζ n < ζ (n + 1) := fun n => by rw [hζs]; exact (hnx _ (pos n).le).1
  have zero : ∀ n, y (ζ n) = 0 := by
    intro n
    cases n with
    | zero => rw [hζ0]; exact (hnx 0 le_rfl).2.1
    | succ n => rw [hζs]; exact (hnx _ (pos n).le).2.1
  have gapn : ∀ n, ∀ t ∈ Ioo (ζ n) (ζ (n + 1)), y t ≠ 0 := fun n t ht => by
    rw [hζs] at ht; exact (hnx _ (pos n).le).2.2 t ht
  have gap0 : ∀ t ∈ Ioo 0 (ζ 0), y t ≠ 0 := fun t ht => by
    rw [hζ0] at ht; exact (hnx 0 le_rfl).2.2 t ht
  have hmono : StrictMono ζ := strictMono_nat_of_lt_succ step
  have htend : Tendsto ζ atTop atTop := by
    rw [tendsto_atTop_atTop_iff_of_monotone hmono.monotone]
    by_contra hn
    push Not at hn
    obtain ⟨b, hb⟩ := hn
    have hbdd : BddAbove (range ζ) := ⟨b, by rintro _ ⟨n, rfl⟩; exact (hb n).le⟩
    have hlim := tendsto_atTop_ciSup hmono.monotone hbdd
    set L := ⨆ i, ζ i
    have hle : ∀ n, ζ n < L := fun n => lt_of_lt_of_le (step n) (le_ciSup hbdd (n + 1))
    have hL : 0 < L := (pos 0).trans (hle 0)
    have hyL : y L = 0 := by
      have hcL : ContinuousAt y L :=
        (hc L (Set.mem_Ici.2 hL.le)).continuousAt (Ici_mem_nhds hL)
      have := hcL.tendsto.comp hlim
      exact tendsto_nhds_unique this (by simp only [Function.comp_def, zero]; exact tendsto_const_nhds)
    obtain ⟨hdL, hdL0⟩ := hd L hL hyL
    have hev := hdL.eventually_ne (c := 0) hdL0
    have hev' : ∀ᶠ n in atTop, y (ζ n) ≠ 0 := by
      have : Tendsto ζ atTop (𝓝[≠] L) :=
        tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hle n).ne⟩
      exact this.eventually hev
    obtain ⟨n, hn⟩ := hev'.exists
    exact hn (zero n)
  -- signs
  have base : ∀ t ∈ Ico 0 (ζ 0), y t < 0 := by
    refine neg_of_one isPreconnected_Ico (hc.mono Ico_subset_Ici_self) ?_
      (Set.left_mem_Ico.2 (pos 0)) h0
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; exact h0.ne
    · exact gap0 t ⟨h, ht.2⟩
  have cont : ∀ n, ContinuousOn y (Ioo (ζ n) (ζ (n + 1))) := fun n =>
    hc.mono (fun t ht => Set.mem_Ici.2 ((pos n).le.trans ht.1.le))
  have ind : ∀ k, (0 < d (ζ (2 * k)) ∧ ∀ t ∈ Ioo (ζ (2 * k)) (ζ (2 * k + 1)), 0 < y t) ∧
      (d (ζ (2 * k + 1)) < 0 ∧ ∀ t ∈ Ioo (ζ (2 * k + 1)) (ζ (2 * k + 2)), y t < 0) := by
    intro k
    induction k with
    | zero =>
      have h1 := flip_neg (a := 0) (pos 0) (step 0) (zero 0) (hd _ (pos 0) (zero 0)).1
        (hd _ (pos 0) (zero 0)).2 (cont 0) (gapn 0) (fun t ht => base t ⟨ht.1.le, ht.2⟩)
      have h2 := flip_pos (step 0) (step 1) (zero 1) (hd _ (pos 1) (zero 1)).1
        (hd _ (pos 1) (zero 1)).2 (cont 1) (gapn 1) h1.2
      exact ⟨h1, h2⟩
    | succ k ih =>
      have e1 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      have e2 : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by ring
      have e3 : 2 * (k + 1) + 2 = 2 * k + 3 + 1 := by ring
      have l1 := ih.2.2
      rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring] at l1
      have h1 := flip_neg (step (2 * k + 1)) (step (2 * k + 1 + 1)) (zero (2 * k + 1 + 1))
        (hd _ (pos (2 * k + 1 + 1)) (zero (2 * k + 1 + 1))).1
        (hd _ (pos (2 * k + 1 + 1)) (zero (2 * k + 1 + 1))).2
        (cont (2 * k + 1 + 1)) (gapn (2 * k + 1 + 1)) l1
      have h2 := flip_pos (step (2 * k + 1 + 1)) (step (2 * k + 1 + 1 + 1))
        (zero (2 * k + 1 + 1 + 1))
        (hd _ (pos (2 * k + 1 + 1 + 1)) (zero (2 * k + 1 + 1 + 1))).1
        (hd _ (pos (2 * k + 1 + 1 + 1)) (zero (2 * k + 1 + 1 + 1))).2
        (cont (2 * k + 1 + 1 + 1)) (gapn (2 * k + 1 + 1 + 1)) h1.2
      rw [e1]
      exact ⟨h1, h2⟩
  exact ⟨ζ, hmono, htend, pos 0, zero, base, fun k => (ind k).1, fun k => (ind k).2⟩

/-! ## Assembly -/

section
variable {w φ : ℝ → ℝ} (E : Hyp w φ)
include E

theorem D_zero_of_max {a z : ℝ} (ha : 0 ≤ a) (haz : a < z)
    (h : ∀ s ∈ Ici a, s ≠ z → Mm w φ s < Mm w φ z) : Dd w φ z = 0 := by
  have hz : 0 < z := lt_of_le_of_lt ha haz
  have hloc : IsLocalMax (Mm w φ) z :=
    Filter.eventually_of_mem (Ioi_mem_nhds haz) (fun s hs => by
      by_cases hsz : s = z
      · rw [hsz]
      · exact (h s (Set.mem_Ici.2 (le_of_lt hs)) hsz).le)
  have h0 := hloc.hasDerivAt_eq_zero (M_deriv E hz)
  have hsq0 : Real.sqrt (4 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have key : Real.exp (w z) - φ z ^ 2 / 2 = 0 := by
    by_contra hne
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hz.ne') (Real.exp_pos _).ne') hne)
      hsq0 h0
  unfold Dd
  linarith

theorem D_deriv_at_zero {s : ℝ} (hs : 0 < s) (hD : Dd w φ s = 0) :
    4 * φ s * Real.exp (w s) + 4 * φ s ^ 2 / s = -(2 * φ s ^ 2 / s) * Y φ s := by
  have he : Real.exp (w s) = φ s ^ 2 / 2 := by unfold Dd at hD; linarith
  rw [he]
  unfold Y
  field_simp
  ring

theorem phi_sq_pos {s : ℝ} (hs : 0 < s) : 0 < φ s ^ 2 := by
  have := phi_neg E hs; nlinarith

omit E in
theorem lam_pos {s : ℝ} (hs : 0 < s) : 0 < lam w s := by
  unfold lam; positivity

/-- H strictly decreases from a zero of Y with λ ≠ 2 to any later radius beyond the next point. -/
theorem H_drop {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hy : Y φ a = 0)
    (hl : lam w a ≠ 2) : H w φ c < H w φ a := by
  have hU : U w φ a ≠ 1 := by
    rw [at_zero_U E ha hy]; intro h; apply hl; linarith
  have hU' : U w φ a - 1 ≠ 0 := sub_ne_zero.2 hU
  have hsq : 0 < (U w φ a - 1) ^ 2 := by positivity
  have hd : -(U w φ a - 1) ^ 2 / a < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hsq) ha
  obtain ⟨t, ht, htI⟩ := ((right_lt (H_deriv E ha) hd).and (Ioo_mem_nhdsGT hab)).exists
  have : H w φ c ≤ H w φ t :=
    H_anti E (show (0 : ℝ) < t from ha.trans htI.1) (show (0 : ℝ) < c from by linarith [htI.2])
      (by linarith [htI.2])
  linarith

theorem lam_order {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hya : Y φ a = 0) (hyc : Y φ c = 0)
    (hH : H w φ c < H w φ a) :
    (2 < lam w a → lam w c < lam w a) ∧ (lam w a < 2 → lam w a < lam w c) := by
  rw [at_zero_H E ha hya, at_zero_H E hc hyc] at hH
  have hA : 0 < lam w a / 2 := half_pos (lam_pos ha)
  have hB : 0 < lam w c / 2 := half_pos (lam_pos hc)
  have hg := g_ineq' hA hB
  have hneg : lam w a / 2 * ((lam w c / 2 - Real.log (lam w c / 2)) -
      (lam w a / 2 - Real.log (lam w a / 2))) < 0 := mul_neg_of_pos_of_neg hA (by linarith)
  constructor
  · intro h2
    by_contra hn
    push Not at hn
    have : 0 ≤ (lam w c / 2 - lam w a / 2) * (lam w a / 2 - 1) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  · intro h2
    by_contra hn
    push Not at hn
    have : 0 ≤ (lam w c / 2 - lam w a / 2) * (lam w a / 2 - 1) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    linarith

end

theorem two_pi : Real.pi * Real.sqrt (2 / Real.pi) ^ 2 = 2 := by
  rw [Real.sq_sqrt (by positivity)]
  field_simp

theorem main (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ζ : ℕ → ℝ, StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      4.071496844 ≤ ζ 0 ∧ ζ 0 ≤ 4.071496845 ∧
      3.321992118 ≤ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ∧ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ≤ 3.321992119 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ζ 0 → s ^ 2 * Real.exp (w s) < ζ 0 ^ 2 * Real.exp (w (ζ 0))) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k)), s ≠ ζ (2 * k + 1) →
        ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < s ^ 2 * Real.exp (w s)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k + 1)), s ≠ ζ (2 * k + 2) →
        s ^ 2 * Real.exp (w s) < ζ (2 * k + 2) ^ 2 * Real.exp (w (ζ (2 * k + 2)))) ∧
      (∀ k : ℕ, ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < 2 ∧
        2 < ζ (2 * k) ^ 2 * Real.exp (w (ζ (2 * k)))) ∧
      Tendsto (fun s => s ^ 2 * Real.exp (w s)) atTop (𝓝 2) ∧
      StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ,
        StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) := by
  have E := hyp_of hw hφ0 hφ
  obtain ⟨ξ, hξm, hξT, hξ0, -, -, -, hmax, hband, hlimM⟩ :=
    Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema w φ hw hφ0 hφ h0
  have ξpos : ∀ n, 0 < ξ n := fun n =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6.4507514) (hξ0.trans (hξm.monotone (Nat.zero_le n)))
  -- zeros of D at the mass maxima
  have Dξ : ∀ k, Dd w φ (ξ (2 * k + 2)) = 0 := fun k =>
    D_zero_of_max E (ξpos _).le (hξm (by omega)) (fun s hs hne => hmax k s hs hne)
  have big : ∀ T, ∃ n, T < ξ n := fun T => (hξT.eventually (eventually_gt_atTop T)).exists
  -- Y = v − 2 vanishes beyond every radius
  have hinf : ∀ T, ∃ z, T < z ∧ Y φ z = 0 := by
    intro T
    by_contra hno
    push Not at hno
    set T' := max T 1 with hT'
    have hT1 : 1 ≤ T' := le_max_right _ _
    obtain ⟨n, hn⟩ := big T'
    have ha : T' < ξ (2 * n + 2) := hn.trans_le (hξm.monotone (by omega))
    have hab : ξ (2 * n + 2) < ξ (2 * (n + 1) + 2) := hξm (by omega)
    have hcY : ContinuousOn (Y φ) (Ioi T') :=
      (Y_cont E).mono (fun t ht => Set.mem_Ici.2 (le_trans (by linarith) (le_of_lt (Set.mem_Ioi.1 ht))))
    have hnz : ∀ t ∈ Ioi T', Y φ t ≠ 0 := fun t ht => hno t (lt_of_le_of_lt (le_max_left _ _) ht)
    have hpos_of : ∀ t ∈ Icc (ξ (2 * n + 2)) (ξ (2 * (n + 1) + 2)), 0 < t := fun t ht =>
      lt_of_lt_of_le (by linarith) (ha.le.trans ht.1)
    have hmemT : ∀ t ∈ Icc (ξ (2 * n + 2)) (ξ (2 * (n + 1) + 2)), t ∈ Ioi T' := fun t ht =>
      lt_of_lt_of_le ha ht.1
    rcases lt_or_gt_of_ne (hnz _ ha) with hneg | hpos
    · have hY := neg_of_one isPreconnected_Ioi hcY hnz ha hneg
      exact no_two_pos (f := Dd w φ) (f' := fun t => 4 * φ t * Real.exp (w t) + 4 * φ t ^ 2 / t)
        hab (Dξ n) (Dξ (n + 1)) (fun t ht => D_deriv E (hpos_of t ht)) (fun t ht hD => by
          have h1 := hpos_of t ht
          rw [D_deriv_at_zero E h1 hD]
          have := hY t (hmemT t ht)
          have := div_pos (mul_pos two_pos (phi_sq_pos E h1)) h1
          nlinarith)
    · have hY := pos_of_one isPreconnected_Ioi hcY hnz ha hpos
      exact no_two_neg (f := Dd w φ) (f' := fun t => 4 * φ t * Real.exp (w t) + 4 * φ t ^ 2 / t)
        hab (Dξ n) (Dξ (n + 1)) (fun t ht => D_deriv E (hpos_of t ht)) (fun t ht hD => by
          have h1 := hpos_of t ht
          rw [D_deriv_at_zero E h1 hD]
          have := hY t (hmemT t ht)
          have := div_pos (mul_pos two_pos (phi_sq_pos E h1)) h1
          nlinarith)
  -- transversality of the zeros of Y
  have htr : ∀ z, 0 < z → Y φ z = 0 →
      HasDerivAt (Y φ) (φ z + z * Real.exp (w z)) z ∧ φ z + z * Real.exp (w z) ≠ 0 := by
    intro z hz hy
    refine ⟨Y_deriv E hz, fun hd0 => ?_⟩
    have hl : lam w z = 2 := by have := at_zero_lam E hz hy; rw [hd0, mul_zero] at this; linarith
    have hHz : H w φ z = 3 - 2 * Real.log 2 := by
      rw [at_zero_H E hz hy, hl]; norm_num
    obtain ⟨n, hn⟩ := big z
    set s := ξ (2 * n) with hs
    have hzs : z < s := hn.trans_le (hξm.monotone (by omega))
    have hs0 : 0 < s := hz.trans hzs
    have hHs : H w φ s ≤ 3 - 2 * Real.log 2 := hHz ▸ H_anti E hz hs0 hzs.le
    obtain ⟨hU, hV⟩ := H_eq E hs0 hHs
    have hYs : Y φ s = 0 := by unfold Y; unfold V at hV; linarith
    have hls : lam w s = 2 := by rw [lam_eq_UV E hs0, hU, hV]; norm_num
    have hM := at_zero_M E hs0 hYs
    rw [hls] at hM
    have hb := (hband n).2
    have hM2 : Mm w φ s ^ 2 = 2 / Real.pi := by
      rw [eq_div_iff Real.pi_pos.ne']; linarith
    have hMpos : 0 ≤ Mm w φ s := le_trans (Real.sqrt_nonneg _) hb.le
    have : Real.sqrt (2 / Real.pi) = Mm w φ s := by rw [← hM2, Real.sqrt_sq hMpos]
    exact absurd hb (by rw [this]; exact lt_irrefl _)
  have hY0 : Y φ 0 < 0 := by unfold Y; norm_num
  obtain ⟨ζ, hζm, hζT, hζ0, hzero, hbase, hev, hodd⟩ :=
    zeros (Y_cont E) hY0 (fun z hz hy => htr z hz hy) hinf
  have ζpos : ∀ n, 0 < ζ n := fun n => hζ0.trans_le (hζm.monotone (Nat.zero_le n))
  -- values at the zeros
  have even_gt : ∀ k, 2 < lam w (ζ (2 * k)) := fun k => by
    have := at_zero_lam E (ζpos (2 * k)) (hzero (2 * k))
    have := mul_pos (ζpos (2 * k)) (hev k).1
    linarith
  have odd_lt : ∀ k, lam w (ζ (2 * k + 1)) < 2 := fun k => by
    have := at_zero_lam E (ζpos (2 * k + 1)) (hzero (2 * k + 1))
    have := mul_neg_of_pos_of_neg (ζpos (2 * k + 1)) (hodd k).1
    linarith
  -- monotone segments
  have dl : ∀ x, 0 < x → deriv (lam w) x = x * Real.exp (w x) * (2 + x * φ x) :=
    fun x hx => (lam_deriv E hx).deriv
  have hY2 : ∀ x, 2 + x * φ x = -Y φ x := fun x => by unfold Y; ring
  have contI : ∀ a b, 0 ≤ a → ContinuousOn (lam w) (Icc a b) := fun a b ha =>
    (lam_cont E).mono (fun t ht => Set.mem_Ici.2 (ha.trans ht.1))
  have mono0 : StrictMonoOn (lam w) (Icc 0 (ζ 0)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (contI _ _ le_rfl)
    intro x hx
    rw [interior_Icc] at hx
    rw [dl x hx.1, hY2]
    have := hbase x ⟨hx.1.le, hx.2⟩
    have := Real.exp_pos (w x)
    have := hx.1
    have : 0 < -Y φ x := by linarith
    positivity
  have anti : ∀ k, StrictAntiOn (lam w) (Icc (ζ (2 * k)) (ζ (2 * k + 1))) := by
    intro k
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (contI _ _ (ζpos _).le)
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := (ζpos _).trans hx.1
    rw [dl x hx0, hY2]
    have := (hev k).2 x hx
    exact mul_neg_of_pos_of_neg (mul_pos hx0 (Real.exp_pos _)) (by linarith)
  have mono : ∀ k, StrictMonoOn (lam w) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2))) := by
    intro k
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (contI _ _ (ζpos _).le)
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := (ζpos _).trans hx.1
    rw [dl x hx0, hY2]
    have := (hodd k).2 x hx
    exact mul_pos (mul_pos hx0 (Real.exp_pos _)) (by linarith)
  -- ordering of the values at the zeros
  have drop : ∀ n, H w φ (ζ (n + 2)) < H w φ (ζ n) := fun n =>
    H_drop E (ζpos n) (hζm (by omega : n < n + 1)) (hζm.monotone (by omega))
      (hzero n) (by
        obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
        · exact (even_gt m).ne'
        · exact (odd_lt m).ne)
  have maxdec : ∀ m, lam w (ζ (2 * m + 2)) < lam w (ζ (2 * m)) := fun m =>
    (lam_order E (ζpos _) (ζpos _) (hzero _) (hzero _) (drop (2 * m))).1 (even_gt m)
  have mininc : ∀ m, lam w (ζ (2 * m + 1)) < lam w (ζ (2 * m + 1 + 2)) := fun m =>
    (lam_order E (ζpos _) (ζpos _) (hzero _) (hzero _) (drop (2 * m + 1))).2 (odd_lt m)
  have env := Checked.Math.BEAllMain.envelope (P := fun s => -lam w s) hζm hζT
    (fun k a ha b hb hab => neg_lt_neg (anti k ha hb hab))
    (fun k a ha b hb hab => neg_lt_neg (mono k ha hb hab))
    (strictMono_nat_of_lt_succ fun m => by
      show -lam w (ζ (2 * m)) < -lam w (ζ (2 * (m + 1)))
      rw [show 2 * (m + 1) = 2 * m + 2 by ring]
      exact neg_lt_neg (maxdec m))
    (strictAnti_nat_of_succ_lt fun m => by
      show -lam w (ζ (2 * (m + 1) + 1)) < -lam w (ζ (2 * m + 1))
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring]
      exact neg_lt_neg (mininc m))
    (fun m j => neg_lt_neg (by linarith [odd_lt j, even_gt m]))
  have e1 : ∀ j s, ζ (2 * j) ≤ s → s ≠ ζ (2 * j + 1) → lam w (ζ (2 * j + 1)) < lam w s :=
    fun j s hs hne => by
      have h : -lam w s < -lam w (ζ (2 * j + 1)) := env.1 j s hs hne
      linarith
  have e2 : ∀ j s, ζ (2 * j + 1) ≤ s → s ≠ ζ (2 * j + 2) → lam w s < lam w (ζ (2 * j + 2)) :=
    fun j s hs hne => by
      have h : -lam w (ζ (2 * j + 2)) < -lam w s := env.2.1 j s hs hne
      linarith
  -- the first maximum is the strict maximum
  have first : ∀ s, 0 ≤ s → s ≠ ζ 0 → lam w s < lam w (ζ 0) := by
    intro s hs hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mono0 ⟨hs, hlt.le⟩ ⟨(ζpos 0).le, le_rfl⟩ hlt
    have h01 : ζ 0 < ζ 1 := hζm (by omega)
    rcases le_or_gt s (ζ 1) with h1 | h1
    · exact (anti 0) ⟨le_rfl, h01.le⟩ ⟨hgt.le, h1⟩ hgt
    · have m0 := maxdec 0
      by_cases h2 : s = ζ 2
      · rw [h2]; exact m0
      · have := e2 0 s h1.le h2
        exact this.trans m0
  -- windows from gelfand_ball_critical
  have hr := Checked.Math.BEAllMain.restrict 5 hw hφ0 hφ
  obtain ⟨s₁, hs1a, hs1b, hs1max, hl1, hl2⟩ :=
    Checked.Math.Gelfand.gelfand_ball_critical 5 (by norm_num) w φ hr.1 hr.2.1 hr.2.2 h0
  have hs1pos : 0 < s₁ := lt_of_lt_of_le (by norm_num) hs1a
  have hs15 : s₁ < 5 := lt_of_le_of_lt hs1b (by norm_num)
  have hs1 : s₁ = ζ 0 := by
    by_contra hne
    rcases le_or_gt (ζ 0) 5 with h5 | h5
    · have a1 : lam w (ζ 0) ≤ lam w s₁ := hs1max (ζ 0) ⟨(ζpos 0).le, h5⟩
      have a2 := first s₁ hs1pos.le hne
      linarith
    · have a1 : lam w 5 ≤ lam w s₁ := hs1max 5 ⟨by norm_num, le_rfl⟩
      have a2 : lam w s₁ < lam w 5 := mono0 ⟨hs1pos.le, (hs15.trans h5).le⟩ ⟨by norm_num, h5.le⟩ hs15
      linarith
  -- the limit
  have hlz : Tendsto (fun n => lam w (ζ n)) atTop (𝓝 2) := by
    have hM : Tendsto (fun n => Mm w φ (ζ n)) atTop (𝓝 (Real.sqrt (2 / Real.pi))) :=
      hlimM.comp hζT
    have := (hM.pow 2).const_mul Real.pi
    rw [two_pi] at this
    refine this.congr (fun n => ?_)
    exact at_zero_M E (ζpos n) (hzero n)
  have seg : ∀ i, ∀ s ∈ Icc (ζ i) (ζ (i + 1)),
      min (lam w (ζ i)) (lam w (ζ (i + 1))) ≤ lam w s ∧
        lam w s ≤ max (lam w (ζ i)) (lam w (ζ (i + 1))) := by
    intro i s hs
    have hi : ζ i ≤ ζ (i + 1) := hζm.monotone (Nat.le_succ i)
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
    · have h := (anti m).antitoneOn
      exact ⟨min_le_right _ _ |>.trans (h hs ⟨hi, le_rfl⟩ hs.2),
        (h ⟨le_rfl, hi⟩ hs hs.1).trans (le_max_left _ _)⟩
    · have h := (mono m).monotoneOn
      have e : 2 * m + 1 + 1 = 2 * m + 2 := by ring
      rw [e] at hs hi ⊢
      exact ⟨min_le_left _ _ |>.trans (h ⟨le_rfl, hi⟩ hs hs.1),
        (h hs ⟨hi, le_rfl⟩ hs.2).trans (le_max_right _ _)⟩
  have hlim : Tendsto (lam w) atTop (𝓝 2) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hlz.eventually (lt_mem_nhds ha))
      refine eventually_atTop.2 ⟨ζ N, fun s hs => ?_⟩
      obtain ⟨i, hi, h1, h2⟩ := Checked.Math.BEAllMain.locate hζm hζT N hs
      exact lt_of_lt_of_le (lt_min (hN i hi) (hN (i + 1) (by omega))) (seg i s ⟨h1, h2.le⟩).1
    · intro b hb
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hlz.eventually (gt_mem_nhds hb))
      refine eventually_atTop.2 ⟨ζ N, fun s hs => ?_⟩
      obtain ⟨i, hi, h1, h2⟩ := Checked.Math.BEAllMain.locate hζm hζT N hs
      exact lt_of_le_of_lt (seg i s ⟨h1, h2.le⟩).2 (max_lt (hN i hi) (hN (i + 1) (by omega)))
  refine ⟨ζ, hζm, hζT, hs1 ▸ hs1a, hs1 ▸ hs1b, hs1 ▸ hl1, hs1 ▸ hl2,
    fun s hs hne => first s hs hne, fun k s hs hne => e1 k s hs hne,
    fun k s hs hne => e2 k s hs hne, fun k => ⟨odd_lt k, even_gt k⟩, hlim, mono0, anti, mono⟩

end Checked.Math.GelfandExtremaMain
