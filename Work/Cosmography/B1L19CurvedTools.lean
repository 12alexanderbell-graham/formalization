import Checked.Cosmography.B1L19
import Checked.Cosmography.BambaCurved

/-!
# Tools for `Work.Cosmography.B1L19Curved`: the closed/flat ΛCDM distance integral

`J(w) = ∫_w^1 2/√(m + k v² + (1 − m − k) v⁶) dv` (`m = Ω_m`, `k = Ω_k`), the bridge from the
pinned `lumDist K` to `J`, and tangent/chord cell enclosures of `J` that are linear in `(m, k)`.
Generated certificates: `Work.Cosmography.B1L19CurvedCerts` (`runs/2026-11-04T2028Z/scripts/gen_curved.py`).
-/

namespace Work.Cosmography.B1L19CurvedTools

open Set Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.B1 Checked.Cosmography.Transverse

/-- `y(v) = m + k v² + (1 − m − k) v⁶`. -/
noncomputable def yC (m k v : ℝ) : ℝ := m + k * v ^ 2 + (1 - m - k) * v ^ 6

/-- The integrand `2/√y`. -/
noncomputable def gC (m k v : ℝ) : ℝ := 2 / √(yC m k v)

/-- The domain of the theorems: `m ∈ [1/10, 1]`, `k ∈ [−1/10, 0]`. -/
structure Dom (m k : ℝ) : Prop where
  m0 : 1 / 10 ≤ m
  m1 : m ≤ 1
  k0 : -(1 / 10) ≤ k
  k1 : k ≤ 0

lemma yC_pos {m k : ℝ} (h : Dom m k) (v : ℝ) (hv : 0 < v) : 0 < yC m k v := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  unfold yC
  have hv6 : 0 < v ^ 6 := by positivity
  rcases le_total v 1 with hv1 | hv1
  · have hv2 : v ^ 2 ≤ 1 := by nlinarith
    have hv62 : v ^ 6 ≤ 1 := by
      have : v ^ 6 = (v ^ 2) ^ 3 := by ring
      rw [this]; exact pow_le_one₀ (by positivity) hv2
    -- k v² ≥ k, and (m + k) ≥ (m + k) v⁶
    have a1 : k * v ^ 2 ≥ k := by nlinarith
    have a2 : (m + k) * v ^ 6 ≤ m + k := by nlinarith
    nlinarith
  · have hv2 : 1 ≤ v ^ 2 := by nlinarith
    have hv26 : v ^ 2 ≤ v ^ 6 := by
      have : v ^ 6 = v ^ 2 * (v ^ 2) ^ 2 := by ring
      rw [this]; nlinarith
    have a1 : k * v ^ 2 ≥ k * v ^ 6 := by nlinarith
    have a2 : (1 - m) * v ^ 6 ≥ 0 := by nlinarith
    nlinarith

lemma gC_cont {m k : ℝ} (h : Dom m k) : ContinuousOn (gC m k) (Ioi 0) := by
  intro v hv
  have hin := yC_pos h v hv
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.div
  · exact (by unfold yC; fun_prop : Continuous fun v : ℝ => yC m k v).continuousAt.sqrt
  · exact (Real.sqrt_pos.2 hin).ne'

lemma gC_nonneg (m k v : ℝ) : 0 ≤ gC m k v := div_nonneg (by norm_num) (Real.sqrt_nonneg _)

lemma gC_intInt {m k : ℝ} (h : Dom m k) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    IntervalIntegrable (gC m k) MeasureTheory.volume α β := by
  apply (gC_cont h).mono _ |>.intervalIntegrable
  intro z hz; rw [uIcc_of_le hαβ] at hz; exact lt_of_lt_of_le hα hz.1

lemma sqrt_algC (m k a₀ as W : ℝ) (hW : 0 < W) (ha₀ : 0 < a₀) (has : as = W ^ 2 * a₀)
    (hin : 0 < yC m k W) :
    √(m * (1 + (a₀ / as - 1)) ^ 3 + k * (1 + (a₀ / as - 1)) ^ 2 + (1 - k) - m)
      = √(yC m k W) / W ^ 3 := by
  rw [show m * (1 + (a₀ / as - 1)) ^ 3 + k * (1 + (a₀ / as - 1)) ^ 2 + (1 - k) - m
      = (√(yC m k W) / W ^ 3) ^ 2 by
    rw [div_pow, Real.sq_sqrt hin.le, has]; unfold yC; field_simp; ring]
  exact Real.sqrt_sq (by positivity)

/-- Bridge: in a model obeying `H = H₀ √(m(1+z)³ + k(1+z)² + 1 − k − m)` on `[t, t₀]`, the comoving
distance is `J/(H₀ a₀)` with `J = ∫_{√(a/a₀)}^1 gC m k`. -/
theorem comoving_eq {m k : ℝ} (hd : Dom m k)
    (a : ℝ → ℝ) (t t₀ : ℝ) (htt : t ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀,
      hubble a s = hubble a t₀ * √(m * (1 + redshift a t₀ s) ^ 3
        + k * (1 + redshift a t₀ s) ^ 2 + (1 - k) - m)) :
    comoving a t₀ t = (∫ v in √(a t / a t₀)..1, gC m k v) / (hubble a t₀ * a t₀) := by
  set a₀ := a t₀ with ha₀def
  set H₀ := hubble a t₀ with hH₀def
  have ha₀ : 0 < a₀ := hpos t₀ ⟨htt, le_rfl⟩
  set G : ℝ → ℝ := fun x => ∫ v in (1:ℝ)..x, gC m k v with hGdef
  have hG : ∀ x, 0 < x → HasDerivAt G (gC m k x) x := by
    intro x hx
    have hsub : uIcc (1:ℝ) x ⊆ Ioi 0 := by
      intro y hy; rcases mem_uIcc.1 hy with h | h
      · exact lt_of_lt_of_le one_pos h.1
      · exact lt_of_lt_of_le hx h.1
    exact intervalIntegral.integral_hasDerivAt_right (((gC_cont hd).mono hsub).intervalIntegrable)
      ((gC_cont hd).stronglyMeasurableAtFilter isOpen_Ioi x hx)
      ((gC_cont hd).continuousAt (Ioi_mem_nhds hx))
  set W : ℝ → ℝ := fun s => √(a s / a₀) with hWdef
  set F : ℝ → ℝ := fun s => G (W s) / (H₀ * a₀) with hFdef
  have hF : ∀ s ∈ uIcc t t₀, HasDerivAt F (1 / a s) s := by
    intro s hs
    rw [uIcc_of_le htt] at hs
    have has := hpos s hs
    have hr : 0 < a s / a₀ := div_pos has ha₀
    have hWs : 0 < W s := Real.sqrt_pos.2 hr
    have hW2 : a s = W s ^ 2 * a₀ := by
      simp only [hWdef]; rw [Real.sq_sqrt hr.le]; field_simp
    have hd' : HasDerivAt W ((deriv a s / a₀) / (2 * √(a s / a₀))) s :=
      ((hdiff s hs).hasDerivAt.div_const a₀).sqrt hr.ne'
    have hc := ((hG (W s) hWs).comp s hd').div_const (H₀ * a₀)
    have hin := yC_pos hd (W s) hWs
    have hHs := hH s hs
    simp only [hubble, redshift] at hHs
    rw [← ha₀def, sqrt_algC m k a₀ (a s) (W s) hWs ha₀ hW2 hin] at hHs
    have hda : deriv a s = a s * H₀ * (√(yC m k (W s)) / W s ^ 3) := by
      rw [hH₀def]; field_simp at hHs ⊢; linarith [hHs]
    have := deriv_alg H₀ a₀ (a s) (deriv a s) _ (W s) hWs (Real.sqrt_pos.2 hin) ha₀ hH₀ hW2 hda
    exact hc.congr_deriv (by simpa [gC] using this)
  have hint : IntervalIntegrable (fun s => 1 / a s) MeasureTheory.volume t t₀ := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le htt] at hx
    exact (continuousAt_const.div (hdiff x hx).continuousAt (hpos x hx).ne').continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  have hW0 : W t₀ = 1 := by
    show √(a t₀ / a₀) = 1
    rw [← ha₀def, div_self ha₀.ne', Real.sqrt_one]
  have hG1 : G 1 = 0 := by simp [hGdef]
  unfold comoving
  rw [hftc]
  simp only [hFdef, hW0, hG1]
  rw [intervalIntegral.integral_symm]
  simp only [hGdef, hWdef]
  ring

/-- The pinned luminosity distance with `K ≥ 0` through `J`: with `κ = Ω₀ − 1 ≥ 0`,
`d_L = (1+z)/H₀ · S(J)`, `S(J) = sin(√κ J)/√κ` (`κ > 0`) or `J` (`κ = 0`). -/
lemma lumDist_eq (K : ℝ) (a : ℝ → ℝ) (t₀ t J : ℝ) (ha₀ : 0 < a t₀) (hH₀ : 0 < hubble a t₀)
    (hχ : comoving a t₀ t = J / (hubble a t₀ * a t₀)) (hK : 0 ≤ K) :
    lumDist K a t₀ t = (1 + redshift a t₀ t) / hubble a t₀ *
      (if omega0 K a t₀ - 1 = 0 then J
        else Real.sin (√(omega0 K a t₀ - 1) * J) / √(omega0 K a t₀ - 1)) := by
  set H₀ := hubble a t₀
  set a₀ := a t₀ with ha₀def
  have hκ : omega0 K a t₀ - 1 = K / (H₀ ^ 2 * a₀ ^ 2) := by unfold omega0; ring
  unfold lumDist transverse
  rw [hχ, hκ]
  rcases eq_or_lt_of_le hK with h0 | h0
  · subst h0; simp [ha₀def]; have : a t₀ ≠ 0 := ha₀.ne'
    field_simp
  · have hne : K / (H₀ ^ 2 * a₀ ^ 2) ≠ 0 := by positivity
    simp only [h0, ite_true, hne, ite_false]
    have hs : √(K / (H₀ ^ 2 * a₀ ^ 2)) = √K / (H₀ * a₀) := by
      rw [Real.sqrt_div' _ (by positivity)]
      rw [show H₀ ^ 2 * a₀ ^ 2 = (H₀ * a₀) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hs]
    have hK' : 0 < √K := Real.sqrt_pos.2 h0
    rw [show √K / (H₀ * a₀) * J = √K * (J / (H₀ * a₀)) by ring]
    field_simp
    simp only [ha₀def]; ring

/-! ## Cell enclosures, linear in `(m, k)` -/

lemma integral_poly26 (α β A B C : ℝ) :
    ∫ v in α..β, (A - B * v ^ 2 - C * v ^ 6)
      = A * (β - α) - B * (β ^ 3 - α ^ 3) / 3 - C * (β ^ 7 - α ^ 7) / 7 := by
  have hd : ∀ x ∈ uIcc α β, HasDerivAt (fun v : ℝ => A * v - B * v ^ 3 / 3 - C * v ^ 7 / 7)
      (A - B * x ^ 2 - C * x ^ 6) x := by
    intro x _
    have h := (((hasDerivAt_id' x).const_mul A).sub (((hasDerivAt_pow 3 x).const_mul B).div_const 3)).sub
      (((hasDerivAt_pow 7 x).const_mul C).div_const 7)
    exact h.congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- Tangent cell bound (no side condition on `c ≥ 0`). -/
lemma cell_lower {m k : ℝ} (hd : Dom m k) (c α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hc : 0 ≤ c) :
    (β - α) * (3 * c - c ^ 3 * m) - c ^ 3 * k * (β ^ 3 - α ^ 3) / 3
      - c ^ 3 * (1 - m - k) * (β ^ 7 - α ^ 7) / 7 ≤ ∫ v in α..β, gC m k v := by
  have e := integral_poly26 α β (3 * c - c ^ 3 * m) (c ^ 3 * k) (c ^ 3 * (1 - m - k))
  have hle : ∫ v in α..β, ((3 * c - c ^ 3 * m) - c ^ 3 * k * v ^ 2 - c ^ 3 * (1 - m - k) * v ^ 6)
      ≤ ∫ v in α..β, gC m k v := by
    apply intervalIntegral.integral_mono_on hαβ
      (by apply Continuous.intervalIntegrable; fun_prop) (gC_intInt hd α β hα hαβ)
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
    have hin := yC_pos hd v hv0
    have := tangent_le _ c hin hc
    unfold gC yC at *; rw [div_eq_mul_one_div 2]; nlinarith
  rw [e] at hle; linarith

/-- Chord cell bound: `p² ≤ y ≤ q²` on the cell. -/
lemma cell_upper {m k : ℝ} (hd : Dom m k) (p q α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (hp : 0 < p) (hq : 0 < q) (hy : ∀ v ∈ Icc α β, p ^ 2 ≤ yC m k v ∧ yC m k v ≤ q ^ 2) :
    ∫ v in α..β, gC m k v ≤ 2 * (β - α) / p
      - 2 / (p * q * (p + q)) * ((β - α) * m + k * (β ^ 3 - α ^ 3) / 3
        + (1 - m - k) * (β ^ 7 - α ^ 7) / 7 - (β - α) * p ^ 2) := by
  set g := 2 / (p * q * (p + q)) with hg
  have e := integral_poly26 α β (2 / p - g * m + g * p ^ 2) (g * k) (g * (1 - m - k))
  have hle : ∫ v in α..β, gC m k v
      ≤ ∫ v in α..β, ((2 / p - g * m + g * p ^ 2) - g * k * v ^ 2 - g * (1 - m - k) * v ^ 6) := by
    apply intervalIntegral.integral_mono_on hαβ (gC_intInt hd α β hα hαβ)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro v hv
    obtain ⟨hy1, hy2⟩ := hy v hv
    have := le_secant _ p q hp hq hy1 hy2
    have eg : (yC m k v - p ^ 2) / (p * q * (p + q)) = g / 2 * (yC m k v - p ^ 2) := by
      rw [hg]; field_simp
    rw [eg] at this
    have e2 : gC m k v = 2 * (1 / √(yC m k v)) := by unfold gC; ring
    rw [e2]
    have h3 : 2 * (1 / √(yC m k v)) ≤ 2 * (1 / p - g / 2 * (yC m k v - p ^ 2)) := by linarith
    refine le_trans h3 (le_of_eq ?_)
    unfold yC; ring
  rw [e] at hle; exact le_trans hle (le_of_eq (by ring))

/-- Interval bounds for `y` on a cell `[α, β] ⊆ (0, 1]` and a parameter box. -/
lemma y_box {m k : ℝ} (m₀ m₁ k₀ k₁ α β dlo dhi v : ℝ) (hm₀ : 0 ≤ m₀) (hm0 : m₀ ≤ m) (hm1 : m ≤ m₁)
    (hk0 : k₀ ≤ k) (hk1 : k ≤ k₁) (hk₁ : k₁ ≤ 0)
    (hα : 0 < α) (hβ : β ≤ 1) (hv : v ∈ Icc α β)
    (hdlo : 0 ≤ dlo) (hdl : dlo ≤ v ^ 2 - v ^ 6) (hdh : v ^ 2 - v ^ 6 ≤ dhi) :
    m₀ * (1 - β ^ 6) + k₀ * dhi + α ^ 6 ≤ yC m k v ∧ yC m k v ≤ m₁ * (1 - α ^ 6) + k₁ * dlo + β ^ 6 := by
  obtain ⟨hv1, hv2⟩ := hv
  have hv0 : 0 ≤ v := by linarith
  have a6 : α ^ 6 ≤ v ^ 6 := pow_le_pow_left₀ hα.le hv1 6
  have b6 : v ^ 6 ≤ β ^ 6 := pow_le_pow_left₀ hv0 hv2 6
  have b61 : β ^ 6 ≤ 1 := pow_le_one₀ (by linarith) hβ
  have e : yC m k v = m * (1 - v ^ 6) + k * (v ^ 2 - v ^ 6) + v ^ 6 := by unfold yC; ring
  rw [e]
  constructor
  · have t1 : m₀ * (1 - β ^ 6) ≤ m * (1 - v ^ 6) := by
      have : 1 - β ^ 6 ≤ 1 - v ^ 6 := by linarith
      nlinarith
    have t2 : k₀ * dhi ≤ k * (v ^ 2 - v ^ 6) := by nlinarith
    linarith
  · have t1 : m * (1 - v ^ 6) ≤ m₁ * (1 - α ^ 6) := by
      have : 1 - v ^ 6 ≤ 1 - α ^ 6 := by linarith
      nlinarith
    have t2 : k * (v ^ 2 - v ^ 6) ≤ k₁ * dlo := by nlinarith
    linarith

lemma d_bounds (α β v : ℝ) (hα : 0 < α) (hβ : β ≤ 1) (hv : v ∈ Icc α β) :
    α ^ 2 - β ^ 6 ≤ v ^ 2 - v ^ 6 ∧ v ^ 2 - v ^ 6 ≤ β ^ 2 - α ^ 6 ∧ 0 ≤ v ^ 2 - v ^ 6 := by
  obtain ⟨hv1, hv2⟩ := hv
  have hv0 : 0 ≤ v := by linarith
  have hv1' : v ≤ 1 := le_trans hv2 hβ
  have a2 : α ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ hα.le hv1 2
  have b2 : v ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hv0 hv2 2
  have a6 : α ^ 6 ≤ v ^ 6 := pow_le_pow_left₀ hα.le hv1 6
  have b6 : v ^ 6 ≤ β ^ 6 := pow_le_pow_left₀ hv0 hv2 6
  have v21 : v ^ 2 ≤ 1 := by nlinarith
  have h0 : v ^ 6 ≤ v ^ 2 := by
    have : v ^ 6 = v ^ 2 * (v ^ 2) ^ 2 := by ring
    rw [this]; have : (v ^ 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Chord side condition for a cell and a parameter box, from rational checks. -/
lemma cell_y {m k : ℝ} (m₀ m₁ k₀ k₁ α β dlo p q : ℝ) (hm₀ : 0 ≤ m₀) (hm0 : m₀ ≤ m) (hm1 : m ≤ m₁)
    (hk0 : k₀ ≤ k) (hk1 : k ≤ k₁) (hk₁ : k₁ ≤ 0) (hα : 0 < α) (hβ : β ≤ 1)
    (hdlo : 0 ≤ dlo) (hdl : dlo = 0 ∨ dlo ≤ α ^ 2 - β ^ 6)
    (hp2 : p ^ 2 ≤ m₀ * (1 - β ^ 6) + k₀ * (β ^ 2 - α ^ 6) + α ^ 6)
    (hq2 : m₁ * (1 - α ^ 6) + k₁ * dlo + β ^ 6 ≤ q ^ 2) :
    ∀ v ∈ Icc α β, p ^ 2 ≤ yC m k v ∧ yC m k v ≤ q ^ 2 := by
  intro v hv
  obtain ⟨d1, d2, d3⟩ := d_bounds α β v hα hβ hv
  have hdl' : dlo ≤ v ^ 2 - v ^ 6 := by
    rcases hdl with h | h
    · rw [h]; exact d3
    · linarith
  obtain ⟨y1, y2⟩ := y_box m₀ m₁ k₀ k₁ α β dlo (β ^ 2 - α ^ 6) v hm₀ hm0 hm1 hk0 hk1 hk₁ hα hβ hv
    hdlo hdl' d2
  exact ⟨le_trans hp2 y1, le_trans y2 hq2⟩

/-- Moving the lower limit up decreases the integral. -/
lemma J_shift {m k : ℝ} (hd : Dom m k) (w w' : ℝ) (hw : 0 < w) (hww : w ≤ w') (hw' : w' ≤ 1) :
    ∫ v in w'..1, gC m k v ≤ ∫ v in w..1, gC m k v := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (gC_intInt hd w w' hw hww)
    (gC_intInt hd w' 1 (by linarith) hw')]
  have : 0 ≤ ∫ v in w..w', gC m k v :=
    intervalIntegral.integral_nonneg hww (fun v _ => gC_nonneg m k v)
  linarith

lemma Jpos {m k : ℝ} (hd : Dom m k) (w : ℝ) (hw : 0 < w) (hw1 : w < 1) :
    0 < ∫ v in w..1, gC m k v := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (gC_intInt hd w 1 hw hw1.le) _ hw1
  intro v hv
  unfold gC
  exact div_pos (by norm_num) (Real.sqrt_pos.2 (yC_pos hd v (lt_trans hw hv.1)))

/-- Summing tangent cells. -/
lemma sum_lower {m k : ℝ} (hd : Dom m k) (w h : ℝ) (hw : 0 < w) (hh : 0 < h)
    (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (N : ℕ) :
    ∑ i ∈ Finset.range N, (h * (3 * c i - c i ^ 3 * m)
        - c i ^ 3 * k * ((w + (i + 1) * h) ^ 3 - (w + i * h) ^ 3) / 3
        - c i ^ 3 * (1 - m - k) * ((w + (i + 1) * h) ^ 7 - (w + i * h) ^ 7) / 7)
      ≤ ∫ v in w..w + N * h, gC m k v := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hcell := cell_lower hd (c n) (w + n * h) (w + (n + 1) * h) (by positivity)
      (by nlinarith) (hc n)
    have e1 : w + (n + 1) * h - (w + n * h) = h := by ring
    rw [e1] at hcell
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (gC_intInt hd w (w + n * h) hw (by nlinarith))
      (gC_intInt hd (w + n * h) (w + (n + 1) * h) (by positivity) (by nlinarith))]
    linarith

/-- Summing chord cells. -/
lemma sum_upper {m k : ℝ} (hd : Dom m k) (w h : ℝ) (hw : 0 < w) (hh : 0 < h)
    (p q : ℕ → ℝ) (N : ℕ) (hp : ∀ i < N, 0 < p i) (hq : ∀ i < N, 0 < q i)
    (hy : ∀ i < N, ∀ v ∈ Icc (w + i * h) (w + (i + 1) * h),
      p i ^ 2 ≤ yC m k v ∧ yC m k v ≤ q i ^ 2) :
    ∫ v in w..w + N * h, gC m k v ≤ ∑ i ∈ Finset.range N, (2 * h / p i
      - 2 / (p i * q i * (p i + q i)) * (h * m
        + k * ((w + (i + 1) * h) ^ 3 - (w + i * h) ^ 3) / 3
        + (1 - m - k) * ((w + (i + 1) * h) ^ 7 - (w + i * h) ^ 7) / 7 - h * p i ^ 2)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hcell := cell_upper hd (p n) (q n) (w + n * h) (w + (n + 1) * h) (by positivity)
      (by nlinarith) (hp n (by omega)) (hq n (by omega)) (hy n (by omega))
    have e1 : w + (n + 1) * h - (w + n * h) = h := by ring
    rw [e1] at hcell
    have ih' := ih (fun i hi => hp i (by omega)) (fun i hi => hq i (by omega))
      (fun i hi => hy i (by omega))
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (gC_intInt hd w (w + n * h) hw (by nlinarith))
      (gC_intInt hd (w + n * h) (w + (n + 1) * h) (by positivity) (by nlinarith))]
    linarith

end Work.Cosmography.B1L19CurvedTools
