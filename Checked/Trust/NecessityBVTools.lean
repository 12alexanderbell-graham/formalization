import Checked.Cosmography.B1L19CurvedTools

/-!
# Hypothesis necessity, the curved quartic pair: tools for open models (trust track T2b)

Run 2026-11-25T1228Z. The tools of `Checked.Cosmography.B1L19CurvedTools` (the distance integral of the
inverse square root of `m + k v² + (1 − m − k) v⁶`, its bridge to the comoving distance and its cell
enclosures) on the open domain `DomO`: density between one tenth and one, curvature parameter `k = 1 − Ω₀`
nonnegative and unbounded. The radicand is `m (1 − v⁶) + k (v² − v⁶) + v⁶`, a sum of nonnegative terms on
the unit interval, so it is positive with no lower bound on `k` (`yC_posO`). Copies of the bridge and of the
cell lemmas with `DomO` in place of `Dom` (proofs verbatim), the chord side condition for nonnegative `k`
(`cell_yO`), and the analytic bound for large `k` (`big_k`): the integrand is then within a fixed factor of
`2/(√k · v √(1 − v⁴))`, whose antiderivative `log v² − log(1 + √(1 − v⁴))` is continuous up to `v = 1`.
-/

namespace Checked.Trust.NCBV

open Set Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.B1 Checked.Cosmography.Transverse Checked.Cosmography.B1L19CurvedTools

/-- The open domain: `m ∈ [1/10, 1]`, `k ≥ 0`. -/
structure DomO (m k : ℝ) : Prop where
  m0 : 1 / 10 ≤ m
  m1 : m ≤ 1
  k0 : 0 ≤ k

lemma yC_eqO (m k v : ℝ) : yC m k v = m * (1 - v ^ 6) + k * (v ^ 2 - v ^ 6) + v ^ 6 := by
  unfold yC; ring

lemma yC_posO {m k : ℝ} (h : DomO m k) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) : 0 < yC m k v := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [yC_eqO]
  have hv6 : 0 < v ^ 6 := by positivity
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  have hv62 : v ^ 6 ≤ v ^ 2 := by
    have : v ^ 6 = v ^ 2 * (v ^ 2) ^ 2 := by ring
    rw [this]; have : (v ^ 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hv61 : v ^ 6 ≤ 1 := le_trans hv62 hv2
  nlinarith [mul_nonneg h2 (sub_nonneg.2 hv62)]

/-- The set where the radicand is positive (open; it contains `(0, 1]` on `DomO`). -/
def posSet (m k : ℝ) : Set ℝ := {v | 0 < yC m k v}

lemma posSet_open (m k : ℝ) : IsOpen (posSet m k) :=
  isOpen_lt continuous_const (by unfold yC; fun_prop)

lemma mem_posSet {m k : ℝ} (h : DomO m k) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) : v ∈ posSet m k :=
  yC_posO h v hv hv1

lemma gC_contU (m k : ℝ) : ContinuousOn (gC m k) (posSet m k) := by
  intro v hv
  have hin : 0 < yC m k v := hv
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_const.div
  · exact (by unfold yC; fun_prop : Continuous fun v : ℝ => yC m k v).continuousAt.sqrt
  · exact (Real.sqrt_pos.2 hin).ne'

lemma gC_intIntO {m k : ℝ} (h : DomO m k) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    IntervalIntegrable (gC m k) MeasureTheory.volume α β := by
  apply (gC_contU m k).mono _ |>.intervalIntegrable
  intro z hz; rw [uIcc_of_le hαβ] at hz
  exact mem_posSet h z (lt_of_lt_of_le hα hz.1) (le_trans hz.2 hβ)

/-- Under a law `H = H₀ √(…)` the scale factor is monotone on the interval (the proof of
`Checked.Trust.NCBI.bi_mono`, which uses only that the right side is nonnegative). -/
theorem monoO (R : ℝ → ℝ) (a : ℝ → ℝ) (t t₀ : ℝ)
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t t₀, hubble a s = hubble a t₀ * √(R s)) :
    MonotoneOn a (Icc t t₀) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc t t₀)
  · exact fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hdiff x (Ioo_subset_Icc_self hx)).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx' := Ioo_subset_Icc_self hx
    have h1 := hH x hx'
    have h2 : 0 ≤ hubble a x := by rw [h1]; exact mul_nonneg hH₀.le (Real.sqrt_nonneg _)
    unfold hubble at h2
    exact (div_nonneg_iff.1 h2).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 (hpos x hx')))

/-- Bridge: in a model obeying `H = H₀ √(m(1+z)³ + k(1+z)² + 1 − k − m)` on `[t, t₀]`, the comoving
distance is `J/(H₀ a₀)` with `J = ∫_{√(a/a₀)}^1 gC m k`. -/
theorem comoving_eqO {m k : ℝ} (hd : DomO m k)
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
  have hG : ∀ x, 0 < x → x ≤ 1 → HasDerivAt G (gC m k x) x := by
    intro x hx hx1
    have hsub : uIcc (1:ℝ) x ⊆ posSet m k := by
      intro y hy; rw [uIcc_of_ge hx1] at hy
      exact mem_posSet hd y (lt_of_lt_of_le hx hy.1) hy.2
    have hxU := mem_posSet hd x hx hx1
    exact intervalIntegral.integral_hasDerivAt_right (((gC_contU m k).mono hsub).intervalIntegrable)
      ((gC_contU m k).stronglyMeasurableAtFilter (posSet_open m k) x hxU)
      ((gC_contU m k).continuousAt ((posSet_open m k).mem_nhds hxU))
  have hmono := monoO _ a t t₀ hpos hdiff hH₀ hH
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
    have hW1 : W s ≤ 1 := by
      simp only [hWdef]; rw [Real.sqrt_le_one, div_le_one ha₀]
      exact hmono hs ⟨htt, le_rfl⟩ hs.2
    have hc := ((hG (W s) hWs hW1).comp s hd').div_const (H₀ * a₀)
    have hin := yC_posO hd (W s) hWs hW1
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


/-- Tangent cell bound (no side condition on `c ≥ 0`). -/
lemma cell_lowerO {m k : ℝ} (hd : DomO m k) (c α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 1)
    (hc : 0 ≤ c) :
    (β - α) * (3 * c - c ^ 3 * m) - c ^ 3 * k * (β ^ 3 - α ^ 3) / 3
      - c ^ 3 * (1 - m - k) * (β ^ 7 - α ^ 7) / 7 ≤ ∫ v in α..β, gC m k v := by
  have e := integral_poly26 α β (3 * c - c ^ 3 * m) (c ^ 3 * k) (c ^ 3 * (1 - m - k))
  have hle : ∫ v in α..β, ((3 * c - c ^ 3 * m) - c ^ 3 * k * v ^ 2 - c ^ 3 * (1 - m - k) * v ^ 6)
      ≤ ∫ v in α..β, gC m k v := by
    apply intervalIntegral.integral_mono_on hαβ
      (by apply Continuous.intervalIntegrable; fun_prop) (gC_intIntO hd α β hα hαβ hβ)
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le hα hv.1
    have hin := yC_posO hd v hv0 (le_trans hv.2 hβ)
    have := tangent_le _ c hin hc
    unfold gC yC at *; rw [div_eq_mul_one_div 2]; nlinarith
  rw [e] at hle; linarith

/-- Chord cell bound: `p² ≤ y ≤ q²` on the cell. -/
lemma cell_upperO {m k : ℝ} (hd : DomO m k) (p q α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 1)
    (hp : 0 < p) (hq : 0 < q) (hy : ∀ v ∈ Icc α β, p ^ 2 ≤ yC m k v ∧ yC m k v ≤ q ^ 2) :
    ∫ v in α..β, gC m k v ≤ 2 * (β - α) / p
      - 2 / (p * q * (p + q)) * ((β - α) * m + k * (β ^ 3 - α ^ 3) / 3
        + (1 - m - k) * (β ^ 7 - α ^ 7) / 7 - (β - α) * p ^ 2) := by
  set g := 2 / (p * q * (p + q)) with hg
  have e := integral_poly26 α β (2 / p - g * m + g * p ^ 2) (g * k) (g * (1 - m - k))
  have hle : ∫ v in α..β, gC m k v
      ≤ ∫ v in α..β, ((2 / p - g * m + g * p ^ 2) - g * k * v ^ 2 - g * (1 - m - k) * v ^ 6) := by
    apply intervalIntegral.integral_mono_on hαβ (gC_intIntO hd α β hα hαβ hβ)
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


/-- Moving the lower limit up decreases the integral. -/
lemma J_shiftO {m k : ℝ} (hd : DomO m k) (w w' : ℝ) (hw : 0 < w) (hww : w ≤ w') (hw' : w' ≤ 1) :
    ∫ v in w'..1, gC m k v ≤ ∫ v in w..1, gC m k v := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (gC_intIntO hd w w' hw hww hw')
    (gC_intIntO hd w' 1 (by linarith) hw' le_rfl)]
  have : 0 ≤ ∫ v in w..w', gC m k v :=
    intervalIntegral.integral_nonneg hww (fun v _ => gC_nonneg m k v)
  linarith

lemma JposO {m k : ℝ} (hd : DomO m k) (w : ℝ) (hw : 0 < w) (hw1 : w < 1) :
    0 < ∫ v in w..1, gC m k v := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (gC_intIntO hd w 1 hw hw1.le le_rfl) _ hw1
  intro v hv
  unfold gC
  exact div_pos (by norm_num) (Real.sqrt_pos.2 (yC_posO hd v (lt_trans hw hv.1) hv.2.le))

/-- Summing tangent cells. -/
lemma sum_lowerO {m k : ℝ} (hd : DomO m k) (w h : ℝ) (hw : 0 < w) (hh : 0 < h)
    (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (N : ℕ) (hN : w + N * h ≤ 1) :
    ∑ i ∈ Finset.range N, (h * (3 * c i - c i ^ 3 * m)
        - c i ^ 3 * k * ((w + (i + 1) * h) ^ 3 - (w + i * h) ^ 3) / 3
        - c i ^ 3 * (1 - m - k) * ((w + (i + 1) * h) ^ 7 - (w + i * h) ^ 7) / 7)
      ≤ ∫ v in w..w + N * h, gC m k v := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    push_cast at hN
    have hN' : w + n * h ≤ 1 := by nlinarith
    have hcell := cell_lowerO hd (c n) (w + n * h) (w + (n + 1) * h) (by positivity)
      (by nlinarith) hN (hc n)
    have e1 : w + (n + 1) * h - (w + n * h) = h := by ring
    rw [e1] at hcell
    have ih' := ih hN'
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (gC_intIntO hd w (w + n * h) hw (by nlinarith) hN')
      (gC_intIntO hd (w + n * h) (w + (n + 1) * h) (by positivity) (by nlinarith) hN)]
    linarith

/-- Summing chord cells. -/
lemma sum_upperO {m k : ℝ} (hd : DomO m k) (w h : ℝ) (hw : 0 < w) (hh : 0 < h)
    (p q : ℕ → ℝ) (N : ℕ) (hN : w + N * h ≤ 1) (hp : ∀ i < N, 0 < p i) (hq : ∀ i < N, 0 < q i)
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
    push_cast at hN
    have hN' : w + n * h ≤ 1 := by nlinarith
    have hcell := cell_upperO hd (p n) (q n) (w + n * h) (w + (n + 1) * h) (by positivity)
      (by nlinarith) hN (hp n (by omega)) (hq n (by omega)) (hy n (by omega))
    have e1 : w + (n + 1) * h - (w + n * h) = h := by ring
    rw [e1] at hcell
    have ih' := ih hN' (fun i hi => hp i (by omega)) (fun i hi => hq i (by omega))
      (fun i hi => hy i (by omega))
    push_cast
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (gC_intIntO hd w (w + n * h) hw (by nlinarith) hN')
      (gC_intIntO hd (w + n * h) (w + (n + 1) * h) (by positivity) (by nlinarith) hN)]
    linarith
/-- Chord side condition for a cell and a parameter box with `k ≥ 0`, from rational checks. -/
lemma cell_yO {m k : ℝ} (m₀ m₁ k₀ k₁ α β dlo p q : ℝ) (hm₀ : 0 ≤ m₀) (hm0 : m₀ ≤ m) (hm1 : m ≤ m₁)
    (hk0 : k₀ ≤ k) (hk1 : k ≤ k₁) (hk₀ : 0 ≤ k₀) (hα : 0 < α) (hβ : β ≤ 1)
    (_hdlo : 0 ≤ dlo) (hdl : dlo = 0 ∨ dlo ≤ α ^ 2 - β ^ 6)
    (hp2 : p ^ 2 ≤ m₀ * (1 - β ^ 6) + k₀ * dlo + α ^ 6)
    (hq2 : m₁ * (1 - α ^ 6) + k₁ * (β ^ 2 - α ^ 6) + β ^ 6 ≤ q ^ 2) :
    ∀ v ∈ Icc α β, p ^ 2 ≤ yC m k v ∧ yC m k v ≤ q ^ 2 := by
  intro v hv
  obtain ⟨d1, d2, d3⟩ := d_bounds α β v hα hβ hv
  have hdl' : dlo ≤ v ^ 2 - v ^ 6 := by
    rcases hdl with h | h
    · rw [h]; exact d3
    · linarith
  obtain ⟨hv1, hv2⟩ := hv
  have hv0 : 0 ≤ v := by linarith
  have a6 : α ^ 6 ≤ v ^ 6 := pow_le_pow_left₀ hα.le hv1 6
  have b6 : v ^ 6 ≤ β ^ 6 := pow_le_pow_left₀ hv0 hv2 6
  have b61 : β ^ 6 ≤ 1 := pow_le_one₀ (by linarith) hβ
  rw [yC_eqO]
  constructor
  · have t1 : m₀ * (1 - β ^ 6) ≤ m * (1 - v ^ 6) := by
      have : 1 - β ^ 6 ≤ 1 - v ^ 6 := by linarith
      nlinarith
    have t2 : k₀ * dlo ≤ k * (v ^ 2 - v ^ 6) := by nlinarith
    linarith
  · have t1 : m * (1 - v ^ 6) ≤ m₁ * (1 - α ^ 6) := by
      have : 1 - v ^ 6 ≤ 1 - α ^ 6 := by linarith
      nlinarith
    have t2 : k * (v ^ 2 - v ^ 6) ≤ k₁ * (β ^ 2 - α ^ 6) := by nlinarith
    linarith

/-! ## Large curvature parameter: an antiderivative continuous up to `v = 1` -/

/-- `F v = log v² − log(1 + √(1 − v⁴))`, an antiderivative of `2/(v √(1 − v⁴))` on `(0, 1)`. -/
noncomputable def Fo (v : ℝ) : ℝ := Real.log (v ^ 2) - Real.log (1 + √(1 - v ^ 4))

lemma Fo_deriv (v : ℝ) (hv : 0 < v) (hv1 : v < 1) :
    HasDerivAt Fo (2 / (v * √(1 - v ^ 4))) v := by
  have hv4 : v ^ 4 < 1 := by
    have : v ^ 4 < 1 ^ 4 := pow_lt_pow_left₀ hv1 hv.le (by norm_num)
    simpa using this
  have hr : 0 < 1 - v ^ 4 := by linarith
  set s := √(1 - v ^ 4) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hr
  have hss : s ^ 2 = 1 - v ^ 4 := Real.sq_sqrt hr.le
  have h1 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2)) (2 * v / v ^ 2) v := by
    have := ((hasDerivAt_pow 2 v).log (by positivity))
    simpa using this
  have hsq : HasDerivAt (fun x : ℝ => √(1 - x ^ 4)) ((-(4 * v ^ 3)) / (2 * s)) v := by
    have := ((hasDerivAt_pow 4 v).const_sub 1).sqrt hr.ne'
    simpa [hs] using this
  have h2 : HasDerivAt (fun x : ℝ => Real.log (1 + √(1 - x ^ 4)))
      (((-(4 * v ^ 3)) / (2 * s)) / (1 + s)) v := by
    have := (hsq.const_add 1).log (by positivity)
    simpa [hs] using this
  have := h1.sub h2
  refine this.congr_deriv ?_
  field_simp
  nlinarith [hss]

lemma Fo_cont : ContinuousOn Fo (Icc (1 / 2) 1) := by
  intro v hv
  apply ContinuousAt.continuousWithinAt
  have hv0 : v ^ 2 ≠ 0 := by have := hv.1; positivity
  have h1 : (1 + √(1 - v ^ 4)) ≠ 0 := by positivity
  unfold Fo
  exact ((continuousAt_id.pow 2).log hv0).sub
    ((continuousAt_const.add ((continuousAt_const.sub (continuousAt_id.pow 4)).sqrt)).log h1)

lemma Fo_one : Fo 1 = 0 := by simp [Fo]

/-- On `[v₀, 1]` the integral of `gC` is at most `(F 1 − F v₀)/√k`. -/
lemma big_upper {m k : ℝ} (hd : DomO m k) (hk : 0 < k) (v₀ : ℝ) (hv₀ : 1 / 2 ≤ v₀) (hv₁ : v₀ < 1) :
    ∫ v in v₀..1, gC m k v ≤ (Fo 1 - Fo v₀) / √k := by
  set Φ : ℝ → ℝ := fun x => (∫ v in v₀..x, gC m k v) - (Fo x - Fo v₀) / √k with hΦ
  have hsk : 0 < √k := Real.sqrt_pos.2 hk
  have hcont : ContinuousOn Φ (Icc v₀ 1) := by
    apply ContinuousOn.sub
    · have hii : MeasureTheory.IntegrableOn (gC m k) (uIcc v₀ 1) := by
        rw [uIcc_of_le hv₁.le]
        exact ((gC_contU m k).mono (fun z hz => mem_posSet hd z (by linarith [hz.1]) hz.2)).integrableOn_Icc
      exact (intervalIntegral.continuousOn_primitive_interval hii).mono (by
        rw [uIcc_of_le hv₁.le])
    · exact ((Fo_cont.mono (Icc_subset_Icc_left hv₀)).sub continuousOn_const).div_const _
  have hderiv : ∀ x ∈ Ioo v₀ 1, HasDerivAt Φ (gC m k x - 2 / (x * √(1 - x ^ 4)) / √k) x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hxU := mem_posSet hd x hx0 hx.2.le
    have hsub : uIcc v₀ x ⊆ posSet m k := by
      intro z hz; rw [uIcc_of_le hx.1.le] at hz
      exact mem_posSet hd z (by linarith [hz.1]) (le_trans hz.2 hx.2.le)
    have hI := intervalIntegral.integral_hasDerivAt_right
      (((gC_contU m k).mono hsub).intervalIntegrable)
      ((gC_contU m k).stronglyMeasurableAtFilter (posSet_open m k) x hxU)
      ((gC_contU m k).continuousAt ((posSet_open m k).mem_nhds hxU))
    exact hI.sub (((Fo_deriv x hx0 hx.2).sub_const (Fo v₀)).div_const √k)
  have hanti : AntitoneOn Φ (Icc v₀ 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc v₀ 1) hcont
    · intro x hx; rw [interior_Icc] at hx; exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x hx).deriv]
      have hx0 : 0 < x := by linarith [hx.1]
      have hx4 : x ^ 4 < 1 := by
        have : x ^ 4 < 1 ^ 4 := pow_lt_pow_left₀ hx.2 hx0.le (by norm_num)
        simpa using this
      have hr : 0 < 1 - x ^ 4 := by linarith
      have hs0 : 0 < √(1 - x ^ 4) := Real.sqrt_pos.2 hr
      -- y ≥ k x² (1 − x⁴)
      have hy : k * (x * √(1 - x ^ 4)) ^ 2 ≤ yC m k x := by
        rw [mul_pow, Real.sq_sqrt hr.le, yC_eqO]
        have hx1 : x ≤ 1 := hx.2.le
        have hx6 : x ^ 6 ≤ 1 := pow_le_one₀ hx0.le hx1
        have : m * (1 - x ^ 6) ≥ 0 := mul_nonneg (by linarith [hd.m0]) (by linarith)
        nlinarith [pow_pos hx0 6]
      have hsq : √k * (x * √(1 - x ^ 4)) ≤ √(yC m k x) := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ x * √(1 - x ^ 4)), ← Real.sqrt_mul hk.le]
        exact Real.sqrt_le_sqrt hy
      have hpos : 0 < √k * (x * √(1 - x ^ 4)) := by positivity
      have : gC m k x ≤ 2 / (x * √(1 - x ^ 4)) / √k := by
        unfold gC
        rw [div_div, div_le_div_iff_of_pos_left (by norm_num) (lt_of_lt_of_le hpos hsq) (by positivity)]
        linarith
      linarith
  have h1 := hanti ⟨le_rfl, hv₁.le⟩ ⟨hv₁.le, le_rfl⟩ hv₁.le
  simp only [hΦ, intervalIntegral.integral_same, sub_self, zero_div] at h1
  linarith

/-- On `[α, β] ⊆ (0, 1)` where `v² − v⁶ ≥ 1/c`, the integral of `gC` is at least
`(F β − F α)/√(k + c)`. -/
lemma big_lower {m k : ℝ} (hd : DomO m k) (c α β : ℝ) (hc : 0 < c) (hα : 0 < α) (hαβ : α ≤ β)
    (hβ : β < 1) (he : ∀ v ∈ Icc α β, 1 ≤ c * (v ^ 2 - v ^ 6)) :
    (Fo β - Fo α) / √(k + c) ≤ ∫ v in α..β, gC m k v := by
  have hkc : 0 < k + c := by linarith [hd.k0]
  have hskc : 0 < √(k + c) := Real.sqrt_pos.2 hkc
  have hF : ∀ x ∈ uIcc α β, HasDerivAt (fun x => Fo x / √(k + c)) (2 / (x * √(1 - x ^ 4)) / √(k + c)) x := by
    intro x hx; rw [uIcc_of_le hαβ] at hx
    exact (Fo_deriv x (by linarith [hx.1]) (lt_of_le_of_lt hx.2 hβ)).div_const _
  have hcontg : ContinuousOn (fun x => 2 / (x * √(1 - x ^ 4)) / √(k + c)) (uIcc α β) := by
    intro x hx; rw [uIcc_of_le hαβ] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hx4 : x ^ 4 < 1 := by
      have : x ^ 4 < 1 ^ 4 := pow_lt_pow_left₀ (lt_of_le_of_lt hx.2 hβ) hx0.le (by norm_num)
      simpa using this
    have : x * √(1 - x ^ 4) ≠ 0 := (mul_pos hx0 (Real.sqrt_pos.2 (by linarith))).ne'
    apply ContinuousAt.continuousWithinAt
    exact ((continuousAt_const.div (continuousAt_id.mul ((continuousAt_const.sub
      (continuousAt_id.pow 4)).sqrt)) this).div_const _)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcontg.intervalIntegrable
  have heq : (Fo β - Fo α) / √(k + c) = Fo β / √(k + c) - Fo α / √(k + c) := by ring
  rw [heq, ← hint]
  apply intervalIntegral.integral_mono_on hαβ hcontg.intervalIntegrable
    (gC_intIntO hd α β hα hαβ hβ.le)
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 := lt_of_le_of_lt hx.2 hβ
  have hx4 : x ^ 4 < 1 := by
    have : x ^ 4 < 1 ^ 4 := pow_lt_pow_left₀ hx1 hx0.le (by norm_num)
    simpa using this
  have hr : 0 < 1 - x ^ 4 := by linarith
  have hin := yC_posO hd x hx0 hx1.le
  have hy : yC m k x ≤ (k + c) * (x * √(1 - x ^ 4)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hr.le, yC_eqO]
    have hex := he x hx
    have hx6 : x ^ 6 ≤ 1 := pow_le_one₀ hx0.le hx1.le
    have hm : m * (1 - x ^ 6) + x ^ 6 ≤ 1 := by nlinarith [hd.m1]
    have e : x ^ 2 * (1 - x ^ 4) = x ^ 2 - x ^ 6 := by ring
    rw [e]; nlinarith
  have hsq : √(yC m k x) ≤ √(k + c) * (x * √(1 - x ^ 4)) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ x * √(1 - x ^ 4)), ← Real.sqrt_mul hkc.le]
    exact Real.sqrt_le_sqrt hy
  unfold gC
  rw [div_div]
  apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hin)
  linarith [mul_comm (√(k + c)) (x * √(1 - x ^ 4))]

end Checked.Trust.NCBV
