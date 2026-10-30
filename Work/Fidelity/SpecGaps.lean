import Work.Fidelity.LumDistSpec
import Work.Fidelity.MoreSpecs

/-!
# Spec gaps: wrong definitions that satisfy the fidelity specifications

Adversarial companion to `Work/Fidelity/LumDistSpec.lean` and `Work/Fidelity/MoreSpecs.lean`.

* `LumDistSpec` has gaps. Its only anchors are flat de Sitter, Milne and the *static* closed
  universe (plus `a ↦ c a` rescaling). Consequently:
  - the closed (`K > 0`) branch is only ever tested at `z = 0`, so every factor of `(1 + z)`
    there is invisible (`gap_closedNoZ`);
  - the flat and open anchors both have constant deceleration parameter (`q = −1`, `q = 0`),
    and the second-order cosmographic series `d_L = (z/H₀)(1 + (1 − q₀) z/2)` is *exact* on
    both (`gap_cosmo2`);
  - the only open anchor (Milne) has `Ω_k = 1`, so `Ω_k` vs `√Ω_k` is invisible (`gap_omegaK`);
  - artificially, any rescaling-invariant correction vanishing at `q₀ ∈ {−1, 0}` survives
    (`gap_qq1`).
  Each gap comes with a Lean proof that it meets `LumDistSpec` and a Lean proof that it
  differs from `lumDist` at a concrete admissible input (`a > 0` smooth, `t < t₀`).
* `DecelSpec` and `AngDistSpec` have no gaps on the admissible domain: their `formula`,
  resp. `flat`/`closed`/`open` + `rescale` anchors determine the function completely there
  (`decelSpec_pins`, `angDistSpec_pins`).
-/

namespace Work.Fidelity.Gaps

open Real Filter Topology Checked.Cosmography Checked.Cosmography.BambaY
open Checked.Cosmography.BambaK Checked.Cosmography.BambaA Checked.Cosmography.Transverse
open Work.Fidelity

/-! ## Helpers -/

lemma pos_iff_sq_mul (c K : ℝ) (hc : 0 < c) : 0 < c ^ 2 * K ↔ 0 < K := by
  have : 0 < c ^ 2 := by positivity
  constructor
  · intro h; by_contra hn; push Not at hn; nlinarith
  · intro h; positivity

lemma neg_iff_sq_mul (c K : ℝ) (hc : 0 < c) : c ^ 2 * K < 0 ↔ K < 0 := by
  have : 0 < c ^ 2 := by positivity
  constructor
  · intro h; by_contra hn; push Not at hn; nlinarith
  · intro h; nlinarith

lemma decel_rescale (c : ℝ) (hc : 0 < c) (a : ℝ → ℝ) (t : ℝ) :
    decel (fun s => c * a s) t = decel a t := by
  unfold decel
  rw [deriv_const_mul_field', deriv_const_mul_field]
  have : c ≠ 0 := hc.ne'
  by_cases hd : deriv a t = 0
  · simp [hd]
  · field_simp

lemma decel_exp (t : ℝ) : decel Real.exp t = -1 := by
  simp only [decel, Real.deriv_exp]
  have := Real.exp_pos t
  field_simp

lemma decel_id (t : ℝ) : decel id t = 0 := by
  simp [decel]

lemma decel_const (R t : ℝ) : decel (fun _ => R) t = 0 := by
  simp [decel]

lemma hubble_id_one : hubble id 1 = 1 := by
  simp [hubble]

lemma hubble_exp_zero : hubble Real.exp 0 = 1 := by
  simp [hubble, Real.deriv_exp]

/-! ## (A1) Closed branch without `(1 + z)` -/

/-- **(A) gap.** A three-branch definition whose closed (`K > 0`) branch forgets the `(1+z)`
factor (it returns the transverse comoving distance `d_M = a₀ S_K(χ)`). The only closed anchor
is the static universe, where `z = 0`, so the omission is invisible.
Distinguishing input: `K = 1`, `a = exp`, `t₀ = 0`, `t = −log 2` (`z = 1`, `χ = 1`):
true `d_L = 2 sin 1`, `gClosedNoZ = sin 1` (`gap_closedNoZ_differs`). -/
noncomputable def gClosedNoZ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  if 0 < K then a t₀ * transverse K (comoving a t₀ t) else lumDist K a t₀ t

theorem gap_closedNoZ : LumDistSpec gClosedNoZ where
  deSitter t ht := by
    simp only [gClosedNoZ, lt_irrefl, ite_false]; exact lumDist_meets_spec.deSitter t ht
  milne t h1 h2 := by
    simp only [gClosedNoZ, show ¬ (0 : ℝ) < -1 by norm_num, ite_false]
    exact lumDist_meets_spec.milne t h1 h2
  staticClosed t₀ t _ := by simp [gClosedNoZ, transverse, comoving_one]
  rescale c hc K a t₀ t := by
    simp only [gClosedNoZ, pos_iff_sq_mul c K hc]
    split_ifs
    · rw [comoving_rescale c hc, transverse_rescale c K _ hc]; field_simp
    · exact lumDist_meets_spec.rescale c hc K a t₀ t

theorem gap_closedNoZ_differs :
    gClosedNoZ 1 Real.exp 0 (-Real.log 2) ≠ lumDist 1 Real.exp 0 (-Real.log 2) := by
  simp only [gClosedNoZ, lumDist, transverse, com_exp, red_exp, one_pos, ite_true,
    Real.sqrt_one, one_mul, div_one, Real.exp_zero]
  have := Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [Real.two_le_pi])
  intro h; linarith

/-! ## (A2) Second-order cosmography -/

/-- Second-order cosmographic luminosity distance `(z/H₀)(1 + (1 − q₀) z/2)`. -/
noncomputable def cosmo2 (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  redshift a t₀ t / hubble a t₀ * (1 + (1 - decel a t₀) * redshift a t₀ t / 2)

/-- **(A) gap.** For `K ≤ 0` the definition uses the truncated cosmographic series
`d_L = (z/H₀)(1 + (1 − q₀) z/2)` (ignores curvature and jerk; the repo's own cosmography
works with exactly this series). It is *exact* for de Sitter (`q₀ = −1`: `z(1+z)/H₀`) and for
Milne (`q₀ = 0`: `z(1+z/2)/H₀`), and it is rescaling invariant, so it meets the spec; the
closed branch is the true one (the static anchor has `H₀ = 0`). Wrong for every model with
time-dependent `q` (matter, radiation, ΛCDM).
Distinguishing input: `K = 0`, `a = id` (coasting flat), `t₀ = 1`, `t = 1/2` (`z = 1`, `H₀ = 1`,
`q₀ = 0`): true `d_L = 2 log 2 ≈ 1.386`, `gCosmo2 = 3/2` (`gap_cosmo2_differs`). -/
noncomputable def gCosmo2 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  if 0 < K then lumDist K a t₀ t else cosmo2 a t₀ t

theorem gap_cosmo2 : LumDistSpec gCosmo2 where
  deSitter t _ := by
    simp only [gCosmo2, lt_irrefl, ite_false, cosmo2, hubble_exp_zero, decel_exp, redshift,
      Real.exp_zero]
    rw [Real.exp_neg]; field_simp; ring
  milne t ht _ := by
    simp only [gCosmo2, show ¬ (0 : ℝ) < -1 by norm_num, ite_false, cosmo2, hubble_id_one,
      decel_id, redshift, id]
    field_simp; ring
  staticClosed t₀ t h := by
    simp only [gCosmo2, one_pos, ite_true]; exact lumDist_meets_spec.staticClosed t₀ t h
  rescale c hc K a t₀ t := by
    simp only [gCosmo2, pos_iff_sq_mul c K hc]
    split_ifs
    · exact lumDist_meets_spec.rescale c hc K a t₀ t
    · simp only [cosmo2, redshift_rescale c hc, ms_hubble_rescale c hc.ne', decel_rescale c hc]

theorem gap_cosmo2_differs : gCosmo2 0 id 1 (1 / 2) ≠ lumDist 0 id 1 (1 / 2) := by
  simp only [gCosmo2, lt_irrefl, ite_false, cosmo2, hubble_id_one, decel_id, red_id_half,
    lumDist, transverse, com_id_half, id]
  have := Real.log_two_lt_d9
  norm_num
  intro h; nlinarith

/-! ## (A3) `Ω_k` instead of `√Ω_k` in the open branch -/

/-- `Ω_k = −K/(a₀H₀)²`. -/
noncomputable def omegaK (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ :=
  -K / (a t₀ * hubble a t₀) ^ 2

/-- **(A) gap.** Open branch written in the Hogg form
`d_L = (1+z) sinh(√Ω_k · a₀H₀χ)/(H₀√Ω_k)` but with both square roots dropped
(`Ω_k` for `√Ω_k`). `Ω_k` is rescaling invariant, and the only open anchor (Milne) has
`Ω_k = 1` exactly, so the error is invisible.
Distinguishing input: `K = −4`, `a = exp`, `t₀ = 0`, `t = −log 2` (`Ω_k = 4`, `χ = 1`, `z = 1`):
true `d_L = sinh 2 ≈ 3.63`, `gOmegaK = sinh 4/2 = sinh 2 cosh 2 ≈ 13.6`
(`gap_omegaK_differs`). -/
noncomputable def gOmegaK (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  if K < 0 then
    (1 + redshift a t₀ t) *
      Real.sinh (omegaK K a t₀ * (a t₀ * hubble a t₀) * comoving a t₀ t) /
      (hubble a t₀ * omegaK K a t₀)
  else lumDist K a t₀ t

lemma omegaK_rescale (c : ℝ) (hc : 0 < c) (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) :
    omegaK (c ^ 2 * K) (fun s => c * a s) t₀ = omegaK K a t₀ := by
  unfold omegaK
  rw [ms_hubble_rescale c hc.ne', show -(c ^ 2 * K) = c ^ 2 * (-K) by ring,
    show (c * a t₀ * hubble a t₀) ^ 2 = c ^ 2 * (a t₀ * hubble a t₀) ^ 2 by ring,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc.ne')]

theorem gap_omegaK : LumDistSpec gOmegaK where
  deSitter t ht := by
    simp only [gOmegaK, lt_irrefl, ite_false]; exact lumDist_meets_spec.deSitter t ht
  milne t ht _ := by
    have hO : omegaK (-1) id 1 = 1 := by simp [omegaK, hubble_id_one]
    simp only [gOmegaK, show (-1 : ℝ) < 0 by norm_num, ite_true, hO, hubble_id_one,
      comoving_id t ht, redshift, id]
    norm_num
    rw [sinh_log _ (by positivity)]
    field_simp; ring
  staticClosed t₀ t h := by
    simp only [gOmegaK, show ¬ (1 : ℝ) < 0 by norm_num, ite_false]
    exact lumDist_meets_spec.staticClosed t₀ t h
  rescale c hc K a t₀ t := by
    simp only [gOmegaK, neg_iff_sq_mul c K hc]
    split_ifs
    · rw [omegaK_rescale c hc, ms_hubble_rescale c hc.ne', redshift_rescale c hc,
        comoving_rescale c hc]
      congr 3
      field_simp
    · exact lumDist_meets_spec.rescale c hc K a t₀ t

theorem gap_omegaK_differs :
    gOmegaK (-4) Real.exp 0 (-Real.log 2) ≠ lumDist (-4) Real.exp 0 (-Real.log 2) := by
  have hO : omegaK (-4) Real.exp 0 = 4 := by simp [omegaK, hubble_exp_zero]
  have hs : Real.sqrt (-(-4 : ℝ)) = 2 := by
    rw [neg_neg, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [gOmegaK, lumDist, transverse, show (-4 : ℝ) < 0 by norm_num, ite_true,
    show ¬ (0 : ℝ) < -4 by norm_num, ite_false, hO, hubble_exp_zero, com_exp, red_exp, hs,
    Real.exp_zero]
  rw [show (4 : ℝ) * (1 * 1) * 1 = 2 * 2 by norm_num, Real.sinh_two_mul]
  have h1 : 0 < Real.sinh 2 := Real.sinh_pos_iff.2 (by norm_num)
  have h2 : 1 < Real.cosh 2 := Real.one_lt_cosh.2 (by norm_num)
  intro h
  field_simp at h
  nlinarith

/-! ## (B) Artificial: a correction vanishing at `q₀ ∈ {−1, 0}` -/

/-- **(B) gap.** `d_L + q₀(1 + q₀) z`: the correction is rescaling invariant and vanishes for
de Sitter (`q₀ = −1`), Milne (`q₀ = 0`) and the static universe (Lean's `q₀ = 0/0 = 0`).
Distinguishing input: `K = 0`, `a = s²`, `t₀ = 1`, `t = 1/2` (`q₀ = −1/2`, `z = 3`): the
correction is `−3/4` (`gap_qq1_differs`). -/
noncomputable def gQQ1 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDist K a t₀ t + decel a t₀ * (1 + decel a t₀) * redshift a t₀ t

theorem gap_qq1 : LumDistSpec gQQ1 where
  deSitter t ht := by
    simp only [gQQ1, decel_exp]; rw [lumDist_meets_spec.deSitter t ht]; ring
  milne t h1 h2 := by
    simp only [gQQ1, decel_id]; rw [lumDist_meets_spec.milne t h1 h2]; ring
  staticClosed t₀ t h := by
    simp only [gQQ1, decel_const]; rw [lumDist_meets_spec.staticClosed t₀ t h]; ring
  rescale c hc K a t₀ t := by
    simp only [gQQ1, decel_rescale c hc, redshift_rescale c hc,
      lumDist_meets_spec.rescale c hc K a t₀ t]

lemma decel_sq_one : decel (fun s : ℝ => s ^ 2) 1 = -1 / 2 := by
  have h1 : deriv (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
    funext s; simp
  simp only [decel, h1]
  simp
  norm_num

theorem gap_qq1_differs :
    gQQ1 0 (fun s => s ^ 2) 1 (1 / 2) - lumDist 0 (fun s => s ^ 2) 1 (1 / 2) = -3 / 4 := by
  simp only [gQQ1, decel_sq_one, redshift]
  norm_num

/-! ## `DecelSpec` and `AngDistSpec` pin the definition on the admissible domain -/

/-- No gap in `DecelSpec`: on every positive scale factor, twice differentiable at `t` with
`ȧ(t) ≠ 0`, any `Q` meeting the spec equals `decel`. -/
theorem decelSpec_pins (Q : (ℝ → ℝ) → ℝ → ℝ) (h : DecelSpec Q) (a a' : ℝ → ℝ) (a'' t : ℝ)
    (h1 : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) (h2 : HasDerivAt a' a'' t) (ha : 0 < a t)
    (hd : a' t ≠ 0) : Q a t = decel a t := by
  rw [h.formula a a' a'' t h1 h2 ha hd, ms_decel_formula a a' a'' t h1 h2]

lemma int_div_const (a : ℝ → ℝ) (c t₀ t : ℝ) :
    (∫ s in t..t₀, 1 / (a s / c)) = c * comoving a t₀ t := by
  unfold comoving
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext s; rw [one_div_div, div_eq_mul_one_div]

/-- No gap in `AngDistSpec`: for every curvature `K`, every scale factor positive and
continuous on `[t, t₀]`, and `t ≤ t₀`, any `D` meeting the spec equals `angDist`
(`flat`/`closed`/`open` fix `K ∈ {0, ±1}`, `rescale` transports them to every `K`). -/
theorem angDistSpec_pins (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : AngDistSpec D) (K : ℝ)
    (a : ℝ → ℝ) (t₀ t : ℝ) (htt : t ≤ t₀) (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s)
    (hcont : ContinuousOn a (Set.Icc t t₀)) : D K a t₀ t = angDist K a t₀ t := by
  obtain ⟨h0, h00⟩ := ms_ends htt hpos
  rw [ms_angDist_eq K a t₀ t h0 h00]
  rcases lt_trichotomy K 0 with hK | rfl | hK
  · set c := Real.sqrt (-K) with hcdef
    have hc : 0 < c := Real.sqrt_pos.2 (by linarith)
    have e1 : c ^ 2 * (-1) = K := by rw [hcdef, Real.sq_sqrt (by linarith)]; ring
    have hab : (fun s => c * (a s / c)) = a := by funext s; field_simp
    have hb : ∀ s ∈ Set.Icc t t₀, 0 < a s / c := fun s hs => div_pos (hpos s hs) hc
    calc D K a t₀ t = D (c ^ 2 * (-1)) (fun s => c * (a s / c)) t₀ t := by rw [e1, hab]
      _ = D (-1) (fun s => a s / c) t₀ t := h.rescale c hc (-1) (fun s => a s / c) t₀ t
      _ = a t / c * Real.sinh (∫ s in t..t₀, 1 / (a s / c)) :=
          h.open (fun s => a s / c) t₀ t htt hb (hcont.div_const c)
      _ = a t * transverse K (comoving a t₀ t) := by
          rw [int_div_const]
          simp only [transverse, not_lt.2 hK.le, hK, ite_false, ite_true, ← hcdef]
          field_simp
  · rw [h.flat a t₀ t htt hpos hcont]; simp [transverse, comoving]
  · set c := Real.sqrt K with hcdef
    have hc : 0 < c := Real.sqrt_pos.2 hK
    have e1 : c ^ 2 * 1 = K := by rw [hcdef, Real.sq_sqrt hK.le]; ring
    have hab : (fun s => c * (a s / c)) = a := by funext s; field_simp
    have hb : ∀ s ∈ Set.Icc t t₀, 0 < a s / c := fun s hs => div_pos (hpos s hs) hc
    calc D K a t₀ t = D (c ^ 2 * 1) (fun s => c * (a s / c)) t₀ t := by rw [e1, hab]
      _ = D 1 (fun s => a s / c) t₀ t := h.rescale c hc 1 (fun s => a s / c) t₀ t
      _ = a t / c * Real.sin (∫ s in t..t₀, 1 / (a s / c)) :=
          h.closed (fun s => a s / c) t₀ t htt hb (hcont.div_const c)
      _ = a t * transverse K (comoving a t₀ t) := by
          rw [int_div_const]
          simp only [transverse, hK, ite_true, ← hcdef]
          field_simp

end Work.Fidelity.Gaps
