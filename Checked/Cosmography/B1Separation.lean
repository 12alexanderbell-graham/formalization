import Checked.Cosmography.B1Truncation

/-!
# B1 two-point separation and direction: a cubic log-polynomial that agrees with exact ΛCDM at z = 3 and z = 7 cannot sit at the ΛCDM point, and lies on one side of it

**Question (TARGETS.md, B1; STATE "B1 separation theorem").** Risaliti & Lusso 2019 (Nat. Astron.
3, 272; arXiv:1811.02590) and Lusso et al. 2019 (A&A 628, L4; arXiv:1907.07692) fit the Hubble
diagram with `D_L = ln(10)(c/H₀)(x + a₂x² + a₃x³)`, `x = log₁₀(1+z)`, and report a > 4σ distance
of the fitted `(a₂, a₃)` from the point flat ΛCDM implies (`lusA2 Ω`, `lusA3 Ω`, Lusso et al. 2019
Eq. (8)). If the universe is exactly flat ΛCDM, how far from the ΛCDM point, and on which side,
must a cubic lie whose distance modulus agrees with the exact one at z = 3 and z = 7?

**Statement.** For every flat ΛCDM model with `Ω ∈ [0.2, 0.4]` (same hypotheses as
`Checked.Cosmography.B1.cubic_shape_miss`: the Friedmann law holds on the whole interval back to a
source at `z = 7`), and every cubic log-polynomial — any coefficients `a₂, a₃`, any normalisation
`H > 0`, any magnitude offset `c` — whose distance modulus agrees with the exact one up to the
common offset `c` within 0.05 mag at both `z = 3` and `z = 7`:
`(a₂ − a₂^ΛCDM)² + (a₃ − a₃^ΛCDM)² > (5/4)²`.
In words: agreeing with exact ΛCDM, up to a common offset, within 0.05 mag at z = 3 and at z = 7
forces the coefficients more than 1.25 (Euclidean, in the papers' (a₂, a₃) units) away from the
ΛCDM-implied point (`cubic_separation`), on the side `a₂ − a₂^ΛCDM < 7 log₁₀2 (a₃ − a₃^ΛCDM)`
(`cubic_direction`). The condition is one scalar constraint on the ratio of the polynomial at the
two redshifts (H and c drop out); it says nothing about other redshifts and is a two-point
criterion, not a statement about least-squares fits over a data range (referee,
`runs/2026-10-31T0828Z/referee_b1sep.md`: the true minimum distance is 1.98; least-squares cubic
fits to exact ΛCDM over z ≤ 5 do not meet the 0.1 mag shape condition). The mechanism (a cubic
matching ΛCDM sits far from the Taylor point) is Banerjee et al. 2021 (arXiv:2009.04109, mock fits);
new here are the certified Ω-uniform, offset-free bounds and the direction.

Positivity of the polynomial distance at both redshifts is assumed (a negative distance has no
distance modulus; `Real.logb` would silently take the absolute value).

Conventions: as `Checked.Cosmography.B1` (`c = 1`, `hubble a t = ȧ/a`,
`redshift a t₀ t = a(t₀)/a(t) − 1`, `lumDistFlat`; distance-modulus difference `5 log₁₀(d/d')`).

FROZEN (annex 40.1) in run 2026-10-31T0828Z before proof work (8be0a7b, 1229815).
PROMOTED from `Work/Cosmography/B1Separation.lean` (statements byte-identical). Audit:
`runs/2026-10-31T0828Z/audit_b1sep.md`; blind restatements closed in `Work/Cosmography/B1SepAudit.lean`;
non-vacuity witness `Checked/Cosmography/B1SepWitness.lean`.
-/

namespace Checked.Cosmography.B1Sep

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-! ## Proof tools (not part of the frozen statement) -/

lemma log_ten_ge : (10 * 0.6931471803 - 24 / 1000) / 3 ≤ Real.log 10 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1000 / 1024 by norm_num)
  have h2 : Real.log (1000 / 1024) = 3 * Real.log 10 - 10 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (1000:ℝ) = 10 ^ 3 by norm_num, show (1024:ℝ) = 2 ^ 10 by norm_num,
      Real.log_pow, Real.log_pow]; push_cast; ring
  rw [h2] at h1
  have h3 : ((1000:ℝ) / 1024)⁻¹ = 1024 / 1000 := by norm_num
  rw [h3] at h1
  linarith [Real.log_two_gt_d9]

/-- Cauchy–Schwarz step: a linear lower bound `m ≤ d₂ g₂ + d₃ g₃` with `g` bounded forces
`(l d₂, l² d₃)` out of the disc of radius `δ`. -/
lemma core (δ ρ m ℓ l d₂ d₃ : ℝ) (hl : (10 * 0.6931471803 - 24 / 1000) / 3 ≤ l)
    (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ 0.6931471808) (hm : 0 < m)
    (h : m ≤ d₂ * ((9 - 4 * ρ) * ℓ ^ 2) + d₃ * ((27 - 8 * ρ) * ℓ ^ 3))
    (hD : δ ^ 2 * ((9 - 4 * ρ) ^ 2 * 0.6931471808 ^ 4 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * ρ) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4) < m ^ 2) :
    δ ^ 2 < (l * d₂) ^ 2 + (l ^ 2 * d₃) ^ 2 := by
  set L0 : ℝ := (10 * 0.6931471803 - 24 / 1000) / 3 with hL0
  have hL0p : 0 < L0 := by norm_num [hL0]
  have hl0 : 0 < l := lt_of_lt_of_le hL0p hl
  set G₂ := (9 - 4 * ρ) * ℓ ^ 2 / l with hG₂
  set G₃ := (27 - 8 * ρ) * ℓ ^ 3 / l ^ 2 with hG₃
  have hsum : d₂ * ((9 - 4 * ρ) * ℓ ^ 2) + d₃ * ((27 - 8 * ρ) * ℓ ^ 3)
      = (l * d₂) * G₂ + (l ^ 2 * d₃) * G₃ := by
    rw [hG₂, hG₃]; field_simp
  have hcs : ((l * d₂) * G₂ + (l ^ 2 * d₃) * G₃) ^ 2
      ≤ ((l * d₂) ^ 2 + (l ^ 2 * d₃) ^ 2) * (G₂ ^ 2 + G₃ ^ 2) := by
    nlinarith [sq_nonneg ((l * d₂) * G₃ - (l ^ 2 * d₃) * G₂)]
  have hℓ4 : ℓ ^ 4 ≤ 0.6931471808 ^ 4 := pow_le_pow_left₀ hℓ0.le hℓ 4
  have hℓ6 : ℓ ^ 6 ≤ 0.6931471808 ^ 6 := pow_le_pow_left₀ hℓ0.le hℓ 6
  have hl2 : L0 ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ hL0p.le hl 2
  have hl4 : L0 ^ 4 ≤ l ^ 4 := pow_le_pow_left₀ hL0p.le hl 4
  have hG₂b : G₂ ^ 2 ≤ (9 - 4 * ρ) ^ 2 * 0.6931471808 ^ 4 / L0 ^ 2 := by
    have e : G₂ ^ 2 = (9 - 4 * ρ) ^ 2 * ℓ ^ 4 / l ^ 2 := by rw [hG₂]; field_simp
    rw [e]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hℓ4 (sq_nonneg _))
      (by positivity) hl2
  have hG₃b : G₃ ^ 2 ≤ (27 - 8 * ρ) ^ 2 * 0.6931471808 ^ 6 / L0 ^ 4 := by
    have e : G₃ ^ 2 = (27 - 8 * ρ) ^ 2 * ℓ ^ 6 / l ^ 4 := by rw [hG₃]; field_simp
    rw [e]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hℓ6 (sq_nonneg _))
      (by positivity) hl4
  by_contra hcon
  push Not at hcon
  rw [hsum] at h
  have hm2 : m ^ 2 ≤ ((l * d₂) * G₂ + (l ^ 2 * d₃) * G₃) ^ 2 := pow_le_pow_left₀ hm.le h 2
  have hS : 0 ≤ (l * d₂) ^ 2 + (l ^ 2 * d₃) ^ 2 := by positivity
  have hGG : G₂ ^ 2 + G₃ ^ 2 ≤ (9 - 4 * ρ) ^ 2 * 0.6931471808 ^ 4 / L0 ^ 2
      + (27 - 8 * ρ) ^ 2 * 0.6931471808 ^ 6 / L0 ^ 4 := add_le_add hG₂b hG₃b
  have h1 : ((l * d₂) ^ 2 + (l ^ 2 * d₃) ^ 2) * (G₂ ^ 2 + G₃ ^ 2)
      ≤ δ ^ 2 * ((9 - 4 * ρ) ^ 2 * 0.6931471808 ^ 4 / L0 ^ 2
        + (27 - 8 * ρ) ^ 2 * 0.6931471808 ^ 6 / L0 ^ 4) :=
    mul_le_mul hcon hGG (by positivity) (sq_nonneg _)
  linarith

/-- `ln 10·(x + a₂x² + a₃x³)` for general coefficients, in `u = ln(1+z)`. -/
lemma poly_gen (a₂ a₃ H z : ℝ) (hH : H ≠ 0) :
    logPolyDL3 a₂ a₃ H z = (Real.log (1 + z) + a₂ / Real.log 10 * Real.log (1 + z) ^ 2
      + a₃ / Real.log 10 ^ 2 * Real.log (1 + z) ^ 3) / H := by
  have hl : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold logPolyDL3 Real.logb
  field_simp

/-- One Ω-subinterval: from the matching inequality `2 J₇ (1−κ) P₃ ≤ J₃ P₇` and enclosures of
`J₃, J₇`, the separation follows. -/
lemma case_step (Ω a₂ a₃ J3 J7 L U ρ m : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (hP3 : 0 < 2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3)
    (hmatch : 2 * J7 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) *
        (2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3)
      ≤ J3 * (3 * Real.log 2 + a₂ / Real.log 10 * (3 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2) ^ 3))
    (hJ3 : 0 < J3) (hL : L ≤ J7) (hU : J3 ≤ U) (hρ : 0 ≤ ρ)
    (hlin : ρ * U ≤ 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)))
    (hmq : m ≤ ρ * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808)) (hm : 0 < m)
    (hD : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * ρ) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * ρ) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4) < m ^ 2) :
    (5 / 4) ^ 2 < (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 := by
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  set P3 := 2 * ℓ + a₂ / l * (2 * ℓ) ^ 2 + a₃ / l ^ 2 * (2 * ℓ) ^ 3 with hP3def
  set P7 := 3 * ℓ + a₂ / l * (3 * ℓ) ^ 2 + a₃ / l ^ 2 * (3 * ℓ) ^ 3 with hP7def
  have hκ : 0 < 1 - 1 / 10 / 5 * (10 / 3 * (0.6931471808 : ℝ)) := by norm_num
  -- P₇ ≥ ρ P₃
  have h1 : ρ * J3 * P3 ≤ J3 * P7 := by
    have e1 : ρ * J3 * P3 ≤ ρ * U * P3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU hρ) hP3.le
    have e2 : ρ * U * P3 ≤ 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3 :=
      mul_le_mul_of_nonneg_right hlin hP3.le
    have e3 : 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3
        ≤ 2 * J7 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3 := by
      apply mul_le_mul_of_nonneg_right _ hP3.le
      exact mul_le_mul_of_nonneg_right (by linarith) hκ.le
    linarith
  have h2 : ρ * P3 ≤ P7 := by
    have : J3 * (ρ * P3) ≤ J3 * P7 := by linarith
    exact le_of_mul_le_mul_left this hJ3
  -- expand around the ΛCDM point
  have hQ2 : Qc Ω (2 * 0.6931471803) ≤ Qc Ω (2 * ℓ) :=
    Qc_mono Ω _ _ hΩ₁ hΩ₂ (by norm_num) (by linarith [Real.log_two_gt_d9])
  have hQ3 : Qc Ω (3 * ℓ) ≤ Qc Ω (3 * 0.6931471808) :=
    Qc_mono Ω _ _ hΩ₁ hΩ₂ (by positivity) (by linarith [Real.log_two_lt_d9])
  set d₂ := a₂ / l - (3 / 2 - 3 / 4 * Ω) with hd₂
  set d₃ := a₃ / l ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6) with hd₃
  have hexp : P7 - ρ * P3 = Qc Ω (3 * ℓ) - ρ * Qc Ω (2 * ℓ)
      + (d₂ * ((9 - 4 * ρ) * ℓ ^ 2) + d₃ * ((27 - 8 * ρ) * ℓ ^ 3)) := by
    rw [hP7def, hP3def, hd₂, hd₃]; unfold Qc; ring
  have hρQ : ρ * Qc Ω (2 * 0.6931471803) ≤ ρ * Qc Ω (2 * ℓ) := mul_le_mul_of_nonneg_left hQ2 hρ
  have hlin2 : m ≤ d₂ * ((9 - 4 * ρ) * ℓ ^ 2) + d₃ * ((27 - 8 * ρ) * ℓ ^ 3) := by linarith
  have hc := core (5 / 4) ρ m ℓ l d₂ d₃ log_ten_ge hℓ0 (by linarith [Real.log_two_lt_d9]) hm hlin2 hD
  have e2 : l * d₂ = a₂ - lusA2 Ω := by rw [hd₂]; unfold lusA2; field_simp; ring
  have e3 : l ^ 2 * d₃ = a₃ - lusA3 Ω := by rw [hd₃]; unfold lusA3; field_simp; ring
  rwa [e2, e3] at hc

/-! Numerical checks per Ω-subinterval (standalone: heartbeat trap). -/

lemma lin0 (Ω : ℝ) (ha : (1/5 : ℝ) ≤ Ω) (hb : Ω ≤ (9/40 : ℝ)) :
    (12899/5000 : ℝ) * ((203715349 / 100000000 : ℝ) + (-91364007 / 50000000 : ℝ) * Ω) ≤ 2 * ((141929311 / 50000000 : ℝ) - (284250829 / 100000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma mq0 (Ω : ℝ) (ha : (1/5 : ℝ) ≤ Ω) (hb : Ω ≤ (9/40 : ℝ)) :
    (6329/10000 : ℝ) ≤ (12899/5000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

lemma dd0 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (12899/5000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (12899/5000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (6329/10000 : ℝ) ^ 2 := by norm_num

lemma lin1 (Ω : ℝ) (ha : (9/40 : ℝ) ≤ Ω) (hb : Ω ≤ (1/4 : ℝ)) :
    (12843/5000 : ℝ) * ((203715349 / 100000000 : ℝ) + (-91364007 / 50000000 : ℝ) * Ω) ≤ 2 * ((141929311 / 50000000 : ℝ) - (284250829 / 100000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma mq1 (Ω : ℝ) (ha : (9/40 : ℝ) ≤ Ω) (hb : Ω ≤ (1/4 : ℝ)) :
    (793/1250 : ℝ) ≤ (12843/5000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

lemma dd1 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (12843/5000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (12843/5000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (793/1250 : ℝ) ^ 2 := by norm_num

lemma lin2 (Ω : ℝ) (ha : (1/4 : ℝ) ≤ Ω) (hb : Ω ≤ (11/40 : ℝ)) :
    (25567/10000 : ℝ) * ((203715349 / 100000000 : ℝ) + (-91364007 / 50000000 : ℝ) * Ω) ≤ 2 * ((141929311 / 50000000 : ℝ) - (284250829 / 100000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma mq2 (Ω : ℝ) (ha : (1/4 : ℝ) ≤ Ω) (hb : Ω ≤ (11/40 : ℝ)) :
    (3159/5000 : ℝ) ≤ (25567/10000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

lemma dd2 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (25567/10000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (25567/10000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (3159/5000 : ℝ) ^ 2 := by norm_num

lemma lin3 (Ω : ℝ) (ha : (11/40 : ℝ) ≤ Ω) (hb : Ω ≤ (3/10 : ℝ)) :
    (25441/10000 : ℝ) * ((203715349 / 100000000 : ℝ) + (-91364007 / 50000000 : ℝ) * Ω) ≤ 2 * ((141929311 / 50000000 : ℝ) - (284250829 / 100000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma mq3 (Ω : ℝ) (ha : (11/40 : ℝ) ≤ Ω) (hb : Ω ≤ (3/10 : ℝ)) :
    (1563/2500 : ℝ) ≤ (25441/10000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

lemma dd3 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (25441/10000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (25441/10000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (1563/2500 : ℝ) ^ 2 := by norm_num

lemma lin4 (Ω : ℝ) (ha : (3/10 : ℝ) ≤ Ω) (hb : Ω ≤ (13/40 : ℝ)) :
    (25449/10000 : ℝ) * ((93266813 / 50000000 : ℝ) + (-62727941 / 50000000 : ℝ) * Ω) ≤ 2 * ((998388 / 390625 : ℝ) - (47016993 / 25000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma mq4 (Ω : ℝ) (ha : (3/10 : ℝ) ≤ Ω) (hb : Ω ≤ (13/40 : ℝ)) :
    (347/500 : ℝ) ≤ (25449/10000 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

lemma dd4 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (25449/10000 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (25449/10000 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (347/500 : ℝ) ^ 2 := by norm_num

lemma lin5 (Ω : ℝ) (ha : (13/40 : ℝ) ≤ Ω) (hb : Ω ≤ (7/20 : ℝ)) :
    (1269/500 : ℝ) * ((93266813 / 50000000 : ℝ) + (-62727941 / 50000000 : ℝ) * Ω) ≤ 2 * ((998388 / 390625 : ℝ) - (47016993 / 25000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma mq5 (Ω : ℝ) (ha : (13/40 : ℝ) ≤ Ω) (hb : Ω ≤ (7/20 : ℝ)) :
    (7171/10000 : ℝ) ≤ (1269/500 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

lemma dd5 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (1269/500 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (1269/500 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (7171/10000 : ℝ) ^ 2 := by norm_num

lemma lin6 (Ω : ℝ) (ha : (7/20 : ℝ) ≤ Ω) (hb : Ω ≤ (2/5 : ℝ)) :
    (1577/625 : ℝ) * ((93266813 / 50000000 : ℝ) + (-62727941 / 50000000 : ℝ) * Ω) ≤ 2 * ((998388 / 390625 : ℝ) - (47016993 / 25000000 : ℝ) * Ω) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma mq6 (Ω : ℝ) (ha : (7/20 : ℝ) ≤ Ω) (hb : Ω ≤ (2/5 : ℝ)) :
    (1741/2500 : ℝ) ≤ (1577/625 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

lemma dd6 : (5 / 4 : ℝ) ^ 2 * ((9 - 4 * (1577/625 : ℝ)) ^ 2 * 0.6931471808 ^ 4 /
        ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 2
      + (27 - 8 * (1577/625 : ℝ)) ^ 2 * 0.6931471808 ^ 6 / ((10 * 0.6931471803 - 24 / 1000) / 3) ^ 4)
      < (1741/2500 : ℝ) ^ 2 := by norm_num

/-- The analytic step shared by `cubic_separation` and `cubic_direction`: the 0.05-mag match at
`z = 3, 7` gives `2 J₇ (1 − κ) P₃ ≤ J₃ P₇` (exact distances through the bridge, the
polynomial in `u = ln(1+z)`). -/
lemma matching (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₇ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₇))
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₇ : |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₇)) - c|
      ≤ 1 / 20) :
    0 < 2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
        + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3 ∧
    2 * (∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v) * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) *
        (2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3)
      ≤ (∫ v in (1/2:ℝ)..1, gL Ω v) * (3 * Real.log 2 + a₂ / Real.log 10 * (3 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2) ^ 3) := by
  have hΩ₀ : 0 ≤ Ω := by linarith
  have hΩ1 : Ω ≤ 1 := by linarith
  have hsub : Set.Icc t₃ t₀ ⊆ Set.Icc t₇ t₀ := Set.Icc_subset_Icc_left h₇₃
  have hbr3 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ1 a t₃ t₀ h₃₀ (fun s hs => hpos s (hsub hs))
    (fun s hs => hdiff s (hsub hs)) hH₀ (fun s hs => hH s (hsub hs))
  have hbr7 := lumDistFlat_flatLCDM Ω hΩ₀ hΩ1 a t₇ t₀ (le_trans h₇₃ h₃₀) hpos hdiff hH₀ hH
  have ha3 : 0 < a t₃ := hpos t₃ ⟨h₇₃, h₃₀⟩
  have ha7 : 0 < a t₇ := hpos t₇ ⟨le_rfl, le_trans h₇₃ h₃₀⟩
  have hw : √(1 / (1 + 3) : ℝ) = 1 / 2 := by
    rw [show (1 / (1 + 3) : ℝ) = (1 / 2) ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [ratio_of_z a t₃ t₀ 3 ha3 (hpos t₀ ⟨le_trans h₇₃ h₃₀, le_rfl⟩) hz₃, hw] at hbr3
  rw [ratio_of_z a t₇ t₀ 7 ha7 (hpos t₀ ⟨le_trans h₇₃ h₃₀, le_rfl⟩) hz₇] at hbr7
  change lumDistFlat a t₀ t₃ = (1 + redshift a t₀ t₃) / hubble a t₀ * ∫ v in (1/2:ℝ)..1, gL Ω v
    at hbr3
  change lumDistFlat a t₀ t₇ = (1 + redshift a t₀ t₇) / hubble a t₀ *
    ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v at hbr7
  rw [poly_gen a₂ a₃ H _ hHp.ne', hz₃, log4] at hp₃ hm₃
  rw [poly_gen a₂ a₃ H _ hHp.ne', hz₇, log8] at hp₇ hm₇
  rw [hbr3, hz₃] at hm₃
  rw [hbr7, hz₇] at hm₇
  set J3 := ∫ v in (1/2:ℝ)..1, gL Ω v with hJ3def
  set J7 := ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v with hJ7def
  set H₀ := hubble a t₀ with hH₀def
  set P3 := 2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3 with hP3def
  set P7 := 3 * Real.log 2 + a₂ / Real.log 10 * (3 * Real.log 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2) ^ 3 with hP7def
  have hP3 : 0 < P3 := by
    have := hp₃; rw [div_pos_iff_of_pos_right hHp] at this; exact this
  have hP7 : 0 < P7 := by
    have := hp₇; rw [div_pos_iff_of_pos_right hHp] at this; exact this
  have hJ3 : 0 < J3 := by
    rcases le_total Ω (3 / 10) with hp | hp
    · have := (J3_lower Ω hΩ₁ hΩ₂).1 hp; linarith
    · have := (J3_lower Ω hΩ₁ hΩ₂).2 hp; linarith
  have hJ7 : 0 < J7 := by
    rcases le_total Ω (3 / 10) with hp | hp
    · have := (J7_lower Ω hΩ₁ hΩ₂).1 hp; linarith
    · have := (J7_lower Ω hΩ₁ hΩ₂).2 hp; linarith
  set X3 := (1 + 3) / H₀ * J3 / (P3 / H) with hX3
  set X7 := (1 + 7) / H₀ * J7 / (P7 / H) with hX7
  have hX3p : 0 < X3 := by positivity
  have hX7p : 0 < X7 := by positivity
  have hdiffm : 5 * Real.logb 10 (X7 / X3) ≤ 1 / 10 := by
    rw [Real.logb_div hX7p.ne' hX3p.ne']
    have h3 := abs_le.1 hm₃
    have h7 := abs_le.1 hm₇
    linarith
  have hY : X7 / X3 = 2 * J7 * P3 / (J3 * P7) := by
    rw [hX7, hX3]; field_simp; ring
  have hκ : X7 / X3 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) ≤ 1 := by
    by_contra hc
    push Not at hc
    have := five_logb_gt (1 / 10) (X7 / X3) (by positivity) (by norm_num) hc
    linarith
  rw [hY] at hκ
  have hmatch : 2 * J7 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3 ≤ J3 * P7 := by
    have hpos' : 0 < J3 * P7 := by positivity
    rw [div_mul_eq_mul_div, div_le_one hpos'] at hκ
    linarith
  exact ⟨hP3, hmatch⟩

/-- **B1 separation.** In every flat ΛCDM model with `Ω ∈ [0.2, 0.4]` (sources at `z = 3`, `z = 7`),
any cubic log-polynomial (coefficients `a₂, a₃`, normalisation `H > 0`, positive at both
redshifts) whose distance modulus agrees with the exact one up to a common offset `c` within
0.05 mag at `z = 3` and at `z = 7` has `(a₂, a₃)` at Euclidean distance more than `5/4` from the
ΛCDM-implied point `(lusA2 Ω, lusA3 Ω)`. -/
theorem cubic_separation (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₇ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₇))
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₇ : |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₇)) - c|
      ≤ 1 / 20) :
    (5 / 4) ^ 2 < (a₂ - lusA2 Ω) ^ 2 + (a₃ - lusA3 Ω) ^ 2 := by
  obtain ⟨hP3, hmatch⟩ := matching Ω hΩ₁ hΩ₂ a t₇ t₃ t₀ h₇₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₇
    a₂ a₃ H c hHp hp₃ hp₇ hm₃ hm₇
  set J3 := ∫ v in (1/2:ℝ)..1, gL Ω v with hJ3def
  set J7 := ∫ v in √(1 / (1 + 7) : ℝ)..1, gL Ω v with hJ7def
  have hJ3 : 0 < J3 := by
    rcases le_total Ω (3 / 10) with hp | hp
    · have := (J3_lower Ω hΩ₁ hΩ₂).1 hp; linarith
    · have := (J3_lower Ω hΩ₁ hΩ₂).2 hp; linarith
  rcases le_total Ω (11/40 : ℝ) with h1 | h1
  · rcases le_total Ω (9/40 : ℝ) with h2 | h2
    · have ha : (1/5 : ℝ) ≤ Ω := by linarith
      have hb : Ω ≤ (9/40 : ℝ) := by linarith
      exact case_step Ω a₂ a₃ J3 J7 _ _ (12899/5000 : ℝ) (6329/10000 : ℝ) hΩ₁ hΩ₂ hP3 hmatch hJ3
        ((J7_lower Ω hΩ₁ hΩ₂).1 (by linarith)) (J3_upper0 Ω (by linarith) (by linarith))
        (by norm_num) (lin0 Ω ha hb) (mq0 Ω ha hb) (by norm_num) dd0
    · rcases le_total Ω (1/4 : ℝ) with h3 | h3
      · have ha : (9/40 : ℝ) ≤ Ω := by linarith
        have hb : Ω ≤ (1/4 : ℝ) := by linarith
        exact case_step Ω a₂ a₃ J3 J7 _ _ (12843/5000 : ℝ) (793/1250 : ℝ) hΩ₁ hΩ₂ hP3 hmatch hJ3
          ((J7_lower Ω hΩ₁ hΩ₂).1 (by linarith)) (J3_upper0 Ω (by linarith) (by linarith))
          (by norm_num) (lin1 Ω ha hb) (mq1 Ω ha hb) (by norm_num) dd1
      · have ha : (1/4 : ℝ) ≤ Ω := by linarith
        have hb : Ω ≤ (11/40 : ℝ) := by linarith
        exact case_step Ω a₂ a₃ J3 J7 _ _ (25567/10000 : ℝ) (3159/5000 : ℝ) hΩ₁ hΩ₂ hP3 hmatch hJ3
          ((J7_lower Ω hΩ₁ hΩ₂).1 (by linarith)) (J3_upper0 Ω (by linarith) (by linarith))
          (by norm_num) (lin2 Ω ha hb) (mq2 Ω ha hb) (by norm_num) dd2
  · rcases le_total Ω (13/40 : ℝ) with h2 | h2
    · rcases le_total Ω (3/10 : ℝ) with h3 | h3
      · have ha : (11/40 : ℝ) ≤ Ω := by linarith
        have hb : Ω ≤ (3/10 : ℝ) := by linarith
        exact case_step Ω a₂ a₃ J3 J7 _ _ (25441/10000 : ℝ) (1563/2500 : ℝ) hΩ₁ hΩ₂ hP3 hmatch hJ3
          ((J7_lower Ω hΩ₁ hΩ₂).1 (by linarith)) (J3_upper0 Ω (by linarith) (by linarith))
          (by norm_num) (lin3 Ω ha hb) (mq3 Ω ha hb) (by norm_num) dd3
      · have ha : (3/10 : ℝ) ≤ Ω := by linarith
        have hb : Ω ≤ (13/40 : ℝ) := by linarith
        exact case_step Ω a₂ a₃ J3 J7 _ _ (25449/10000 : ℝ) (347/500 : ℝ) hΩ₁ hΩ₂ hP3 hmatch hJ3
          ((J7_lower Ω hΩ₁ hΩ₂).2 (by linarith)) (J3_upper1 Ω (by linarith) (by linarith))
          (by norm_num) (lin4 Ω ha hb) (mq4 Ω ha hb) (by norm_num) dd4
    · rcases le_total Ω (7/20 : ℝ) with h3 | h3
      · have ha : (13/40 : ℝ) ≤ Ω := by linarith
        have hb : Ω ≤ (7/20 : ℝ) := by linarith
        exact case_step Ω a₂ a₃ J3 J7 _ _ (1269/500 : ℝ) (7171/10000 : ℝ) hΩ₁ hΩ₂ hP3 hmatch hJ3
          ((J7_lower Ω hΩ₁ hΩ₂).2 (by linarith)) (J3_upper1 Ω (by linarith) (by linarith))
          (by norm_num) (lin5 Ω ha hb) (mq5 Ω ha hb) (by norm_num) dd5
      · have ha : (7/20 : ℝ) ≤ Ω := by linarith
        have hb : Ω ≤ (2/5 : ℝ) := by linarith
        exact case_step Ω a₂ a₃ J3 J7 _ _ (1577/625 : ℝ) (1741/2500 : ℝ) hΩ₁ hΩ₂ hP3 hmatch hJ3
          ((J7_lower Ω hΩ₁ hΩ₂).2 (by linarith)) (J3_upper1 Ω (by linarith) (by linarith))
          (by norm_num) (lin6 Ω ha hb) (mq6 Ω ha hb) (by norm_num) dd6

lemma dir_lin0 (Ω : ℝ) (ha : (1/5 : ℝ) ≤ Ω) (hb : Ω ≤ (3/10 : ℝ)) :
    (5/2 : ℝ) * ((203715349 / 100000000 : ℝ) + (-91364007 / 50000000 : ℝ) * Ω) ≤
      2 * ((141929311 / 50000000 : ℝ) - (284250829 / 100000000 : ℝ) * Ω) *
        (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma dir_lin1 (Ω : ℝ) (ha : (3/10 : ℝ) ≤ Ω) (hb : Ω ≤ (2/5 : ℝ)) :
    (5/2 : ℝ) * ((93266813 / 50000000 : ℝ) + (-62727941 / 50000000 : ℝ) * Ω) ≤
      2 * ((998388 / 390625 : ℝ) - (47016993 / 25000000 : ℝ) * Ω) *
        (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) := by
  norm_num; linarith

lemma dir_mq (Ω : ℝ) (ha : (1/5 : ℝ) ≤ Ω) (hb : Ω ≤ (2/5 : ℝ)) :
    0 < (5/2 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808) := by
  unfold Qc; nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

lemma dir_step (Ω a₂ a₃ J3 J7 L U : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (hP3 : 0 < 2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
      + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3)
    (hmatch : 2 * J7 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) *
        (2 * Real.log 2 + a₂ / Real.log 10 * (2 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (2 * Real.log 2) ^ 3)
      ≤ J3 * (3 * Real.log 2 + a₂ / Real.log 10 * (3 * Real.log 2) ^ 2
          + a₃ / Real.log 10 ^ 2 * (3 * Real.log 2) ^ 3))
    (hJ3 : 0 < J3) (hL : L ≤ J7) (hU : J3 ≤ U)
    (hlin : (5/2 : ℝ) * U ≤ 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)))
    (hmq : 0 < (5/2 : ℝ) * Qc Ω (2 * 0.6931471803) - Qc Ω (3 * 0.6931471808)) :
    a₂ - lusA2 Ω < 7 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  set l := Real.log 10 with hl
  set ℓ := Real.log 2 with hℓ
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := Real.log_pos (by norm_num)
  set P3 := 2 * ℓ + a₂ / l * (2 * ℓ) ^ 2 + a₃ / l ^ 2 * (2 * ℓ) ^ 3 with hP3def
  set P7 := 3 * ℓ + a₂ / l * (3 * ℓ) ^ 2 + a₃ / l ^ 2 * (3 * ℓ) ^ 3 with hP7def
  have hκ : 0 < 1 - 1 / 10 / 5 * (10 / 3 * (0.6931471808 : ℝ)) := by norm_num
  have h1 : (5/2 : ℝ) * J3 * P3 ≤ J3 * P7 := by
    have e1 : (5/2 : ℝ) * J3 * P3 ≤ (5/2) * U * P3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU (by norm_num)) hP3.le
    have e2 : (5/2 : ℝ) * U * P3 ≤ 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3 :=
      mul_le_mul_of_nonneg_right hlin hP3.le
    have e3 : 2 * L * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3
        ≤ 2 * J7 * (1 - 1 / 10 / 5 * (10 / 3 * 0.6931471808)) * P3 := by
      apply mul_le_mul_of_nonneg_right _ hP3.le
      exact mul_le_mul_of_nonneg_right (by linarith) hκ.le
    linarith
  have h2 : (5/2 : ℝ) * P3 ≤ P7 := by
    have : J3 * ((5/2) * P3) ≤ J3 * P7 := by linarith
    exact le_of_mul_le_mul_left this hJ3
  have hQ2 : Qc Ω (2 * 0.6931471803) ≤ Qc Ω (2 * ℓ) :=
    Qc_mono Ω _ _ hΩ₁ hΩ₂ (by norm_num) (by linarith [Real.log_two_gt_d9])
  have hQ3 : Qc Ω (3 * ℓ) ≤ Qc Ω (3 * 0.6931471808) :=
    Qc_mono Ω _ _ hΩ₁ hΩ₂ (by positivity) (by linarith [Real.log_two_lt_d9])
  set d₂ := a₂ / l - (3 / 2 - 3 / 4 * Ω) with hd₂
  set d₃ := a₃ / l ^ 2 - (9 / 8 * Ω ^ 2 - 2 * Ω + 7 / 6) with hd₃
  have hexp : P7 - (5/2) * P3 = Qc Ω (3 * ℓ) - (5/2) * Qc Ω (2 * ℓ)
      + (d₂ * (-ℓ ^ 2) + d₃ * (7 * ℓ ^ 3)) := by
    rw [hP7def, hP3def, hd₂, hd₃]; unfold Qc; ring
  have hpos2 : 0 < d₂ * (-ℓ ^ 2) + d₃ * (7 * ℓ ^ 3) := by linarith
  have e2 : d₂ = (a₂ - lusA2 Ω) / l := by rw [hd₂]; unfold lusA2; field_simp; ring
  have e3 : d₃ = (a₃ - lusA3 Ω) / l ^ 2 := by rw [hd₃]; unfold lusA3; field_simp; ring
  rw [e2, e3] at hpos2
  have hlb : Real.logb 10 2 = ℓ / l := rfl
  rw [hlb]
  have key : (a₂ - lusA2 Ω) * (ℓ ^ 2 * l) < 7 * (ℓ / l) * (a₃ - lusA3 Ω) * (ℓ ^ 2 * l) := by
    have e : 7 * (ℓ / l) * (a₃ - lusA3 Ω) * (ℓ ^ 2 * l) - (a₂ - lusA2 Ω) * (ℓ ^ 2 * l)
        = l ^ 2 * ((a₂ - lusA2 Ω) / l * (-ℓ ^ 2) + (a₃ - lusA3 Ω) / l ^ 2 * (7 * ℓ ^ 3)) := by
      field_simp; ring
    have : 0 < l ^ 2 * ((a₂ - lusA2 Ω) / l * (-ℓ ^ 2) + (a₃ - lusA3 Ω) / l ^ 2 * (7 * ℓ ^ 3)) :=
      mul_pos (by positivity) hpos2
    linarith
  exact lt_of_mul_lt_mul_right key (by positivity)

/-- **B1 direction.** In every flat ΛCDM model with `Ω ∈ [0.2, 0.4]` (sources at `z = 3`, `z = 7`;
hypotheses as in `cubic_separation`), every cubic log-polynomial that agrees with exact flat ΛCDM (`Ω ∈ [0.2, 0.4]`) within 0.05 mag at `z = 3` and `z = 7` up to a common
offset lies strictly on one side of a line through the ΛCDM-implied point:
`a₂ − lusA2 Ω < 7 log₁₀2 · (a₃ − lusA3 Ω)` (slope `7 log₁₀ 2 ≈ 2.107`). Truncation can move a
matching cubic only towards smaller `a₂` / larger `a₃` relative to that line.

FROZEN (annex 40.1) in run 2026-10-31T0828Z before proof work (added after the referee's
direction remark, `runs/2026-10-31T0828Z/referee_b1sep.md`). -/
theorem cubic_direction (Ω : ℝ) (hΩ₁ : 1 / 5 ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₇ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₇))
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₇ : |5 * Real.logb 10 (lumDistFlat a t₀ t₇ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₇)) - c|
      ≤ 1 / 20) :
    a₂ - lusA2 Ω < 7 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  obtain ⟨hP3, hmatch⟩ := matching Ω hΩ₁ hΩ₂ a t₇ t₃ t₀ h₇₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₇
    a₂ a₃ H c hHp hp₃ hp₇ hm₃ hm₇
  have hJ3 : 0 < ∫ v in (1/2:ℝ)..1, gL Ω v := by
    rcases le_total Ω (3 / 10) with hp | hp
    · have := (J3_lower Ω hΩ₁ hΩ₂).1 hp; linarith
    · have := (J3_lower Ω hΩ₁ hΩ₂).2 hp; linarith
  rcases le_total Ω (3 / 10) with hp | hp
  · exact dir_step Ω a₂ a₃ _ _ _ _ hΩ₁ hΩ₂ hP3 hmatch hJ3 ((J7_lower Ω hΩ₁ hΩ₂).1 hp)
      (J3_upper0 Ω hΩ₁ hp) (dir_lin0 Ω hΩ₁ hp) (dir_mq Ω hΩ₁ hΩ₂)
  · exact dir_step Ω a₂ a₃ _ _ _ _ hΩ₁ hΩ₂ hP3 hmatch hJ3 ((J7_lower Ω hΩ₁ hΩ₂).2 hp)
      (J3_upper1 Ω hp hΩ₂) (dir_lin1 Ω hp hΩ₂) (dir_mq Ω hΩ₁ hΩ₂)

end Checked.Cosmography.B1Sep
