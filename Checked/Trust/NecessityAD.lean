import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD

/-! Hypothesis necessity for the smoothness hypothesis (hypothesis 1, `ContDiffAt`) of the past-only
"printed coefficient fails" cosmography headlines (run 2026-11-14T0828Z; scratch
`runs/2026-11-14T0828Z/lean/NecessityAD.lean`): `CCS.printedD4_fails_past`, `BambaY.printedD2y_fails_past`,
`CVdQ.printedQ2_fails_past`, `BambaK.printedD3y_fails_past`, `BambaK.printedD4y_fails_past`,
`BambaA.printedDA3_fails_past`, `BambaA.printedDA4_fails_past`, `BambaZ.printedDL4z_fails_past`,
`BambaZ.printedDA4z_fails_past`, `DemianskiZ.demDL4_fails_past`, `DemianskiZ.demDA4_fails_past`.

Each witness is a kinked scale factor `a = 1 + t + b t² + d t³ + c tⁿ⁺¹|t|` at `t₀ = 0` with `c ≠ 0`. Its
`(n+1)`-th derivative is a polynomial plus a multiple of `|t|`, so Lean's derivative of it at `0` is the
junk value `0`: the top cosmographic coefficient the headline needs (`j₀`, `s₀` or `l₀`) is `0`. For `t < 0`
the scale factor is the polynomial `1 + t + b t² + d t³ − c tⁿ⁺²`, and every distance in these headlines at a
past time depends only on the scale factor between that time and `t₀`. The constant `c` is chosen so that
the polynomial's own top coefficient makes the correct series coefficient equal to the printed one evaluated
at the junk value; the correct-order series theorem for the polynomial then gives the remainder bound that
the headline denies, on the past side. The other hypotheses hold: `a(0) = 1`, `H₀ = 1`, and the
printed-coefficient condition is nonzero at the kinked scale factor's coefficients. So the smoothness
hypothesis is needed: without it the printed coefficient can be right, through a junk derivative. The
two-sided companions keep this hypothesis open (a kink gives different top coefficients on the two sides).

The two-sided `lookback_second_order_bigO` (`O(z³)`) is different: its only other hypotheses are `a(t₀) ≠ 0`
and `ȧ(t₀) ≠ 0`, so the kinked `1 + t + t|t|` of `Checked.Trust.NCD` (junk `q₀ = 0`, remainder `t|t| + a z³`)
shows smoothness needed there too. -/

namespace Checked.Trust.NecessityAD
open Set Filter Topology Asymptotics
open Checked.Cosmography Checked.Cosmography.Aviles

/-! ### Kinked scale factors and their past branches -/

/-- `α + β x + γ x² + ε x³ + δ xⁿ⁺¹|x|`. -/
noncomputable def G (α β γ ε δ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  α + β * x + γ * x ^ 2 + ε * x ^ 3 + δ * (x ^ (n + 1) * |x|)

theorem G_hasDerivAt (α β γ ε δ : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (G α β γ ε δ n) (β + 2 * γ * x + 3 * ε * x ^ 2 + δ * ((n + 2) * x ^ n * |x|)) x := by
  have h := ((((hasDerivAt_const x α).add ((hasDerivAt_id x).const_mul β)).add
    ((hasDerivAt_pow 2 x).const_mul γ)).add ((hasDerivAt_pow 3 x).const_mul ε)).add
    ((Checked.Trust.NCD.pabs_hasDerivAt n x).const_mul δ)
  convert h using 1
  · funext t; simp only [G, id, Pi.add_apply]
  · simp; ring

theorem G_deriv_succ (α β γ ε δ : ℝ) (n : ℕ) :
    deriv (G α β γ ε δ (n + 1)) = G β (2 * γ) (3 * ε) 0 (δ * ((n : ℝ) + 3)) n := by
  funext x; rw [(G_hasDerivAt α β γ ε δ (n + 1) x).deriv]; simp only [G]; push_cast; ring

theorem G_deriv_zero (α β γ ε δ : ℝ) :
    deriv (G α β γ ε δ 0) = fun x => β + 2 * γ * x + 3 * ε * x ^ 2 + 2 * δ * |x| := by
  funext x; rw [(G_hasDerivAt α β γ ε δ 0 x).deriv]; push_cast; ring

/-- Lean's junk derivative: a polynomial plus a nonzero multiple of `|x|` has no derivative at `0`. -/
theorem junk (β γ ε δ : ℝ) (hδ : δ ≠ 0) :
    deriv (fun x : ℝ => β + 2 * γ * x + 3 * ε * x ^ 2 + 2 * δ * |x|) 0 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro h
  apply not_differentiableAt_abs_zero
  have hp : DifferentiableAt ℝ (fun x : ℝ => β + 2 * γ * x + 3 * ε * x ^ 2) 0 := by fun_prop
  have := (h.sub hp).const_mul (1 / (2 * δ))
  convert this using 1
  funext x; simp only [Pi.sub_apply]; field_simp; ring

theorem G_zero (α β γ ε δ : ℝ) (n : ℕ) : G α β γ ε δ n 0 = α := by simp [G]

/-- Quintic polynomial `α + β x + γ x² + ε x³ + ζ x⁴ + η x⁵`. -/
noncomputable def PQ (α β γ ε ζ η : ℝ) (x : ℝ) : ℝ :=
  α + β * x + γ * x ^ 2 + ε * x ^ 3 + ζ * x ^ 4 + η * x ^ 5

theorem PQ_deriv (α β γ ε ζ η : ℝ) :
    deriv (PQ α β γ ε ζ η) = PQ β (2 * γ) (3 * ε) (4 * ζ) (5 * η) 0 := by
  funext x
  apply HasDerivAt.deriv
  have h := (((((hasDerivAt_const x α).add ((hasDerivAt_id x).const_mul β)).add
    ((hasDerivAt_pow 2 x).const_mul γ)).add ((hasDerivAt_pow 3 x).const_mul ε)).add
    ((hasDerivAt_pow 4 x).const_mul ζ)).add ((hasDerivAt_pow 5 x).const_mul η)
  convert h using 1
  · funext t; simp only [PQ, id, Pi.add_apply]
  · simp [PQ]; ring

theorem PQ_zero (α β γ ε ζ η : ℝ) : PQ α β γ ε ζ η 0 = α := by simp [PQ]

theorem PQ_smooth (α β γ ε ζ η : ℝ) (n : ℕ∞) : ContDiffAt ℝ n (PQ α β γ ε ζ η) 0 := by
  have : ContDiff ℝ n (PQ α β γ ε ζ η) := by unfold PQ; fun_prop
  exact this.contDiffAt

/-- Coefficients of a scale factor with `a(0) = 1`, `ȧ(0) = 1`. -/
theorem unit_hubble {a : ℝ → ℝ} (h0 : a 0 = 1) (h1 : deriv a 0 = 1) : hubble a 0 = 1 := by
  simp [hubble, h0, h1]

theorem unit_coeff {a : ℝ → ℝ} (h0 : a 0 = 1) (h1 : deriv a 0 = 1) (k : ℕ) :
    cosmoCoeff k a 0 = iteratedDeriv k a 0 := by
  simp [cosmoCoeff, unit_hubble h0 h1, h0]

theorem unit_decel {a : ℝ → ℝ} (h0 : a 0 = 1) (h1 : deriv a 0 = 1) :
    decel a 0 = -deriv (deriv a) 0 := by
  simp [decel, h0, h1]

theorem unit_omega0 {a : ℝ → ℝ} (h0 : a 0 = 1) (h1 : deriv a 0 = 1) (K : ℝ) :
    BambaK.omega0 K a 0 = 1 + K := by
  simp [BambaK.omega0, unit_hubble h0 h1, h0]

theorem unit_curvK {a : ℝ → ℝ} (h0 : a 0 = 1) (h1 : deriv a 0 = 1) (K : ℝ) :
    BambaZ.curvK K a 0 = K := by
  simp [BambaZ.curvK, unit_hubble h0 h1, h0]

/-! Values for the families used below. -/

theorem G_d1_zero (b d c : ℝ) (n : ℕ) : deriv (G 1 1 b d c n) 0 = 1 := by
  rw [(G_hasDerivAt 1 1 b d c n 0).deriv]; simp

theorem PQ_d1_zero (b d ζ η : ℝ) : deriv (PQ 1 1 b d ζ η) 0 = 1 := by
  rw [PQ_deriv]; simp [PQ]

/-- `1 + t + b t² + d t³ + c t⁴|t|` (`C⁴`, not `C⁵` when `c ≠ 0`). -/
theorem G3_vals (b d c : ℝ) (hc : c ≠ 0) :
    deriv (deriv (G 1 1 b d c 3)) 0 = 2 * b ∧ iteratedDeriv 3 (G 1 1 b d c 3) 0 = 6 * d ∧
    iteratedDeriv 4 (G 1 1 b d c 3) 0 = 0 ∧ iteratedDeriv 5 (G 1 1 b d c 3) 0 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [G_deriv_succ, G_deriv_succ]; simp [G]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, G_deriv_succ, G_deriv_succ,
      G_deriv_succ]; simp [G]; ring
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, G_deriv_succ,
      G_deriv_succ, G_deriv_succ, G_deriv_zero]; simp
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, G_deriv_succ, G_deriv_succ, G_deriv_succ, G_deriv_zero]
    exact junk _ _ _ _ (by push_cast; positivity)

theorem P3_vals (b d c : ℝ) :
    deriv (deriv (PQ 1 1 b d 0 (-c))) 0 = 2 * b ∧ iteratedDeriv 3 (PQ 1 1 b d 0 (-c)) 0 = 6 * d ∧
    iteratedDeriv 4 (PQ 1 1 b d 0 (-c)) 0 = 0 ∧ iteratedDeriv 5 (PQ 1 1 b d 0 (-c)) 0 = -120 * c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [PQ_deriv, PQ_deriv]; simp [PQ]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, PQ_deriv, PQ_deriv, PQ_deriv]
    simp [PQ]; ring
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, PQ_deriv,
      PQ_deriv, PQ_deriv, PQ_deriv]; simp [PQ]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, PQ_deriv, PQ_deriv, PQ_deriv, PQ_deriv, PQ_deriv]; simp [PQ]; ring

theorem G3_past (b d c : ℝ) : ∀ s ≤ (0 : ℝ), G 1 1 b d c 3 s = PQ 1 1 b d 0 (-c) s := by
  intro s hs; simp only [G, PQ, abs_of_nonpos hs]; ring

/-! ### Agreement of the distances on the past side -/

theorem agree_comoving {a Q : ℝ → ℝ} (h : ∀ s ≤ (0 : ℝ), a s = Q s) {t : ℝ} (ht : t ≤ 0) :
    BambaY.comoving a 0 t = BambaY.comoving Q 0 t := by
  unfold BambaY.comoving
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  simp only [h s hs.2]

theorem agree_redshift {a Q : ℝ → ℝ} (h : ∀ s ≤ (0 : ℝ), a s = Q s) {t : ℝ} (ht : t ≤ 0) :
    redshift a 0 t = redshift Q 0 t := by
  simp only [redshift, h 0 le_rfl, h t ht]

theorem agree_yred {a Q : ℝ → ℝ} (h : ∀ s ≤ (0 : ℝ), a s = Q s) {t : ℝ} (ht : t ≤ 0) :
    BambaY.yred a 0 t = BambaY.yred Q 0 t := by
  simp only [BambaY.yred, agree_redshift h ht]

theorem agree_lumDist {a Q : ℝ → ℝ} (h : ∀ s ≤ (0 : ℝ), a s = Q s) {t : ℝ} (ht : t ≤ 0) (K : ℝ) :
    BambaK.lumDist K a 0 t = BambaK.lumDist K Q 0 t := by
  simp only [BambaK.lumDist, agree_redshift h ht, agree_comoving h ht, h 0 le_rfl]

theorem agree_angDist {a Q : ℝ → ℝ} (h : ∀ s ≤ (0 : ℝ), a s = Q s) {t : ℝ} (ht : t ≤ 0) (K : ℝ) :
    BambaA.angDist K a 0 t = BambaA.angDist K Q 0 t := by
  simp only [BambaA.angDist, agree_lumDist h ht, agree_redshift h ht]

theorem agree_lumDistFlat {a Q : ℝ → ℝ} (h : ∀ s ≤ (0 : ℝ), a s = Q s) {t : ℝ} (ht : t ≤ 0) :
    BambaY.lumDistFlat a 0 t = BambaY.lumDistFlat Q 0 t := by
  simp only [BambaY.lumDistFlat, agree_redshift h ht, agree_comoving h ht, h 0 le_rfl]

theorem agree_dQFlat {a Q : ℝ → ℝ} (h : ∀ s ≤ (0 : ℝ), a s = Q s) {t : ℝ} (ht : t ≤ 0) :
    CVdQ.dQFlat a 0 t = CVdQ.dQFlat Q 0 t := by
  simp only [CVdQ.dQFlat, agree_lumDistFlat h ht, agree_redshift h ht]

theorem past_mem : ∀ᶠ t in 𝓝[<] (0 : ℝ), t ≤ 0 :=
  eventually_nhdsWithin_of_forall fun _ ht => le_of_lt ht

/-! ### Fifth order, top coefficient `l₀`: `a = 1 + t + b t² + d t³ + c t⁴|t|` -/

theorem G3_coeffs (b d c : ℝ) (hc : c ≠ 0) :
    G 1 1 b d c 3 0 = 1 ∧ hubble (G 1 1 b d c 3) 0 = 1 ∧ decel (G 1 1 b d c 3) 0 = -(2 * b) ∧
    cosmoCoeff 3 (G 1 1 b d c 3) 0 = 6 * d ∧ cosmoCoeff 4 (G 1 1 b d c 3) 0 = 0 ∧
    cosmoCoeff 5 (G 1 1 b d c 3) 0 = 0 := by
  have h0 := G_zero 1 1 b d c 3
  have h1 := G_d1_zero b d c 3
  obtain ⟨v2, v3, v4, v5⟩ := G3_vals b d c hc
  refine ⟨h0, unit_hubble h0 h1, ?_, ?_, ?_, ?_⟩
  · rw [unit_decel h0 h1, v2]
  all_goals rwa [unit_coeff h0 h1]

theorem P3_coeffs (b d c : ℝ) :
    PQ 1 1 b d 0 (-c) 0 = 1 ∧ hubble (PQ 1 1 b d 0 (-c)) 0 = 1 ∧
    decel (PQ 1 1 b d 0 (-c)) 0 = -(2 * b) ∧
    cosmoCoeff 3 (PQ 1 1 b d 0 (-c)) 0 = 6 * d ∧ cosmoCoeff 4 (PQ 1 1 b d 0 (-c)) 0 = 0 ∧
    cosmoCoeff 5 (PQ 1 1 b d 0 (-c)) 0 = -120 * c := by
  have h0 := PQ_zero 1 1 b d 0 (-c)
  have h1 := PQ_d1_zero b d 0 (-c)
  obtain ⟨v2, v3, v4, v5⟩ := P3_vals b d c
  refine ⟨h0, unit_hubble h0 h1, ?_, ?_, ?_, ?_⟩
  · rw [unit_decel h0 h1, v2]
  all_goals rwa [unit_coeff h0 h1]

/-- Smoothness (`C⁵` at `t₀`) is needed in `CCS.printedD4_fails_past`: `a = 1 + t − t²/2 + (21/8) t⁴|t|`
is `C⁴` with `q₀ = 1`; Lean's junk fifth derivative gives `l₀ = 0`, and for `t < 0` the scale factor is the
polynomial `1 + t − t²/2 − (21/8) t⁵`, whose `l₀ = −315` makes the correct `D⁴` equal the printed one at
`l₀ = 0`. -/
theorem printedD4_fails_past_h1 : necessity% Checked.Cosmography.CCS.printedD4_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as, al⟩ := G3_coeffs (-1 / 2) 0 (21 / 8) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps, pl⟩ := P3_coeffs (-1 / 2) 0 (21 / 8)
  refine ⟨G 1 1 (-1 / 2) 0 (21 / 8) 3, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by rw [aq]; norm_num, ?_⟩
  have hc := (CCS.lookback_fifth_order (PQ 1 1 (-1 / 2) 0 0 (-(21 / 8))) 0 (PQ_smooth _ _ _ _ _ _ _)
    (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G3_past (-1 / 2) 0 (21 / 8)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [CCS.remainder, CCS.series, CCS.printedD4, CCS.correctD4, agree_redshift hP ht,
      aH, aq, aj, as, al, pH, pq, pj, ps, pl]
    norm_num
  · filter_upwards [past_mem] with t ht
    rw [agree_redshift hP ht]

/-! ### Fourth order, top coefficient `s₀`: `a = 1 + t + b t² + d t³ + c t³|t|` -/

theorem G2_vals (b d c : ℝ) (hc : c ≠ 0) :
    deriv (deriv (G 1 1 b d c 2)) 0 = 2 * b ∧ iteratedDeriv 3 (G 1 1 b d c 2) 0 = 6 * d ∧
    iteratedDeriv 4 (G 1 1 b d c 2) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [G_deriv_succ, G_deriv_succ]; simp [G]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, G_deriv_succ, G_deriv_succ,
      G_deriv_zero]; simp; ring
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, G_deriv_succ,
      G_deriv_succ, G_deriv_zero]
    exact junk _ _ _ _ (by push_cast; positivity)

theorem P2_vals (b d c : ℝ) :
    deriv (deriv (PQ 1 1 b d (-c) 0)) 0 = 2 * b ∧ iteratedDeriv 3 (PQ 1 1 b d (-c) 0) 0 = 6 * d ∧
    iteratedDeriv 4 (PQ 1 1 b d (-c) 0) 0 = -24 * c := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PQ_deriv, PQ_deriv]; simp [PQ]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, PQ_deriv, PQ_deriv, PQ_deriv]
    simp [PQ]; ring
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, PQ_deriv,
      PQ_deriv, PQ_deriv, PQ_deriv]; simp [PQ]; ring

theorem G2_past (b d c : ℝ) : ∀ s ≤ (0 : ℝ), G 1 1 b d c 2 s = PQ 1 1 b d (-c) 0 s := by
  intro s hs; simp only [G, PQ, abs_of_nonpos hs]; ring

theorem G2_coeffs (b d c : ℝ) (hc : c ≠ 0) :
    G 1 1 b d c 2 0 = 1 ∧ hubble (G 1 1 b d c 2) 0 = 1 ∧ decel (G 1 1 b d c 2) 0 = -(2 * b) ∧
    cosmoCoeff 3 (G 1 1 b d c 2) 0 = 6 * d ∧ cosmoCoeff 4 (G 1 1 b d c 2) 0 = 0 := by
  have h0 := G_zero 1 1 b d c 2
  have h1 := G_d1_zero b d c 2
  obtain ⟨v2, v3, v4⟩ := G2_vals b d c hc
  refine ⟨h0, unit_hubble h0 h1, ?_, ?_, ?_⟩
  · rw [unit_decel h0 h1, v2]
  all_goals rwa [unit_coeff h0 h1]

theorem P2_coeffs (b d c : ℝ) :
    PQ 1 1 b d (-c) 0 0 = 1 ∧ hubble (PQ 1 1 b d (-c) 0) 0 = 1 ∧
    decel (PQ 1 1 b d (-c) 0) 0 = -(2 * b) ∧
    cosmoCoeff 3 (PQ 1 1 b d (-c) 0) 0 = 6 * d ∧ cosmoCoeff 4 (PQ 1 1 b d (-c) 0) 0 = -24 * c := by
  have h0 := PQ_zero 1 1 b d (-c) 0
  have h1 := PQ_d1_zero b d (-c) 0
  obtain ⟨v2, v3, v4⟩ := P2_vals b d c
  refine ⟨h0, unit_hubble h0 h1, ?_, ?_, ?_⟩
  · rw [unit_decel h0 h1, v2]
  all_goals rwa [unit_coeff h0 h1]

/-! ### Third order, top coefficient `j₀`: `a = 1 + t + b t² + c t²|t|` -/

theorem G1_vals (b c : ℝ) (hc : c ≠ 0) :
    deriv (deriv (G 1 1 b 0 c 1)) 0 = 2 * b ∧ iteratedDeriv 3 (G 1 1 b 0 c 1) 0 = 0 := by
  refine ⟨?_, ?_⟩
  · rw [G_deriv_succ, G_deriv_zero]; simp
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, G_deriv_succ, G_deriv_zero]
    exact junk _ _ _ _ (by push_cast; positivity)

theorem P1_vals (b c : ℝ) :
    deriv (deriv (PQ 1 1 b (-c) 0 0)) 0 = 2 * b ∧ iteratedDeriv 3 (PQ 1 1 b (-c) 0 0) 0 = -6 * c := by
  refine ⟨?_, ?_⟩
  · rw [PQ_deriv, PQ_deriv]; simp [PQ]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, PQ_deriv, PQ_deriv, PQ_deriv]
    simp [PQ]; ring

theorem G1_past (b c : ℝ) : ∀ s ≤ (0 : ℝ), G 1 1 b 0 c 1 s = PQ 1 1 b (-c) 0 0 s := by
  intro s hs; simp only [G, PQ, abs_of_nonpos hs]; ring

theorem G1_coeffs (b c : ℝ) (hc : c ≠ 0) :
    G 1 1 b 0 c 1 0 = 1 ∧ hubble (G 1 1 b 0 c 1) 0 = 1 ∧ decel (G 1 1 b 0 c 1) 0 = -(2 * b) ∧
    cosmoCoeff 3 (G 1 1 b 0 c 1) 0 = 0 := by
  have h0 := G_zero 1 1 b 0 c 1
  have h1 := G_d1_zero b 0 c 1
  obtain ⟨v2, v3⟩ := G1_vals b c hc
  refine ⟨h0, unit_hubble h0 h1, ?_, ?_⟩
  · rw [unit_decel h0 h1, v2]
  · rwa [unit_coeff h0 h1]

theorem P1_coeffs (b c : ℝ) :
    PQ 1 1 b (-c) 0 0 0 = 1 ∧ hubble (PQ 1 1 b (-c) 0 0) 0 = 1 ∧
    decel (PQ 1 1 b (-c) 0 0) 0 = -(2 * b) ∧ cosmoCoeff 3 (PQ 1 1 b (-c) 0 0) 0 = -6 * c := by
  have h0 := PQ_zero 1 1 b (-c) 0 0
  have h1 := PQ_d1_zero b (-c) 0 0
  obtain ⟨v2, v3⟩ := P1_vals b c
  refine ⟨h0, unit_hubble h0 h1, ?_, ?_⟩
  · rw [unit_decel h0 h1, v2]
  · rwa [unit_coeff h0 h1]

theorem PQ_diff (α β γ ε ζ η : ℝ) : DifferentiableAt ℝ (PQ α β γ ε ζ η) 0 :=
  (PQ_smooth α β γ ε ζ η 1).differentiableAt (by norm_num)

/-! ### The witnesses -/

/-- Smoothness (`C³`) is needed in `BambaY.printedD2y_fails_past`: `a = 1 + t − (11/3) t²|t|` is `C²`,
Lean's junk third derivative gives `j₀ = 0`; for `t < 0` it is `1 + t + (11/3) t³` (`j₀ = 22`), for which the
correct `D²` equals the printed one at `j₀ = 0`. -/
theorem printedD2y_fails_past_h1 : necessity% Checked.Cosmography.BambaY.printedD2y_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj⟩ := G1_coeffs 0 (-11 / 3) (by norm_num)
  obtain ⟨p0, pH, pq, pj⟩ := P1_coeffs 0 (-11 / 3)
  refine ⟨G 1 1 0 0 (-11 / 3) 1, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by rw [aq, aj]; norm_num, ?_⟩
  have hc := (BambaY.lumDist_y_third_order (PQ 1 1 0 (-(-11 / 3)) 0 0) 0 (PQ_smooth _ _ _ _ _ _ _)
    (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G1_past 0 (-11 / 3)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaY.remainderY, BambaY.seriesY, BambaY.printedD2y, BambaY.correctD2y,
      agree_yred hP ht, agree_lumDistFlat hP ht, aH, aq, aj, pH, pq, pj]
    ring
  · filter_upwards [past_mem] with t ht
    rw [agree_yred hP ht]

/-- Smoothness (`C³`) is needed in `CVdQ.printedQ2_fails_past`: `a = 1 + t − (1/24) t²|t|`; for `t < 0` it
is `1 + t + t³/24` (`j₀ = 1/4`), for which the correct `Q²` equals the printed one at Lean's junk `j₀ = 0`. -/
theorem printedQ2_fails_past_h1 : necessity% Checked.Cosmography.CVdQ.printedQ2_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj⟩ := G1_coeffs 0 (-1 / 24) (by norm_num)
  obtain ⟨p0, pH, pq, pj⟩ := P1_coeffs 0 (-1 / 24)
  refine ⟨G 1 1 0 0 (-1 / 24) 1, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by rw [aq, aj]; norm_num, ?_⟩
  have hc := (CVdQ.dQ_y_third_order (PQ 1 1 0 (-(-1 / 24)) 0 0) 0 (PQ_smooth _ _ _ _ _ _ _)
    (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G1_past 0 (-1 / 24)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [CVdQ.remainderQ, CVdQ.seriesQ, CVdQ.printedQ2, CVdQ.correctQ2,
      agree_yred hP ht, agree_dQFlat hP ht, aH, aq, aj, pH, pq, pj]
    ring
  · filter_upwards [past_mem] with t ht
    rw [agree_yred hP ht]

/-- Smoothness is needed in `BambaK.printedD3y_fails_past`: with `K = 1` (`Ω₀ = 2`), `a = 1 + t − t³|t|/3`
is `C³`, Lean's junk fourth derivative gives `s₀ = 0`; for `t < 0` it is `1 + t + t⁴/3` (`s₀ = 8`), for which
the correct `D³` equals the printed one at `s₀ = 0`. -/
theorem printedD3y_fails_past_h1 : necessity% Checked.Cosmography.BambaK.printedD3y_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as⟩ := G2_coeffs 0 0 (-1 / 3) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps⟩ := P2_coeffs 0 0 (-1 / 3)
  refine ⟨1, G 1 1 0 0 (-1 / 3) 2, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by simp only [BambaK.omega0, aH, a0, aq]; norm_num, ?_⟩
  set Q := PQ 1 1 0 0 (-(-1 / 3)) 0
  have h54 := Checked.Trust.NCD.y5_y4 Q 0 (PQ_diff _ _ _ _ _ _) (by rw [p0]; norm_num)
  have hc := (((BambaK.lumDist_y_fifth_order 1 Q 0 (PQ_smooth _ _ _ _ _ _ _) (by rw [p0]; norm_num)
    (by rw [pH]; norm_num)).trans h54).add (h54.const_mul_left (BambaK.correctD4y (decel Q 0)
    (cosmoCoeff 3 Q 0) (cosmoCoeff 4 Q 0) (cosmoCoeff 5 Q 0) (BambaK.omega0 1 Q 0)))).mono
    (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G2_past 0 0 (-1 / 3)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaK.remK, BambaK.seriesY4, BambaK.printedD3y, BambaK.correctD3y,
      BambaY.correctD2y, BambaK.omega0, agree_yred hP ht, agree_lumDist hP ht, a0, aH, aq, aj, as,
      p0, pH, pq, pj, ps]
    ring
  · filter_upwards [past_mem] with t ht
    rw [agree_yred hP ht]

/-- Smoothness (`C⁵`) is needed in `BambaK.printedD4y_fails_past`: with `K = 1`, `a = 1 + t − t⁴|t|/120`
is `C⁴`, Lean's junk fifth derivative gives `l₀ = 0`; for `t < 0` it is `1 + t + t⁵/120` (`l₀ = 1`), for
which the correct `D⁴` equals the printed one at `l₀ = 0`. -/
theorem printedD4y_fails_past_h1 : necessity% Checked.Cosmography.BambaK.printedD4y_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as, al⟩ := G3_coeffs 0 0 (-1 / 120) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps, pl⟩ := P3_coeffs 0 0 (-1 / 120)
  refine ⟨1, G 1 1 0 0 (-1 / 120) 3, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by simp only [BambaK.omega0, aH, a0, aq]; norm_num, ?_⟩
  have hc := (BambaK.lumDist_y_fifth_order 1 (PQ 1 1 0 0 0 (-(-1 / 120))) 0 (PQ_smooth _ _ _ _ _ _ _)
    (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G3_past 0 0 (-1 / 120)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaK.remK, BambaK.seriesY4, BambaK.printedD4y, BambaK.correctD4y, BambaK.correctD3y,
      BambaY.correctD2y, BambaK.omega0, agree_yred hP ht, agree_lumDist hP ht, a0, aH, aq, aj, as, al,
      p0, pH, pq, pj, ps, pl]
    ring
  · filter_upwards [past_mem] with t ht
    rw [agree_yred hP ht]

/-- Smoothness is needed in `BambaA.printedDA3_fails_past`: with `K = 1`, `a = 1 + t − t²/2 + t³|t|/4` is
`C³` with `q₀ = 1`, Lean's junk fourth derivative gives `s₀ = 0`; for `t < 0` it is `1 + t − t²/2 − t⁴/4`
(`s₀ = −6`), for which the correct `D³_A` equals the printed one at `s₀ = 0`. -/
theorem printedDA3_fails_past_h1 : necessity% Checked.Cosmography.BambaA.printedDA3_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as⟩ := G2_coeffs (-1 / 2) 0 (1 / 4) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps⟩ := P2_coeffs (-1 / 2) 0 (1 / 4)
  refine ⟨1, G 1 1 (-1 / 2) 0 (1 / 4) 2, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by simp only [BambaK.omega0, aH, a0, aq]; norm_num, ?_⟩
  set Q := PQ 1 1 (-1 / 2) 0 (-(1 / 4)) 0
  have h54 := Checked.Trust.NCD.y5_y4 Q 0 (PQ_diff _ _ _ _ _ _) (by rw [p0]; norm_num)
  have hc := (((BambaA.angDist_y_fifth_order 1 Q 0 (PQ_smooth _ _ _ _ _ _ _) (by rw [p0]; norm_num)
    (by rw [pH]; norm_num)).trans h54).add (h54.const_mul_left (BambaA.correctDA4 (decel Q 0)
    (cosmoCoeff 3 Q 0) (cosmoCoeff 4 Q 0) (cosmoCoeff 5 Q 0) (BambaK.omega0 1 Q 0)))).mono
    (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G2_past (-1 / 2) 0 (1 / 4)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaA.remA, BambaA.printedDA3, BambaA.correctDA3, BambaA.DA1, BambaA.DA2,
      BambaK.omega0, agree_yred hP ht, agree_angDist hP ht, a0, aH, aq, aj, as, p0, pH, pq, pj, ps]
    ring
  · filter_upwards [past_mem] with t ht
    rw [agree_yred hP ht]

/-- Smoothness (`C⁵`) is needed in `BambaA.printedDA4_fails_past`: with `K = 1`, `a = 1 + t − t⁴|t|/120`
(`l₀ = 0` by Lean's junk value; `l₀ = 1` for its past branch `1 + t + t⁵/120`). -/
theorem printedDA4_fails_past_h1 : necessity% Checked.Cosmography.BambaA.printedDA4_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as, al⟩ := G3_coeffs 0 0 (-1 / 120) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps, pl⟩ := P3_coeffs 0 0 (-1 / 120)
  refine ⟨1, G 1 1 0 0 (-1 / 120) 3, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by simp only [BambaK.omega0, aH, a0, aq, aj]; norm_num, ?_⟩
  have hc := (BambaA.angDist_y_fifth_order 1 (PQ 1 1 0 0 0 (-(-1 / 120))) 0 (PQ_smooth _ _ _ _ _ _ _)
    (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G3_past 0 0 (-1 / 120)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaA.remA, BambaA.printedDA4, BambaA.correctDA4, BambaA.correctDA3, BambaA.printedDA3,
      BambaA.DA1, BambaA.DA2, BambaK.omega0, agree_yred hP ht, agree_angDist hP ht, a0, aH, aq, aj, as,
      al, p0, pH, pq, pj, ps, pl]
    ring
  · filter_upwards [past_mem] with t ht
    rw [agree_yred hP ht]

/-- Smoothness (`C⁵`) is needed in `BambaZ.printedDL4z_fails_past`: `K = 1`, `a = 1 + t − t⁴|t|/120`. -/
theorem printedDL4z_fails_past_h1 : necessity% Checked.Cosmography.BambaZ.printedDL4z_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as, al⟩ := G3_coeffs 0 0 (-1 / 120) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps, pl⟩ := P3_coeffs 0 0 (-1 / 120)
  refine ⟨1, G 1 1 0 0 (-1 / 120) 3, 0, by rw [a0]; norm_num, by rw [aH]; norm_num, one_ne_zero, ?_⟩
  have hc := (BambaZ.lumDist_z_fifth_order 1 (PQ 1 1 0 0 0 (-(-1 / 120))) 0 (PQ_smooth _ _ _ _ _ _ _)
    (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G3_past 0 0 (-1 / 120)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaZ.remLz, BambaZ.printedDL4z, BambaZ.correctDL4z, BambaZ.curvK,
      agree_redshift hP ht, agree_lumDist hP ht, a0, aH, aq, aj, as, al, p0, pH, pq, pj, ps, pl]
    ring_nf
  · filter_upwards [past_mem] with t ht
    rw [agree_redshift hP ht]

/-- Smoothness (`C⁵`) is needed in `BambaZ.printedDA4z_fails_past`: `K = 1`, `a = 1 + t − t⁴|t|/120`. -/
theorem printedDA4z_fails_past_h1 : necessity% Checked.Cosmography.BambaZ.printedDA4z_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as, al⟩ := G3_coeffs 0 0 (-1 / 120) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps, pl⟩ := P3_coeffs 0 0 (-1 / 120)
  refine ⟨1, G 1 1 0 0 (-1 / 120) 3, 0, by rw [a0]; norm_num, by rw [aH]; norm_num, one_ne_zero, ?_⟩
  have hc := (BambaZ.angDist_z_fifth_order 1 (PQ 1 1 0 0 0 (-(-1 / 120))) 0 (PQ_smooth _ _ _ _ _ _ _)
    (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G3_past 0 0 (-1 / 120)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaZ.remAz, BambaZ.printedDA4z, BambaZ.correctDA4z, BambaZ.curvK,
      agree_redshift hP ht, agree_angDist hP ht, a0, aH, aq, aj, as, al, p0, pH, pq, pj, ps, pl]
    ring_nf
  · filter_upwards [past_mem] with t ht
    rw [agree_redshift hP ht]

/-- Smoothness (`C⁵`) is needed in `DemianskiZ.demDL4_fails_past`: `a = 1 + t − t²/2 − (7/4) t⁴|t|`
(`q₀ = 1`, junk `l₀ = 0`); its past branch `1 + t − t²/2 + (7/4) t⁵` has `l₀ = 210`. -/
theorem demDL4_fails_past_h1 : necessity% Checked.Cosmography.DemianskiZ.demDL4_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as, al⟩ := G3_coeffs (-1 / 2) 0 (-7 / 4) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps, pl⟩ := P3_coeffs (-1 / 2) 0 (-7 / 4)
  refine ⟨G 1 1 (-1 / 2) 0 (-7 / 4) 3, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by rw [aq]; norm_num, ?_⟩
  have hc := (BambaZ.lumDist_z_fifth_order 0 (PQ 1 1 (-1 / 2) 0 0 (-(-7 / 4))) 0
    (PQ_smooth _ _ _ _ _ _ _) (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono
    (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G3_past (-1 / 2) 0 (-7 / 4)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaZ.remLz, DemianskiZ.demDL4, BambaZ.printedDL4z, BambaZ.correctDL4z, BambaZ.curvK,
      agree_redshift hP ht, agree_lumDist hP ht, a0, aH, aq, aj, as, al, p0, pH, pq, pj, ps, pl]
    ring_nf
  · filter_upwards [past_mem] with t ht
    rw [agree_redshift hP ht]

/-- Smoothness (`C⁵`) is needed in `DemianskiZ.demDA4_fails_past`: `a = 1 + t + t³/6 + (137/60) t⁴|t|`
(`j₀ = 1`, junk `l₀ = 0`); its past branch `1 + t + t³/6 − (137/60) t⁵` has `l₀ = −274`. -/
theorem demDA4_fails_past_h1 : necessity% Checked.Cosmography.DemianskiZ.demDA4_fails_past 1 := by
  obtain ⟨a0, aH, aq, aj, as, al⟩ := G3_coeffs 0 (1 / 6) (137 / 60) (by norm_num)
  obtain ⟨p0, pH, pq, pj, ps, pl⟩ := P3_coeffs 0 (1 / 6) (137 / 60)
  refine ⟨G 1 1 0 (1 / 6) (137 / 60) 3, 0, by rw [a0]; norm_num, by rw [aH]; norm_num,
    by rw [aj]; norm_num, ?_⟩
  have hc := (BambaZ.angDist_z_fifth_order 0 (PQ 1 1 0 (1 / 6) 0 (-(137 / 60))) 0
    (PQ_smooth _ _ _ _ _ _ _) (by rw [p0]; norm_num) (by rw [pH]; norm_num)).mono
    (nhdsWithin_le_nhds (s := Iio 0))
  have hP := G3_past 0 (1 / 6) (137 / 60)
  refine hc.congr' ?_ ?_
  · filter_upwards [past_mem] with t ht
    simp only [BambaZ.remAz, DemianskiZ.demDA4, BambaZ.printedDA4z, BambaZ.correctDA4z, BambaZ.curvK,
      agree_redshift hP ht, agree_angDist hP ht, a0, aH, aq, aj, as, al, p0, pH, pq, pj, ps, pl]
    ring_nf
  · filter_upwards [past_mem] with t ht
    rw [agree_redshift hP ht]

/-! ### `lookback_second_order_bigO` (two-sided, `O(z³)`) -/

/-- Smoothness (`C³` at `t₀`) is needed in `lookback_second_order_bigO`: `a = 1 + t + t|t|` has `a(0) = 1`
and `ȧ(0) = 1` (the only other hypotheses), Lean's junk second derivative at `0` gives `q₀ = 0`, and the
remainder is `t|t| + a z³`, which is not `O(z³)` (it is not even `o(z²)`). -/
theorem lookback_second_order_bigO_h1 :
    necessity% Checked.Cosmography.lookback_second_order_bigO 1 := by
  refine ⟨Checked.Trust.NCD.kink 0, 0, Checked.Trust.NCD.kink_ne 0,
    by rw [Checked.Trust.NCD.kink_deriv]; norm_num, fun h => ?_⟩
  have hH : hubble (Checked.Trust.NCD.kink 0) 0 = 1 := Checked.Trust.NCD.kink_hubble 0
  have hq : decel (Checked.Trust.NCD.kink 0) 0 = 0 := by simp [decel, Checked.Trust.NCD.kink0_deriv2]
  rw [hH, hq] at h
  have h32 : (fun t => redshift (Checked.Trust.NCD.kink 0) 0 t ^ 3) =o[𝓝 0]
      (fun t => redshift (Checked.Trust.NCD.kink 0) 0 t ^ 2) := by
    simpa using BambaY.pow_succ_mul_isLittleO (Checked.Trust.NCD.kink_z_tendsto 0) 2
      (fun _ => (1 : ℝ)) (isBigO_refl _ _)
  have hg := ((h.congr' Checked.Trust.NCD.kink0_rem EventuallyEq.rfl).trans_isLittleO h32).sub
    (Checked.Trust.NCD.kink_az 0 2)
  apply Checked.Trust.NCD.kink_not_littleO 0
  refine hg.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
  ring

end Checked.Trust.NecessityAD
