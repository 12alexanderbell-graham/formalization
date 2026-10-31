import Checked.Cosmography.LCDMWitness

/-!
# Candidates C11, C13: Bamba, Capozziello, Nojiri, Odintsov, Astrophys. Space Sci. 342, 155
(2012), arXiv:1205.3421v3, Sec. XI ("Testing F(R) gravity by cosmography"), Eqs. (11.1)–(11.31);
upstream Capozziello, Cardone, Salzano, PRD 78, 063504 (2008), arXiv:0802.1583, Eqs. (11)–(33)

Source (typeset; crops `runs/2026-10-30T1428Z/typeset/`, `runs/2026-10-30T1232Z/screen_secXI/`;
review v1–v3 identical by pdftotext of (11.31)):
* (11.1)–(11.2): `H² = (1/3)[ρ_M/F′(R) + ρ_curv]`,
  `ρ_curv = (1/F′(R))[(F(R) − R F′(R))/2 − 3H Ṙ F″(R)]`, `κ² = 1`, `ρ_M = 3H₀²Ω_M a⁻³`
  (`a(t₀) = 1`; here `ρ_M = 3H₀²Ω (a₀/a)³`).
* (11.5): `Ḣ = −(1/(2F′(R)))[3H₀²Ω_M a⁻³ + R̈ F″(R) + Ṙ(Ṙ F‴(R) − H F″(R))]`.
* (11.6): `R = −6(Ḣ + 2H²)`.
* (11.10)–(11.13): `R₀ = −6H₀²(1 − q₀)`, `Ṙ₀ = −6H₀³(j₀ − q₀ − 2)`,
  `R̈₀ = −6H₀⁴(s₀ + q₀² + 8q₀ + 6)`,
  `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]`.
* (11.17): `F′(R₀) = 1`; (11.19): `F` replaced by its cubic Taylor polynomial at `R₀`, so
  `F⁽⁴⁾(R₀) = 0`; (11.20) is the time derivative of (11.5) at `t₀`.
* (11.21): `F(R₀)/(6H₀²) = −(P₀Ω_M + Q₀)/R`; (11.23): `F″(R₀)/(6H₀²)⁻¹ = −(P₂Ω_M + Q₂)/R`;
  (11.24): `F‴(R₀)/(6H₀²)⁻² = −(P₃Ω_M + Q₃)/((j₀ − q₀ − 2)R)`; `P₀ … Q₃` (11.25)–(11.30) and
  `R` (11.31) are transcribed below verbatim.
* (11.39)–(11.40): for ΛCDM the formulas are said to give `F(R₀) = R₀ + 2Λ`, `F″ = F‴ = 0`.

Model (explicit hypotheses, `IsFRCosmo`): flat FLRW scale factor `a`, `C⁵` at `t₀`, `a(t₀) > 0`,
`H₀ > 0`; `F` is `C⁴` on ℝ; the expansion-rate equation (11.1)–(11.2) holds at `t₀` (that is
(11.14)); the master equation (11.5) holds for all `t` near `t₀` (so (11.15) and its time
derivative (11.20) hold at `t₀`); `F′(R₀) = 1` (11.17); `F⁽⁴⁾(R₀) = 0` (11.19). The two field
equations are stated multiplied by `3F′(R)` and `−2F′(R)` (equivalent wherever `F′(R) ≠ 0`, which
holds near `t₀` since `F′(R₀) = 1`). Cosmographic parameters as in `Checked.Cosmography`:
`q₀ = decel a t₀`, `j₀, s₀, l₀ = cosmoCoeff 3, 4, 5`.

Claims frozen: the printed `d³R₀/dt³` (11.13) (candidate C11) and the printed `F(R₀)` relation
(11.21) with the printed `R` (11.31) (candidate C13), the latter both as printed (division, with
`R ≠ 0` assumed so no junk value enters) and multiplied out. The F″, F‴ relations (11.23)–(11.24)
are true in ΛCDM with either `R` (both sides vanish), so they are not refuted here.

FROZEN (annex 40.1) in run 2026-10-30T1428Z before proof work (commit 4ff3816).

PROMOTED from `Work/Cosmography/FRCosmo.lean` (statements byte-identical); audit
`runs/2026-10-30T1428Z/audit.md`; blind closure `Work/Cosmography/FRCosmoAudit.lean`.
Referee notes: the division form of the printed (11.21) fails at every Ω ∈ (0,1) except
Ω ≈ 0.5383, where the printed R vanishes in ΛCDM and (11.21) is undefined; the multiplied form
fails at every Ω ∈ (0,1). Provenance: upstream 0802.1583 Eq. (33) already has the bracket sign
error and the missing `180 q₀²` (with `−18`); the review's `+18` is a further transcription
error. (11.13) has the same sign error as upstream Eq. (16).
-/

namespace Checked.Cosmography.FRCosmo

open Filter Topology Checked.Cosmography Checked.Cosmography.Aviles

/-- Ricci scalar of flat FLRW in the review's sign convention (11.6): `R = −6(Ḣ + 2H²)`. -/
noncomputable def curv (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -6 * (deriv (hubble a) t + 2 * hubble a t ^ 2)

/-- Dust density `ρ_M = 3H₀²Ω (a₀/a)³` (`κ² = 1`, text after (11.2)). -/
noncomputable def rhoM (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  3 * hubble a t₀ ^ 2 * Ω * (a t₀ / a t) ^ 3

/-- Expansion-rate equation (11.1)–(11.2) at time `t`, multiplied by `3F′(R)`. -/
def FriedmannEq (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) : Prop :=
  3 * deriv F (curv a t) * hubble a t ^ 2 =
    rhoM Ω a t₀ t + (F (curv a t) - curv a t * deriv F (curv a t)) / 2
      - 3 * hubble a t * deriv (curv a) t * deriv^[2] F (curv a t)

/-- Master equation (11.5) at time `t`, multiplied by `−2F′(R)`. -/
def MasterEq (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) : Prop :=
  -2 * deriv F (curv a t) * deriv (hubble a) t =
    rhoM Ω a t₀ t + deriv^[2] (curv a) t * deriv^[2] F (curv a t)
      + deriv (curv a) t * (deriv (curv a) t * deriv^[3] F (curv a t)
        - hubble a t * deriv^[2] F (curv a t))

/-- The setting of Eqs. (11.14)–(11.24): metric `F(R)` gravity with dust, flat FLRW, Newton's
constant today (11.17), cubic truncation of `F` at `R₀` (11.19). -/
structure IsFRCosmo (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ) : Prop where
  pos : 0 < a t₀
  expanding : 0 < hubble a t₀
  smooth_a : ContDiffAt ℝ 5 a t₀
  smooth_F : ContDiff ℝ 4 F
  friedmann : FriedmannEq Ω a F t₀ t₀
  master : ∀ᶠ t in 𝓝 t₀, MasterEq Ω a F t₀ t
  newton : deriv F (curv a t₀) = 1
  cubic : deriv^[4] F (curv a t₀) = 0

/-- `P₀` (11.25), verbatim. -/
def P0 (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s + 7 * j + 6 * q ^ 2 + 41 * q + 22) * s
    - ((3 * q + 16) * j + 20 * q ^ 2 + 64 * q + 12) * j
    - (3 * q ^ 4 + 25 * q ^ 3 + 96 * q ^ 2 + 72 * q + 20)

/-- `Q₀` (11.26), verbatim. -/
def Q0 (q j s l : ℝ) : ℝ :=
  (q ^ 2 - j * q + 2 * q) * l
    + (3 * q * s + (4 * q + 6) * j + 6 * q ^ 3 + 44 * q ^ 2 + 22 * q - 12) * s
    + (2 * j ^ 2 + (3 * q ^ 2 + 10 * q - 6) * j + 17 * q ^ 3 + 52 * q ^ 2 + 54 * q + 36) * j
    + (3 * q ^ 5 + 28 * q ^ 4 + 118 * q ^ 3 + 72 * q ^ 2 - 76 * q - 64)

/-- `P₂` (11.27), verbatim. -/
def P2 (q j s : ℝ) : ℝ := 9 * s + 6 * j + 9 * q ^ 2 + 66 * q + 42

/-- `Q₂` (11.28), verbatim. -/
def Q2 (q j s : ℝ) : ℝ :=
  -(6 * (q + 1) * s + (2 * j - 2 * (1 - q)) * j + 6 * q ^ 3 + 50 * q ^ 2 + 74 * q + 32)

/-- `P₃` (11.29), verbatim. -/
def P3 (q j s l : ℝ) : ℝ := 3 * l + 3 * s - 9 * (q + 4) * j - (45 * q ^ 2 + 78 * q + 12)

/-- `Q₃` (11.30), verbatim. -/
def Q3 (q j s l : ℝ) : ℝ :=
  -(2 * (1 + q) * l + 2 * (j + q) * s - (2 * j + 4 * q ^ 2 + 12 * q + 6) * j
    - (30 * q ^ 3 + 84 * q ^ 2 + 78 * q + 24))

/-- `R` (11.31) as printed in the review, verbatim. -/
def printedR (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    + ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q + 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 246 * q + 104)

/-- Proposed correction of (11.31) (derived in `runs/2026-10-30T1428Z/scripts/derive_fr.py`):
the bracket enters with a minus sign, `+18` is `−18`, and `180 q₀²` is missing. -/
def correctR (q j s l : ℝ) : ℝ :=
  (j - q - 2) * l - (3 * s - 2 * j + 6 * q ^ 2 + 50 * q + 40) * s
    - ((3 * q + 10) * j + 11 * q ^ 2 + 4 * q - 18) * j
    - (3 * q ^ 4 + 34 * q ^ 3 + 180 * q ^ 2 + 246 * q + 104)

/-- Printed (11.13): `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]` for every
flat FLRW scale factor (`C⁵` at `t₀`, `a(t₀) > 0`, `H₀ > 0`). -/
def PrintedR3Claim : Prop :=
  ∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → 0 < hubble a t₀ → ContDiffAt ℝ 5 a t₀ →
    deriv^[3] (curv a) t₀ = -6 * hubble a t₀ ^ 5 *
      (cosmoCoeff 5 a t₀ - cosmoCoeff 4 a t₀ + 2 * (decel a t₀ + 4) * cosmoCoeff 3 a t₀
        - 6 * (3 * decel a t₀ + 8) * decel a t₀ - 24)

/-- Printed (11.21) with printed (11.31), as printed (division; `R ≠ 0` assumed). -/
def PrintedF0Claim : Prop :=
  ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
    printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 →
    F (curv a t₀) / (6 * hubble a t₀ ^ 2) =
      -(P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
          + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
        / printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)

/-- Printed (11.21) with printed (11.31), multiplied out (no division). -/
def PrintedF0ClaimMul : Prop :=
  ∀ (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
    printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
        * F (curv a t₀) =
      -6 * hubble a t₀ ^ 2 *
        (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
          + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))

/-! ## Proof tools (helpers; not part of the frozen statements) -/

lemma key (f : ℝ → ℝ) (k : ℕ) (t : ℝ) (hk : DifferentiableAt ℝ (deriv^[k] f) t) :
    HasDerivAt (deriv^[k] f) (deriv^[k+1] f t) t := by
  simpa [Function.iterate_succ_apply'] using hk.hasDerivAt

lemma cds4 (f : ℝ → ℝ) (t : ℝ) (h : ContDiffAt ℝ 4 f t) :
    DifferentiableAt ℝ (deriv^[0] f) t ∧ DifferentiableAt ℝ (deriv^[1] f) t ∧
    DifferentiableAt ℝ (deriv^[2] f) t ∧ DifferentiableAt ℝ (deriv^[3] f) t := by
  have c3 : ContDiffAt ℝ 3 (deriv^[1] f) t := h.derivWithin (by norm_num)
  have c2 : ContDiffAt ℝ 2 (deriv^[2] f) t := by
    have := c3.derivWithin (m := 2) (by norm_num)
    simpa [Function.iterate_succ_apply'] using this
  have c1 : ContDiffAt ℝ 1 (deriv^[3] f) t := by
    have := c2.derivWithin (m := 1) (by norm_num)
    simpa [Function.iterate_succ_apply'] using this
  exact ⟨h.differentiableAt (by norm_num), c3.differentiableAt (by norm_num),
    c2.differentiableAt (by norm_num), c1.differentiableAt (by norm_num)⟩

lemma cds5 (f : ℝ → ℝ) (t : ℝ) (h : ContDiffAt ℝ 5 f t) :
    DifferentiableAt ℝ (deriv^[0] f) t ∧ DifferentiableAt ℝ (deriv^[1] f) t ∧
    DifferentiableAt ℝ (deriv^[2] f) t ∧ DifferentiableAt ℝ (deriv^[3] f) t ∧
    DifferentiableAt ℝ (deriv^[4] f) t := by
  have c4 : ContDiffAt ℝ 4 (deriv^[1] f) t := h.derivWithin (by norm_num)
  obtain ⟨-, d2, d3, d4⟩ := cds4 _ t c4
  refine ⟨h.differentiableAt (by norm_num), c4.differentiableAt (by norm_num), ?_, ?_, ?_⟩
  · simpa [← Function.iterate_succ_apply' deriv, Function.iterate_succ_apply] using d2
  · simpa [← Function.iterate_succ_apply' deriv, Function.iterate_succ_apply] using d3
  · simpa [← Function.iterate_succ_apply' deriv, Function.iterate_succ_apply] using d4

lemma hubble_contDiffAt {a : ℝ → ℝ} {t : ℝ} (hs : ContDiffAt ℝ 5 a t) (ha : a t ≠ 0) :
    ContDiffAt ℝ 4 (hubble a) t := by
  have hd : ContDiffAt ℝ 4 (deriv a) t := hs.derivWithin (by norm_num)
  exact hd.div (hs.of_le (by norm_num)) ha

/-- Eventual derivative data of `a` and `H`. -/
lemma derivData (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hs : ContDiffAt ℝ 5 a t₀) :
    ∀ᶠ t in 𝓝 t₀, 0 < a t ∧
      HasDerivAt (deriv^[0] a) (deriv^[1] a t) t ∧ HasDerivAt (deriv^[1] a) (deriv^[2] a t) t ∧
      HasDerivAt (deriv^[2] a) (deriv^[3] a t) t ∧ HasDerivAt (deriv^[3] a) (deriv^[4] a t) t ∧
      HasDerivAt (deriv^[4] a) (deriv^[5] a t) t ∧
      HasDerivAt (deriv^[0] (hubble a)) (deriv^[1] (hubble a) t) t ∧
      HasDerivAt (deriv^[1] (hubble a)) (deriv^[2] (hubble a) t) t ∧
      HasDerivAt (deriv^[2] (hubble a)) (deriv^[3] (hubble a) t) t ∧
      HasDerivAt (deriv^[3] (hubble a)) (deriv^[4] (hubble a) t) t := by
  have hpos : ∀ᶠ t in 𝓝 t₀, 0 < a t := hs.continuousAt.eventually (lt_mem_nhds ha)
  have hsm : ∀ᶠ t in 𝓝 t₀, ContDiffAt ℝ 5 a t := hs.eventually (by simp)
  filter_upwards [hpos, hsm] with t hp h
  obtain ⟨a0, a1, a2, a3, a4⟩ := cds5 a t h
  obtain ⟨b0, b1, b2, b3⟩ := cds4 _ t (hubble_contDiffAt h hp.ne')
  exact ⟨hp, key a 0 t a0, key a 1 t a1, key a 2 t a2, key a 3 t a3, key a 4 t a4,
    key _ 0 t b0, key _ 1 t b1, key _ 2 t b2, key _ 3 t b3⟩


/-- If `F` vanishes near `x` and has derivative `G` near `x`, then `G` vanishes near `x`. -/
lemma step {F G : ℝ → ℝ} {x : ℝ} (hF : ∀ᶠ t in 𝓝 x, F t = 0)
    (hG : ∀ᶠ t in 𝓝 x, HasDerivAt F (G t) t) : ∀ᶠ t in 𝓝 x, G t = 0 := by
  filter_upwards [hF.eventually_nhds, hG] with t hFt hGt
  have h : F =ᶠ[𝓝 t] fun _ => (0 : ℝ) := hFt
  rw [← hGt.deriv, h.deriv_eq]
  simp

/-- Derivatives of `H` at `t₀` from the cosmographic parameters (the review's (10.6)–(10.9)). -/
lemma hvals (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hH : 0 < hubble a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    deriv^[1] (hubble a) t₀ = -hubble a t₀ ^ 2 * (1 + decel a t₀) ∧
    deriv^[2] (hubble a) t₀ = hubble a t₀ ^ 3 * (cosmoCoeff 3 a t₀ + 3 * decel a t₀ + 2) ∧
    deriv^[3] (hubble a) t₀ = -hubble a t₀ ^ 4 * (4 * cosmoCoeff 3 a t₀ + 3 * decel a t₀ ^ 2
      + 12 * decel a t₀ - cosmoCoeff 4 a t₀ + 6) ∧
    deriv^[4] (hubble a) t₀ = hubble a t₀ ^ 5 * (10 * cosmoCoeff 3 a t₀ * decel a t₀
      + 20 * cosmoCoeff 3 a t₀ + cosmoCoeff 5 a t₀ + 30 * decel a t₀ ^ 2 + 60 * decel a t₀
      - 5 * cosmoCoeff 4 a t₀ + 24) := by
  set D : ℕ → ℝ → ℝ := fun k => deriv^[k] a with hD
  set h : ℕ → ℝ → ℝ := fun k => deriv^[k] (hubble a) with hh
  have hd := derivData a t₀ ha hs
  have G0 : ∀ᶠ t in 𝓝 t₀, D 1 t - h 0 t * D 0 t = 0 := by
    filter_upwards [hd] with t ⟨hp, _⟩
    simp only [hD, hh, Function.iterate_zero, id, Function.iterate_one, hubble]
    field_simp
    ring
  have G1 := step G0 (G := fun t => D 2 t - (h 1 t * D 0 t + h 0 t * D 1 t)) (by
    filter_upwards [hd] with t ⟨_, d0, d1, _, _, _, h0, _⟩
    exact d1.sub (h0.mul d0))
  have G2 := step G1 (G := fun t => D 3 t - (h 2 t * D 0 t + 2 * h 1 t * D 1 t + h 0 t * D 2 t)) (by
    filter_upwards [hd] with t ⟨_, d0, d1, d2, _, _, h0, h1, _⟩
    exact (d2.sub ((h1.mul d0).add (h0.mul d1))).congr_deriv (by ring))
  have G3 := step G2 (G := fun t => D 4 t - (h 3 t * D 0 t + 3 * h 2 t * D 1 t
      + 3 * h 1 t * D 2 t + h 0 t * D 3 t)) (by
    filter_upwards [hd] with t ⟨_, d0, d1, d2, d3, _, h0, h1, h2, _⟩
    exact (d3.sub (((h2.mul d0).add ((h1.const_mul 2).mul d1)).add (h0.mul d2))).congr_deriv
      (by ring))
  have G4 := step G3 (G := fun t => D 5 t - (h 4 t * D 0 t + 4 * h 3 t * D 1 t
      + 6 * h 2 t * D 2 t + 4 * h 1 t * D 3 t + h 0 t * D 4 t)) (by
    filter_upwards [hd] with t ⟨_, d0, d1, d2, d3, d4, h0, h1, h2, h3⟩
    exact (d4.sub ((((h3.mul d0).add ((h2.const_mul 3).mul d1)).add ((h1.const_mul 3).mul d2)).add
      (h0.mul d3))).congr_deriv (by ring))
  have e1 := G1.self_of_nhds
  have e2 := G2.self_of_nhds
  have e3 := G3.self_of_nhds
  have e4 := G4.self_of_nhds
  simp only [hD, hh, Function.iterate_zero, id_eq, Function.iterate_one] at e1 e2 e3 e4
  have hA : a t₀ ≠ 0 := ha.ne'
  have hd1 : deriv a t₀ = hubble a t₀ * a t₀ := by rw [hubble]; field_simp
  have hd2 : deriv^[2] a t₀ = -decel a t₀ * a t₀ * hubble a t₀ ^ 2 := by
    have h2 : deriv^[2] a t₀ = deriv (deriv a) t₀ := rfl
    have : deriv a t₀ ≠ 0 := by rw [hd1]; positivity
    rw [h2, decel, hd1]
    field_simp
  have hc : ∀ n, deriv^[n] a t₀ = cosmoCoeff n a t₀ * a t₀ * hubble a t₀ ^ n := by
    intro n
    rw [cosmoCoeff, iteratedDeriv_eq_iterate]
    field_simp
  simp only [hd1, hd2, hc 3, hc 4, hc 5] at e1 e2 e3 e4
  simp only [Function.iterate_one]
  have h1v : deriv (hubble a) t₀ = -hubble a t₀ ^ 2 * (1 + decel a t₀) := by
    apply mul_left_cancel₀ hA
    linear_combination (-1) * e1
  simp only [h1v] at e2 e3 e4
  have h2v : deriv^[2] (hubble a) t₀ =
      hubble a t₀ ^ 3 * (cosmoCoeff 3 a t₀ + 3 * decel a t₀ + 2) := by
    apply mul_left_cancel₀ hA
    linear_combination (-1) * e2
  simp only [h2v] at e3 e4
  have h3v : deriv^[3] (hubble a) t₀ = -hubble a t₀ ^ 4 * (4 * cosmoCoeff 3 a t₀
      + 3 * decel a t₀ ^ 2 + 12 * decel a t₀ - cosmoCoeff 4 a t₀ + 6) := by
    apply mul_left_cancel₀ hA
    linear_combination (-1) * e3
  simp only [h3v] at e4
  refine ⟨h1v, h2v, h3v, ?_⟩
  apply mul_left_cancel₀ hA
  linear_combination (-1) * e4


/-- Algebra of the closure system: (11.14), (11.15), (11.20) with `F′ = 1`, `F⁽⁴⁾ = 0`, the
`H`-derivatives written through `(q₀, j₀, s₀, l₀)`. Certificates from
`runs/2026-10-30T1428Z/scripts/cert_lean.py`. -/
lemma alg (q j s l H Ω x0 x2 x3 : ℝ) (hH : H ≠ 0)
    (e1 : 3 * H ^ 2 = 3 * H ^ 2 * Ω + (x0 - (-6 * ((-H ^ 2 * (1 + q)) + 2 * H ^ 2))) / 2 - 3 * H * (-6 * ((H ^ 3 * (j + 3 * q + 2)) + 4 * H * (-H ^ 2 * (1 + q)))) * x2)
    (e2 : -2 * (-H ^ 2 * (1 + q)) = 3 * H ^ 2 * Ω + (-6 * ((-H ^ 4 * (4 * j + 3 * q ^ 2 + 12 * q - s + 6)) + 4 * (-H ^ 2 * (1 + q)) ^ 2 + 4 * H * (H ^ 3 * (j + 3 * q + 2)))) * x2 + (-6 * ((H ^ 3 * (j + 3 * q + 2)) + 4 * H * (-H ^ 2 * (1 + q)))) * ((-6 * ((H ^ 3 * (j + 3 * q + 2)) + 4 * H * (-H ^ 2 * (1 + q)))) * x3 - H * x2))
    (e3 : -2 * x2 * (-6 * ((H ^ 3 * (j + 3 * q + 2)) + 4 * H * (-H ^ 2 * (1 + q)))) * (-H ^ 2 * (1 + q)) - 2 * (H ^ 3 * (j + 3 * q + 2)) = -3 * H * (3 * H ^ 2 * Ω) + (-6 * ((H ^ 5 * (10 * j * q + 20 * j + l + 30 * q ^ 2 + 60 * q - 5 * s + 24)) + 12 * (-H ^ 2 * (1 + q)) * (H ^ 3 * (j + 3 * q + 2)) + 4 * H * (-H ^ 4 * (4 * j + 3 * q ^ 2 + 12 * q - s + 6)))) * x2 + 3 * (-6 * ((H ^ 3 * (j + 3 * q + 2)) + 4 * H * (-H ^ 2 * (1 + q)))) * (-6 * ((-H ^ 4 * (4 * j + 3 * q ^ 2 + 12 * q - s + 6)) + 4 * (-H ^ 2 * (1 + q)) ^ 2 + 4 * H * (H ^ 3 * (j + 3 * q + 2)))) * x3 - (-H ^ 2 * (1 + q)) * (-6 * ((H ^ 3 * (j + 3 * q + 2)) + 4 * H * (-H ^ 2 * (1 + q)))) * x2 - H * (-6 * ((-H ^ 4 * (4 * j + 3 * q ^ 2 + 12 * q - s + 6)) + 4 * (-H ^ 2 * (1 + q)) ^ 2 + 4 * H * (H ^ 3 * (j + 3 * q + 2)))) * x2 - H * (-6 * ((H ^ 3 * (j + 3 * q + 2)) + 4 * H * (-H ^ 2 * (1 + q)))) ^ 2 * x3) :
    correctR q j s l * x0 = -6 * H ^ 2 * (P0 q j s l * Ω + Q0 q j s l) ∧
    correctR q j s l * (6 * H ^ 2) * x2 = -(P2 q j s * Ω + Q2 q j s) ∧
    (j - q - 2) * correctR q j s l * (6 * H ^ 2) ^ 2 * x3 = -(P3 q j s l * Ω + Q3 q j s l) := by
  have h3 : H ^ 3 ≠ 0 := pow_ne_zero 3 hH
  refine ⟨?_, ?_, ?_⟩
  · apply mul_left_cancel₀ h3
    simp only [correctR, P0, Q0]
    linear_combination (6*H^3*j^2*q + 20*H^3*j^2 - 2*H^3*j*l + 22*H^3*j*q^2 + 8*H^3*j*q - 4*H^3*j*s - 36*H^3*j + 2*H^3*l*q + 4*H^3*l + 6*H^3*q^4 + 68*H^3*q^3 + 12*H^3*q^2*s + 360*H^3*q^2 + 100*H^3*q*s + 492*H^3*q + 6*H^3*s^2 + 80*H^3*s + 208*H^3) * e1 + (-6*H^3*j^2 + 18*H^3*j*q^2 + 156*H^3*j*q + 18*H^3*j*s + 132*H^3*j - 18*H^3*q^3 - 186*H^3*q^2 - 18*H^3*q*s - 420*H^3*q - 36*H^3*s - 240*H^3) * e2 + (-6*H^2*j^2 + 12*H^2*j*q + 24*H^2*j - 6*H^2*q^2 - 24*H^2*q - 24*H^2) * e3
  · apply mul_left_cancel₀ h3
    simp only [correctR, P2, Q2]
    linear_combination (0) * e1 + (H*j - 3*H*q^2 - 25*H*q - 3*H*s - 20*H) * e2 + (j - q - 2) * e3
  · apply mul_left_cancel₀ h3
    simp only [correctR, P3, Q3]
    linear_combination (0) * e1 + (3*H*j*q + 9*H*j - H*l + 18*H*q^2 + 53*H*q + 2*H*s + 28*H) * e2 + (-j + q^2 + 9*q + s + 8) * e3

/-- `R`, `Ṙ`, `R̈` near `t₀` and `d³R/dt³` at `t₀` through the derivatives of `H` ((11.6)–(11.9)). -/
lemma curvData (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hs : ContDiffAt ℝ 5 a t₀) :
    (∀ᶠ t in 𝓝 t₀, HasDerivAt (curv a) (-6 * (deriv^[2] (hubble a) t
        + 4 * deriv^[0] (hubble a) t * deriv^[1] (hubble a) t)) t) ∧
    (∀ᶠ t in 𝓝 t₀, deriv (curv a) t = -6 * (deriv^[2] (hubble a) t
        + 4 * deriv^[0] (hubble a) t * deriv^[1] (hubble a) t)) ∧
    (∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => -6 * (deriv^[2] (hubble a) t
        + 4 * deriv^[0] (hubble a) t * deriv^[1] (hubble a) t))
        (-6 * (deriv^[3] (hubble a) t + 4 * deriv^[1] (hubble a) t ^ 2
          + 4 * deriv^[0] (hubble a) t * deriv^[2] (hubble a) t)) t) ∧
    (∀ᶠ t in 𝓝 t₀, deriv^[2] (curv a) t = -6 * (deriv^[3] (hubble a) t
        + 4 * deriv^[1] (hubble a) t ^ 2 + 4 * deriv^[0] (hubble a) t * deriv^[2] (hubble a) t)) ∧
    (∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => -6 * (deriv^[3] (hubble a) t
        + 4 * deriv^[1] (hubble a) t ^ 2 + 4 * deriv^[0] (hubble a) t * deriv^[2] (hubble a) t))
        (-6 * (deriv^[4] (hubble a) t + 12 * deriv^[1] (hubble a) t * deriv^[2] (hubble a) t
          + 4 * deriv^[0] (hubble a) t * deriv^[3] (hubble a) t)) t) := by
  have hd := derivData a t₀ ha hs
  have hc : curv a = fun t => -6 * (deriv^[1] (hubble a) t + 2 * deriv^[0] (hubble a) t ^ 2) := rfl
  have D1 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (curv a) (-6 * (deriv^[2] (hubble a) t
        + 4 * deriv^[0] (hubble a) t * deriv^[1] (hubble a) t)) t := by
    filter_upwards [hd] with t ⟨_, _, _, _, _, _, h0, h1, _, _⟩
    rw [hc]
    exact ((h1.add ((h0.pow 2).const_mul 2)).const_mul (-6)).congr_deriv (by push_cast; ring)
  have E1 : ∀ᶠ t in 𝓝 t₀, deriv (curv a) t = -6 * (deriv^[2] (hubble a) t
        + 4 * deriv^[0] (hubble a) t * deriv^[1] (hubble a) t) := by
    filter_upwards [D1] with t h using h.deriv
  have D2 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => -6 * (deriv^[2] (hubble a) t
        + 4 * deriv^[0] (hubble a) t * deriv^[1] (hubble a) t))
        (-6 * (deriv^[3] (hubble a) t + 4 * deriv^[1] (hubble a) t ^ 2
          + 4 * deriv^[0] (hubble a) t * deriv^[2] (hubble a) t)) t := by
    filter_upwards [hd] with t ⟨_, _, _, _, _, _, h0, h1, h2, _⟩
    exact ((h2.add ((h0.const_mul 4).mul h1)).const_mul (-6)).congr_deriv (by ring)
  have E2 : ∀ᶠ t in 𝓝 t₀, deriv^[2] (curv a) t = -6 * (deriv^[3] (hubble a) t
        + 4 * deriv^[1] (hubble a) t ^ 2 + 4 * deriv^[0] (hubble a) t * deriv^[2] (hubble a) t) := by
    filter_upwards [E1.eventually_nhds, D2] with t h hD
    rw [Function.iterate_succ_apply', Function.iterate_one]
    exact (Filter.EventuallyEq.deriv_eq h).trans hD.deriv
  have D3 : ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t => -6 * (deriv^[3] (hubble a) t
        + 4 * deriv^[1] (hubble a) t ^ 2 + 4 * deriv^[0] (hubble a) t * deriv^[2] (hubble a) t))
        (-6 * (deriv^[4] (hubble a) t + 12 * deriv^[1] (hubble a) t * deriv^[2] (hubble a) t
          + 4 * deriv^[0] (hubble a) t * deriv^[3] (hubble a) t)) t := by
    filter_upwards [hd] with t ⟨_, _, _, _, _, _, h0, h1, h2, h3⟩
    exact (((h3.add ((h1.pow 2).const_mul 4)).add ((h0.const_mul 4).mul h2)).const_mul (-6)).congr_deriv
      (by push_cast; ring)
  exact ⟨D1, E1, D2, E2, D3⟩

lemma deriv3_curv (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hs : ContDiffAt ℝ 5 a t₀) :
    deriv^[3] (curv a) t₀ = -6 * (deriv^[4] (hubble a) t₀
      + 12 * deriv^[1] (hubble a) t₀ * deriv^[2] (hubble a) t₀
      + 4 * deriv^[0] (hubble a) t₀ * deriv^[3] (hubble a) t₀) := by
  obtain ⟨-, -, -, E2, D3⟩ := curvData a t₀ ha hs
  rw [Function.iterate_succ_apply']
  exact (Filter.EventuallyEq.deriv_eq E2).trans D3.self_of_nhds.deriv

/-- **Correct (11.10)–(11.13).** For every flat FLRW scale factor `C⁵` at `t₀` with `a(t₀) > 0`, `H₀ > 0`,
the Ricci scalar `R = −6(Ḣ + 2H²)` (the review's sign convention) and its first three time derivatives
at `t₀`: `R₀ = −6H₀²(1 − q₀)`, `Ṙ₀ = −6H₀³(j₀ − q₀ − 2)`, `R̈₀ = −6H₀⁴(s₀ + q₀² + 8q₀ + 6)`,
`R⃛₀ = −6H₀⁵[l₀ − s₀ − 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]` (the review's (11.13) prints `+2(q₀ + 4)j₀`). -/
theorem curv_derivs (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hH : 0 < hubble a t₀)
    (hs : ContDiffAt ℝ 5 a t₀) :
    curv a t₀ = -6 * hubble a t₀ ^ 2 * (1 - decel a t₀) ∧
    deriv (curv a) t₀ = -6 * hubble a t₀ ^ 3 * (cosmoCoeff 3 a t₀ - decel a t₀ - 2) ∧
    deriv^[2] (curv a) t₀ =
      -6 * hubble a t₀ ^ 4 * (cosmoCoeff 4 a t₀ + decel a t₀ ^ 2 + 8 * decel a t₀ + 6) ∧
    deriv^[3] (curv a) t₀ = -6 * hubble a t₀ ^ 5 *
      (cosmoCoeff 5 a t₀ - cosmoCoeff 4 a t₀ - 2 * (decel a t₀ + 4) * cosmoCoeff 3 a t₀
        - 6 * (3 * decel a t₀ + 8) * decel a t₀ - 24) := by
  obtain ⟨h1v, h2v, h3v, h4v⟩ := hvals a t₀ ha hH hs
  obtain ⟨-, E1, -, E2, -⟩ := curvData a t₀ ha hs
  have h3 := deriv3_curv a t₀ ha hs
  simp only [Function.iterate_one, Function.iterate_zero, id_eq] at h1v E1 E2 h3 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · show -6 * (deriv (hubble a) t₀ + 2 * hubble a t₀ ^ 2) = _
    rw [h1v]; ring
  · rw [E1.self_of_nhds, h2v, h1v]; ring
  · rw [E2.self_of_nhds, h3v, h1v, h2v]; ring
  · rw [h3, h4v, h1v, h2v, h3v]; ring

/-- The closure system at `t₀`: (11.14), (11.15) and the time derivative of (11.5) ((11.20),
with the correct `−Ḣ₀Ṙ₀`), using `F′(R₀) = 1`, `F⁽⁴⁾(R₀) = 0`. -/
lemma closure (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ) (hM : IsFRCosmo Ω a F t₀) :
    (3 * hubble a t₀ ^ 2 = 3 * hubble a t₀ ^ 2 * Ω + (F (curv a t₀) - (-6 * ((deriv^[1] (hubble a) t₀) + 2 * hubble a t₀ ^ 2))) / 2 - 3 * hubble a t₀ * (-6 * ((deriv^[2] (hubble a) t₀) + 4 * hubble a t₀ * (deriv^[1] (hubble a) t₀))) * deriv^[2] F (curv a t₀)) ∧
    (-2 * (deriv^[1] (hubble a) t₀) = 3 * hubble a t₀ ^ 2 * Ω + (-6 * ((deriv^[3] (hubble a) t₀) + 4 * (deriv^[1] (hubble a) t₀) ^ 2 + 4 * hubble a t₀ * (deriv^[2] (hubble a) t₀))) * deriv^[2] F (curv a t₀) + (-6 * ((deriv^[2] (hubble a) t₀) + 4 * hubble a t₀ * (deriv^[1] (hubble a) t₀))) * ((-6 * ((deriv^[2] (hubble a) t₀) + 4 * hubble a t₀ * (deriv^[1] (hubble a) t₀))) * deriv^[3] F (curv a t₀) - hubble a t₀ * deriv^[2] F (curv a t₀))) ∧
    (-2 * deriv^[2] F (curv a t₀) * (-6 * ((deriv^[2] (hubble a) t₀) + 4 * hubble a t₀ * (deriv^[1] (hubble a) t₀))) * (deriv^[1] (hubble a) t₀) - 2 * (deriv^[2] (hubble a) t₀) = -3 * hubble a t₀ * (3 * hubble a t₀ ^ 2 * Ω) + (-6 * ((deriv^[4] (hubble a) t₀) + 12 * (deriv^[1] (hubble a) t₀) * (deriv^[2] (hubble a) t₀) + 4 * hubble a t₀ * (deriv^[3] (hubble a) t₀))) * deriv^[2] F (curv a t₀) + 3 * (-6 * ((deriv^[2] (hubble a) t₀) + 4 * hubble a t₀ * (deriv^[1] (hubble a) t₀))) * (-6 * ((deriv^[3] (hubble a) t₀) + 4 * (deriv^[1] (hubble a) t₀) ^ 2 + 4 * hubble a t₀ * (deriv^[2] (hubble a) t₀))) * deriv^[3] F (curv a t₀) - (deriv^[1] (hubble a) t₀) * (-6 * ((deriv^[2] (hubble a) t₀) + 4 * hubble a t₀ * (deriv^[1] (hubble a) t₀))) * deriv^[2] F (curv a t₀) - hubble a t₀ * (-6 * ((deriv^[3] (hubble a) t₀) + 4 * (deriv^[1] (hubble a) t₀) ^ 2 + 4 * hubble a t₀ * (deriv^[2] (hubble a) t₀))) * deriv^[2] F (curv a t₀) - hubble a t₀ * (-6 * ((deriv^[2] (hubble a) t₀) + 4 * hubble a t₀ * (deriv^[1] (hubble a) t₀))) ^ 2 * deriv^[3] F (curv a t₀)) := by
  obtain ⟨ha, hH, hs, hF, hfr, hmas, hnew, hcub⟩ := hM
  obtain ⟨D1, E1, D2, E2, D3⟩ := curvData a t₀ ha hs
  have hd := derivData a t₀ ha hs
  have hFd : ∀ x, HasDerivAt (deriv^[0] F) (deriv^[1] F x) x ∧
      HasDerivAt (deriv^[1] F) (deriv^[2] F x) x ∧ HasDerivAt (deriv^[2] F) (deriv^[3] F x) x ∧
      HasDerivAt (deriv^[3] F) (deriv^[4] F x) x := by
    intro x
    obtain ⟨b0, b1, b2, b3⟩ := cds4 F x hF.contDiffAt
    exact ⟨key F 0 x b0, key F 1 x b1, key F 2 x b2, key F 3 x b3⟩
  have hR0 : curv a t₀ = -6 * (deriv^[1] (hubble a) t₀ + 2 * hubble a t₀ ^ 2) := rfl
  have hrho : rhoM Ω a t₀ t₀ = 3 * hubble a t₀ ^ 2 * Ω := by
    simp [rhoM, div_self ha.ne']
  refine ⟨?_, ?_, ?_⟩
  · unfold FriedmannEq at hfr
    rw [hnew, E1.self_of_nhds, hrho] at hfr
    simp only [Function.iterate_zero, id_eq] at hfr ⊢
    linear_combination hfr - (1 / 2 : ℝ) * hR0
  · have hm := hmas.self_of_nhds
    unfold MasterEq at hm
    rw [hnew, E1.self_of_nhds, E2.self_of_nhds, hrho] at hm
    simp only [Function.iterate_zero, Function.iterate_one, id_eq] at hm ⊢
    linear_combination hm
  · obtain ⟨_, d0, _, _, _, _, h0d, h1d, _, _⟩ := hd.self_of_nhds
    have cR := D1.self_of_nhds
    have f1 := (hFd (curv a t₀)).2.1.comp t₀ cR
    have f2 := (hFd (curv a t₀)).2.2.1.comp t₀ cR
    have f3 := (hFd (curv a t₀)).2.2.2.comp t₀ cR
    have ad : HasDerivAt a (deriv^[1] a t₀) t₀ := d0
    have hrd := (((hasDerivAt_const t₀ (a t₀)).div ad ha.ne').pow 3).const_mul
      (3 * hubble a t₀ ^ 2 * Ω)
    have hG := ((f1.const_mul (-2)).mul h1d).sub
      ((hrd.add (D3.self_of_nhds.mul f2)).add
        (D2.self_of_nhds.mul ((D2.self_of_nhds.mul f3).sub (h0d.mul f2))))
    have h0 := hG.unique ((hasDerivAt_const t₀ (0 : ℝ)).congr_of_eventuallyEq ?_)
    · have hd1 : deriv^[1] a t₀ = hubble a t₀ * a t₀ := by
        simp only [Function.iterate_one, hubble]; field_simp
      rw [hd1, hcub] at h0
      simp only [Function.comp, Function.iterate_zero, id_eq, Function.iterate_one, hnew,
        Pi.div_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, div_self ha.ne', one_pow, mul_one] at h0 ⊢
      push_cast at h0
      field_simp at h0
      apply mul_left_cancel₀ ha.ne'
      linear_combination (1 : ℝ) * h0
    · filter_upwards [hmas, E1, E2] with t hm e1 e2
      unfold MasterEq rhoM at hm
      rw [e1, e2] at hm
      simp only [Function.comp, Function.iterate_zero, Function.iterate_one, id_eq, Pi.mul_apply,
        Pi.sub_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply] at hm ⊢
      linear_combination hm

/-- **Correct (11.21), (11.23), (11.24)** (multiplied out; no nondegeneracy needed). -/
theorem fR_values (Ω : ℝ) (a F : ℝ → ℝ) (t₀ : ℝ) (hM : IsFRCosmo Ω a F t₀) :
    correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
        * F (curv a t₀) =
      -6 * hubble a t₀ ^ 2 *
        (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
          + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) ∧
    correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
        * (6 * hubble a t₀ ^ 2) * deriv^[2] F (curv a t₀) =
      -(P2 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) * Ω
          + Q2 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀)) ∧
    (cosmoCoeff 3 a t₀ - decel a t₀ - 2)
        * correctR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
        * (6 * hubble a t₀ ^ 2) ^ 2 * deriv^[3] F (curv a t₀) =
      -(P3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
          + Q3 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) := by
  obtain ⟨e1, e2, e3⟩ := closure Ω a F t₀ hM
  obtain ⟨h1v, h2v, h3v, h4v⟩ := hvals a t₀ hM.pos hM.expanding hM.smooth_a
  simp only [h1v, h2v, h3v, h4v] at e1 e2 e3
  exact alg _ _ _ _ _ _ _ _ _ hM.expanding.ne' (by linear_combination e1) (by linear_combination e2)
    (by linear_combination e3)

/-! ## ΛCDM witness ((11.39)–(11.40)) -/

section
open Real Checked.Cosmography.AvilesWitness

lemma deriv_hubble_lam {t : ℝ} (ht : 0 < t) : deriv (hubble lam) t = -(2 / 3) / sinh t ^ 2 := by
  have hs : 0 < sinh t := sinh_pos_iff.2 ht
  have heq : hubble lam =ᶠ[𝓝 t] fun u => 2 / 3 * cosh u / sinh u := by
    filter_upwards [lt_mem_nhds ht] with u hu using hubble_lam hu
  rw [heq.deriv_eq]
  have hd := ((hasDerivAt_cosh t).const_mul (2 / 3 : ℝ)).div (hasDerivAt_sinh t) hs.ne'
  have hd' : deriv (fun u => 2 / 3 * cosh u / sinh u) t = _ := hd.deriv
  rw [hd']
  have h1 := cosh_sq t
  field_simp
  linear_combination (-1 : ℝ) * h1

lemma iter_affine (c : ℝ) : deriv (fun R : ℝ => R + c) = (fun _ => 1) ∧
    ∀ k, deriv^[k + 2] (fun R : ℝ => R + c) = (fun _ => 0) := by
  have h1 : deriv (fun R : ℝ => R + c) = fun _ => 1 := by
    funext x; simp
  refine ⟨h1, ?_⟩
  intro k
  induction k with
  | zero => simp [h1]
  | succ n ih => rw [Function.iterate_succ_apply', ih]; funext x; simp

theorem lcdm_witness {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ ∧ ContDiffAt ℝ 6 a t₀ ∧
      IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀ := by
  set u := √(1 / Ω - 1) with hu
  have hu0 : 0 < u := sqrt_pos.2 (by rw [lt_sub_iff_add_lt, zero_add, lt_div_iff₀ h0]; linarith)
  set t₀ := arsinh u
  have ht0 : 0 < t₀ := arsinh_pos_iff.2 hu0
  have hΩ : 1 / cosh t₀ ^ 2 = Ω := by
    rw [cosh_sq, sinh_arsinh, hu, sq_sqrt (by rw [sub_nonneg, le_div_iff₀ h0]; linarith)]
    field_simp
    ring
  have hs6 : ContDiffAt ℝ 6 lam t₀ :=
    (contDiff_sinh.contDiffAt).rpow_const_of_ne (sinh_pos_iff.2 ht0).ne'
  have hs0 : 0 < sinh t₀ := sinh_pos_iff.2 ht0
  have hc0 : 0 < cosh t₀ := cosh_pos t₀
  obtain ⟨hF1, hFk⟩ := iter_affine (6 * hubble lam t₀ ^ 2 * (1 - Ω))
  have hF2 := hFk 0
  have hF3 := hFk 1
  have hF4 := hFk 2
  simp only [zero_add, Nat.reduceAdd] at hF2 hF3 hF4
  have hl0 : 0 < lam t₀ := rpow_pos_of_pos hs0 _
  refine ⟨lam, t₀, hΩ ▸ lam_isFlatLCDM ht0, hs6, ?_⟩
  refine ⟨rpow_pos_of_pos hs0 _, by rw [hubble_lam ht0]; positivity, hs6.of_le (by norm_num),
    contDiff_id.add contDiff_const, ?_, ?_, by rw [hF1], by rw [hF4]⟩
  · unfold FriedmannEq rhoM
    simp only [hF1, hF2, div_self hl0.ne', one_pow]
    ring
  · filter_upwards [lt_mem_nhds ht0] with t ht
    have hs : 0 < sinh t := sinh_pos_iff.2 ht
    unfold MasterEq rhoM
    simp only [hF1, hF2, hF3]
    rw [deriv_hubble_lam ht, hubble_lam ht0, div_pow (lam t₀), lam_cube ht0, lam_cube ht, ← hΩ]
    field_simp
    ring

end

/-- ΛCDM data used by the refutations: the witness, its cosmographic parameters ((11.39)) and
`R₀`. -/
lemma lcdm_facts {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀ ∧
      decel a t₀ = 3 / 2 * Ω - 1 ∧ cosmoCoeff 3 a t₀ = 1 ∧ cosmoCoeff 4 a t₀ = 1 - 9 / 2 * Ω ∧
      cosmoCoeff 5 a t₀ = 1 + 3 * Ω + 27 / 2 * Ω ^ 2 ∧
      curv a t₀ = -6 * hubble a t₀ ^ 2 * (1 - (3 / 2 * Ω - 1)) := by
  obtain ⟨a, t₀, hL, h6, hM⟩ := lcdm_witness h0 h1
  obtain ⟨hq, hj, hs, hl, -⟩ := flatLCDM_coeffs Ω a t₀ hL h6
  obtain ⟨hR0, -, -, -⟩ := curv_derivs a t₀ hM.pos hM.expanding hM.smooth_a
  exact ⟨a, t₀, hM, hq, hj, hs, hl, by rw [hR0, hq]⟩

lemma quad_pos (Ω : ℝ) : 0 < 909 * Ω ^ 2 - 1170 * Ω + 416 := by
  nlinarith [sq_nonneg (Ω - 585 / 909)]

/-- (11.40), the paper's own check: for every `Ω ∈ (0,1)` there is a flat ΛCDM scale factor
which, with `F(R) = R + 2Λ`, `Λ = 3H₀²(1 − Ω)`, satisfies every hypothesis of `IsFRCosmo`. -/
theorem exists_LCDM_model {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ∃ (a : ℝ → ℝ) (t₀ : ℝ), IsFlatLCDM Ω a t₀ ∧
      IsFRCosmo Ω a (fun R => R + 6 * hubble a t₀ ^ 2 * (1 - Ω)) t₀ := by
  obtain ⟨a, t₀, hL, -, hM⟩ := lcdm_witness h0 h1
  exact ⟨a, t₀, hL, hM⟩

/-- The review's (11.13), `d³R₀/dt³ = −6H₀⁵[l₀ − s₀ + 2(q₀ + 4)j₀ − 6(3q₀ + 8)q₀ − 24]`, does not hold for
every flat FLRW scale factor `C⁵` at `t₀` with `a(t₀) > 0`, `H₀ > 0` (the correct term is
`−2(q₀ + 4)j₀`: `curv_derivs`). -/
theorem printedR3Claim_false : ¬ PrintedR3Claim := by
  intro h
  obtain ⟨a, t₀, hM, hq, hj, -, -, -⟩ := lcdm_facts (Ω := 1 / 4) (by norm_num) (by norm_num)
  have e := h a t₀ hM.pos hM.expanding hM.smooth_a
  obtain ⟨-, -, -, hR3⟩ := curv_derivs a t₀ hM.pos hM.expanding hM.smooth_a
  rw [hR3, hq, hj] at e
  have hH := hM.expanding
  have : hubble a t₀ ^ 5 * 81 = 0 := by linear_combination e
  have : 0 < hubble a t₀ ^ 5 * 81 := by positivity
  linarith

/-- The multiplied-out printed relation fails in ΛCDM at every `Ω ∈ (0,1)`. -/
theorem printedF0Mul_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)
          * F (curv a t₀) =
        -6 * hubble a t₀ ^ 2 *
          (P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)) := by
  intro h
  obtain ⟨a, t₀, hM, hq, hj, hs, hl, hR0⟩ := lcdm_facts h0 h1
  have e := h a _ t₀ hM
  rw [hq, hj, hs, hl, hR0] at e
  simp only [printedR, P0, Q0] at e
  have hH := hM.expanding
  have k : hubble a t₀ ^ 2 * ((2 - Ω) * (909 * Ω ^ 2 - 1170 * Ω + 416)) = 0 := by
    linear_combination (-2 / 3 : ℝ) * e
  have : 0 < hubble a t₀ ^ 2 * ((2 - Ω) * (909 * Ω ^ 2 - 1170 * Ω + 416)) := by
    have := quad_pos Ω
    have : 0 < 2 - Ω := by linarith
    positivity
  linarith

/-- The review's (11.21) with its printed common denominator `R` (11.31), multiplied out
(`R·F(R₀) = −6H₀²(P₀Ω + Q₀)`, no division), does not hold for every F(R) cosmology satisfying the
paper's field equations (`IsFRCosmo`). -/
theorem printedF0ClaimMul_false : ¬ PrintedF0ClaimMul := by
  intro h
  exact printedF0Mul_false_at (Ω := 1 / 4) (by norm_num) (by norm_num) (fun a F t₀ hM => h _ a F t₀ hM)


/-- Division form at every `Ω ∈ (0,1)` where the printed `R` is nonzero in ΛCDM
(`printedR` at ΛCDM is `−(243Ω⁴ + 540Ω³ − 6264Ω² + 9360Ω − 3328)/16`). -/
theorem printedF0_false_at {Ω : ℝ} (h0 : 0 < Ω) (h1 : Ω < 1)
    (hR : 243 * Ω ^ 4 + 540 * Ω ^ 3 - 6264 * Ω ^ 2 + 9360 * Ω - 3328 ≠ 0) :
    ¬ ∀ (a F : ℝ → ℝ) (t₀ : ℝ), IsFRCosmo Ω a F t₀ →
      printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 →
      F (curv a t₀) / (6 * hubble a t₀ ^ 2) =
        -(P0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) * Ω
            + Q0 (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀))
          / printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) := by
  intro h
  obtain ⟨a, t₀, hM, hq, hj, hs, hl, hR0⟩ := lcdm_facts h0 h1
  have hne : printedR (decel a t₀) (cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀) ≠ 0 := by
    rw [hq, hj, hs, hl]
    simp only [printedR]
    intro e
    apply hR
    linear_combination (-16 : ℝ) * e
  have e := h a _ t₀ hM hne
  have hH := hM.expanding
  rw [div_eq_div_iff (by positivity) hne] at e
  rw [hq, hj, hs, hl, hR0] at e
  simp only [printedR, P0, Q0] at e
  have k : hubble a t₀ ^ 2 * ((2 - Ω) * (909 * Ω ^ 2 - 1170 * Ω + 416)) = 0 := by
    linear_combination (-2 / 3 : ℝ) * e
  have : 0 < hubble a t₀ ^ 2 * ((2 - Ω) * (909 * Ω ^ 2 - 1170 * Ω + 416)) := by
    have := quad_pos Ω
    have : 0 < 2 - Ω := by linarith
    positivity
  linarith

/-- The printed relation (division form) fails in ΛCDM at the review's concordance value
`Ω = 1/4` (Sec. XI uses `Ω_M = 0.25` and `0.041`; both are covered by the `Ω ∈ (0,1)` statement
below whenever the printed `R` is nonzero there). -/
theorem printedF0Claim_false : ¬ PrintedF0Claim := by
  intro h
  exact printedF0_false_at (Ω := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (fun a F t₀ hM hne => h _ a F t₀ hM hne)

end Checked.Cosmography.FRCosmo
