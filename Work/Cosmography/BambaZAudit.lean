import Mathlib
import Work.Cosmography.BambaZ

/-! C9 audit. Blind restatement copied verbatim from `runs/2026-10-30T1232Z/blind/C9_blind.lean` (only the imports changed), followed by the comparison `C9Audit`. -/

/-!
# Blind restatement: Bamba–Capozziello–Nojiri–Odintsov (2012), Sec. X, Eqs. (10.38)–(10.51)

Source: K. Bamba, S. Capozziello, S. Nojiri, S. D. Odintsov, "Dark energy cosmology: the
equivalent description via different theoretical models and cosmography tests",
Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421v3, pp. 106–110.

Written from the source alone (independent reading; no repository cosmology definitions used).

## What the source claims
(10.38)  `d_L(z) = (c z / H₀) { D_L⁰ + D_L¹ z + D_L² z² + D_L³ z³ + D_L⁴ z⁴ + O(z⁵) }`
(10.45)  `d_A(z) = (c z / H₀) { D_A⁰ + D_A¹ z + D_A² z² + D_A³ z³ + D_A⁴ z⁴ + O(z⁵) }`
with the D-coefficients (10.39)–(10.44), (10.46)–(10.51) polynomials in `q₀, j₀, s₀, l₀` and
the curvature term `Kc²/(H₀²a₀²)`.

## Definitions (from the source)
* (10.1)–(10.5): `H = ȧ/a`, `q = -ä/(a H²)`, `j = a⃛/(a H³)`, `s = a⁽⁴⁾/(a H⁴)`,
  `l = a⁽⁵⁾/(a H⁵)`, all evaluated at the observation time `t₀`; `a₀ = a(t₀)`.
* `1 + z = a(t₀)/a(t)` (p. 107), emission time `t = t₀ - D/c`.
* (10.26) `d_L = (a(t₀)/a(t₀ - D/c)) · a(t₀) r₀`, (10.27) `d_A = (a(t₀ - D/c)/a(t₀)) · a(t₀) r₀`.
* (10.28) `r₀ = sin χ, χ, sinh χ` for `K = +1, 0, -1`, with `χ = ∫_{t₀-D/c}^{t₀} c dt / a(t)`.
  We encode this as `r₀ = S_K(χ)` with `S_K(χ) = sin(√K χ)/√K` (K>0), `χ` (K=0),
  `sinh(√(-K) χ)/√(-K)` (K<0), which coincides with (10.28) for `K ∈ {-1,0,1}`.

## Reading choices (most charitable faithful reading)
1. **Class of scale factors.** The source only uses the 5th-order Taylor expansion (10.10) of
   `a` with remainder `O((t-t₀)⁶)`. We assume `a` is `C⁶` near `t₀` (`ContDiffAt ℝ 6 a t₀`,
   which in Mathlib gives `C⁶` on a neighbourhood), `a(t₀) > 0`, `H₀ > 0` (needed for the
   parameters to be defined and for `z ↦ t` to be a local inverse with `z > 0` in the past),
   and `c > 0`. This is the weakest natural hypothesis giving an `O(z⁶)` remainder for `d_L`.
2. **Curvature.** The source writes `K = +1, 0, -1` in (10.28); we quantify over exactly
   these values. (The coefficients are polynomial in `k := Kc²/(H₀²a₀²)` and the derivation
   in `C9_blind_sympy.py` is valid for every real `K` with the general `S_K`.)
3. **Variable / filter.** `d_L(z)` is a function of `z` through the emission time. Instead of
   introducing the local inverse `t(z)`, we parametrise by the emission time `t` and use the
   filter `𝓝[≤] t₀` (past light cone, `D = c(t₀ - t) ≥ 0`, hence `z ≥ 0`). Since `z(t)` is a
   `C⁶` local diffeomorphism with `z'(t₀) = -H₀ ≠ 0`, `O(z⁶)` along `t → t₀⁻` is the same as
   `O(z⁶)` as `z → 0⁺` along the inverse. (The two-sided filter `𝓝 t₀` would also be true for
   the corrected coefficients, but the source only considers emission in the past.)
4. **Remainder order.** `(cz/H₀){… + O(z⁵)}` means `H₀ d_L/c − Σ_{n=0}^{4} Dⁿ z^{n+1} = O(z⁶)`.
5. **Typography.** In (10.44) and (10.51) the term printed `10 j²` (no subscript) is read as
   `10 j₀²` (the only cosmographic parameter it can mean; confirmed by the derivation).
   The `−` at the start of the second lines (10.44)/(10.51) follows a trailing `+` on the first
   line; we read `… − 15 q₀ s₀ + − 27 j₀ …` as `… − 15 q₀ s₀ − 27 j₀ …`.

## Verdict of the blind derivation (see `C9_blind_sympy.out`)
All of `D_L⁰…D_L³`, `D_A⁰…D_A³` are correct. Both `D_L⁴` and `D_A⁴` are missing the
second-order curvature term: `printed − correct = −k²/120`, `k = Kc²/(H₀²a₀²)`.
The cause is visible in (10.30): the sin/sinh series is truncated after the cubic term,
dropping `+K² χ⁵/5!`, which contributes at order `z⁵` of `d_L, d_A`, i.e. to `D⁴`.
Exact-model counterexample: Milne `a(t) = t`, `t₀ = 1`, `K = -1`, `c = 1`:
`H₀ d_L/c = z + z²/2` exactly, but the printed series gives `z + z²/2 − z⁵/120`.
Under the (non-faithful) reading "to first order in the curvature term" the printed
coefficients would be correct.
-/

open Real Filter Asymptotics Topology

namespace C9Blind

noncomputable section

/-! ### Cosmographic definitions (own, independent) -/

/-- Hubble parameter `H(t) = ȧ/a`. -/
def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- `H₀ = H(t₀)`. -/
def H0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := hubble a t0

/-- Deceleration `q₀ = -ä/(a H²)` at `t₀` (10.2). -/
def q0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := -(iteratedDeriv 2 a t0 / (a t0 * H0 a t0 ^ 2))

/-- Jerk `j₀ = a⃛/(a H³)` at `t₀` (10.3). -/
def j0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := iteratedDeriv 3 a t0 / (a t0 * H0 a t0 ^ 3)

/-- Snap `s₀ = a⁽⁴⁾/(a H⁴)` at `t₀` (10.4). -/
def s0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := iteratedDeriv 4 a t0 / (a t0 * H0 a t0 ^ 4)

/-- Lerk `l₀ = a⁽⁵⁾/(a H⁵)` at `t₀` (10.5). -/
def l0 (a : ℝ → ℝ) (t0 : ℝ) : ℝ := iteratedDeriv 5 a t0 / (a t0 * H0 a t0 ^ 5)

/-- Redshift of light emitted at time `t` and observed at `t₀`: `1 + z = a(t₀)/a(t)`. -/
def redshift (a : ℝ → ℝ) (t0 t : ℝ) : ℝ := a t0 / a t - 1

/-- Comoving coordinate distance `χ = ∫_t^{t₀} c dt'/a(t')` (argument of sin/sinh in (10.28)). -/
def comoving (a : ℝ → ℝ) (c t0 t : ℝ) : ℝ := ∫ s in t..t0, c / a s

/-- `S_K(χ)`: `sin(√K χ)/√K`, `χ`, `sinh(√(-K) χ)/√(-K)`; equals (10.28) for `K ∈ {1,0,-1}`. -/
def SK (K χ : ℝ) : ℝ :=
  if 0 < K then Real.sin (√K * χ) / √K
  else if K = 0 then χ
  else Real.sinh (√(-K) * χ) / √(-K)

/-- `r₀` of (10.28) as a function of the emission time `t = t₀ - D/c`. -/
def r0 (a : ℝ → ℝ) (c K t0 t : ℝ) : ℝ := SK K (comoving a c t0 t)

/-- Luminosity distance (10.26): `d_L = (a(t₀)/a(t)) · a(t₀) r₀`. -/
def dL (a : ℝ → ℝ) (c K t0 t : ℝ) : ℝ := a t0 / a t * (a t0 * r0 a c K t0 t)

/-- Angular-diameter distance (10.27): `d_A = (a(t)/a(t₀)) · a(t₀) r₀`. -/
def dA (a : ℝ → ℝ) (c K t0 t : ℝ) : ℝ := a t / a t0 * (a t0 * r0 a c K t0 t)

/-- The curvature term `k = K c² / (H₀² a₀²)` appearing in (10.41)–(10.51). -/
def curv (a : ℝ → ℝ) (c K t0 : ℝ) : ℝ := K * c ^ 2 / (H0 a t0 ^ 2 * a t0 ^ 2)

/-- Admissible data: `C⁶` scale factor near `t₀`, `a₀ > 0`, `H₀ > 0`, `c > 0`. -/
structure Admissible (a : ℝ → ℝ) (c t0 : ℝ) : Prop where
  smooth : ContDiffAt ℝ 6 a t0
  a_pos : 0 < a t0
  H_pos : 0 < H0 a t0
  c_pos : 0 < c

/-! ### Printed coefficients, transcribed verbatim (with `10 j² ↦ 10 j₀²`)
Arguments: `q = q₀, j = j₀, s = s₀, l = l₀, k = Kc²/(H₀²a₀²)`. -/

/-- (10.39)–(10.44): printed `D_Lⁿ`. -/
def DLprinted (q j s l k : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -(1 / 2) * (-1 + q)
  | 2 => -(1 / 6) * (1 - q - 3 * q ^ 2 + j + k)
  | 3 => (1 / 24) * (2 - 2 * q - 15 * q ^ 2 - 15 * q ^ 3 + 5 * j + 10 * q * j + s
          + 2 * k * (1 + 3 * q))
  | 4 => (1 / 120) * (-6 + 6 * q + 81 * q ^ 2 + 165 * q ^ 3 + 105 * q ^ 4 - 110 * q * j
          - 105 * q ^ 2 * j - 15 * q * s - 27 * j + 10 * j ^ 2 - 11 * s - l
          - 5 * k * (1 + 8 * q + 9 * q ^ 2 - 2 * j))
  | _ => 0

/-- (10.46)–(10.51): printed `D_Aⁿ`. -/
def DAprinted (q j s l k : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => -(1 / 2) * (3 + q)
  | 2 => (1 / 6) * (11 + 7 * q + 3 * q ^ 2 - j - k)
  | 3 => -(1 / 24) * (50 + 46 * q + 39 * q ^ 2 + 15 * q ^ 3 - 13 * j - 10 * q * j - s
          - 2 * k * (5 + 3 * q))
  | 4 => (1 / 120) * (274 + 326 * q + 411 * q ^ 2 + 315 * q ^ 3 + 105 * q ^ 4 - 210 * q * j
          - 105 * q ^ 2 * j - 15 * q * s - 137 * j + 10 * j ^ 2 - 21 * s - l
          - 5 * k * (17 + 20 * q + 9 * q ^ 2 - 2 * j))
  | _ => 0

/-! ### Independently derived coefficients (from `C9_blind_sympy.py`) -/

/-- Correct `D_Lⁿ` (derived): differs from print only in `n = 4` by `+k²/120`. -/
def DLcorrect (q j s l k : ℝ) : ℕ → ℝ
  | 4 => DLprinted q j s l k 4 + k ^ 2 / 120
  | n => DLprinted q j s l k n

/-- Correct `D_Aⁿ` (derived): differs from print only in `n = 4` by `+k²/120`. -/
def DAcorrect (q j s l k : ℝ) : ℕ → ℝ
  | 4 => DAprinted q j s l k 4 + k ^ 2 / 120
  | n => DAprinted q j s l k n

/-! ### The source's claims as Props -/

/-- Generic shape of (10.38)/(10.45): for every admissible `a` and `K ∈ {-1,0,1}`,
`H₀ d(t)/c − Σ_{n<5} Dⁿ z^{n+1} = O(z⁶)` as the emission time `t → t₀⁻`. -/
def SeriesClaim (dist : (ℝ → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (D : ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ (a : ℝ → ℝ) (c K t0 : ℝ), Admissible a c t0 → (K = -1 ∨ K = 0 ∨ K = 1) →
    (fun t => H0 a t0 * dist a c K t0 t / c
        - ∑ n ∈ Finset.range 5,
            D (q0 a t0) (j0 a t0) (s0 a t0) (l0 a t0) (curv a c K t0) n
              * redshift a t0 t ^ (n + 1))
      =O[𝓝[≤] t0] (fun t => redshift a t0 t ^ 6)

/-- **Source claim (10.38)–(10.44)** as printed. Blind verdict: FALSE (Milne `a = t`, `K = -1`). -/
def ClaimDL_printed : Prop := SeriesClaim dL DLprinted

/-- **Source claim (10.45)–(10.51)** as printed. Blind verdict: FALSE (same counterexample). -/
def ClaimDA_printed : Prop := SeriesClaim dA DAprinted

/-- **Corrected claim** for `d_L` (`D_L⁴` gains `+k²/120`). Stated only; not proved here. -/
def ClaimDL_corrected : Prop := SeriesClaim dL DLcorrect

/-- **Corrected claim** for `d_A` (`D_A⁴` gains `+k²/120`). Stated only; not proved here. -/
def ClaimDA_corrected : Prop := SeriesClaim dA DAcorrect

/-! ### Machine-checked algebra: printed − correct -/

theorem DL_diff (q j s l k : ℝ) :
    (DLprinted q j s l k 0 - DLcorrect q j s l k 0 = 0) ∧
    (DLprinted q j s l k 1 - DLcorrect q j s l k 1 = 0) ∧
    (DLprinted q j s l k 2 - DLcorrect q j s l k 2 = 0) ∧
    (DLprinted q j s l k 3 - DLcorrect q j s l k 3 = 0) ∧
    (DLprinted q j s l k 4 - DLcorrect q j s l k 4 = -k ^ 2 / 120) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [DLcorrect] <;> ring

theorem DA_diff (q j s l k : ℝ) :
    (DAprinted q j s l k 0 - DAcorrect q j s l k 0 = 0) ∧
    (DAprinted q j s l k 1 - DAcorrect q j s l k 1 = 0) ∧
    (DAprinted q j s l k 2 - DAcorrect q j s l k 2 = 0) ∧
    (DAprinted q j s l k 3 - DAcorrect q j s l k 3 = 0) ∧
    (DAprinted q j s l k 4 - DAcorrect q j s l k 4 = -k ^ 2 / 120) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [DAcorrect] <;> ring

/-- The fully expanded corrected `D_L⁴` (×120), as output by the sympy derivation. -/
theorem DLcorrect4_expanded (q j s l k : ℝ) :
    120 * DLcorrect q j s l k 4 =
      10 * j ^ 2 - 105 * j * q ^ 2 - 110 * j * q - 27 * j + k ^ 2
        + k * (10 * j - 45 * q ^ 2 - 40 * q - 5) - l + 105 * q ^ 4 + 165 * q ^ 3
        + 81 * q ^ 2 - 15 * q * s + 6 * q - 11 * s - 6 := by
  simp only [DLcorrect, DLprinted]; ring

/-- The fully expanded corrected `D_A⁴` (×120), as output by the sympy derivation. -/
theorem DAcorrect4_expanded (q j s l k : ℝ) :
    120 * DAcorrect q j s l k 4 =
      10 * j ^ 2 - 105 * j * q ^ 2 - 210 * j * q - 137 * j + k ^ 2
        + k * (10 * j - 45 * q ^ 2 - 100 * q - 85) - l + 105 * q ^ 4 + 315 * q ^ 3
        + 411 * q ^ 2 - 15 * q * s + 326 * q - 21 * s + 274 := by
  simp only [DAcorrect, DAprinted]; ring

/-- Milne check at the coefficient level (`q₀=j₀=s₀=l₀=0`, `k=-1`): the printed series is
`z + z²/2 − z⁵/120`, while the exact `H₀ d_L/c = z + z²/2`; the corrected series matches. -/
theorem milne_printed (z : ℝ) :
    ∑ n ∈ Finset.range 5, DLprinted 0 0 0 0 (-1) n * z ^ (n + 1) = z + z ^ 2 / 2 - z ^ 5 / 120 := by
  simp [Finset.sum_range_succ, DLprinted]; ring

theorem milne_corrected (z : ℝ) :
    ∑ n ∈ Finset.range 5, DLcorrect 0 0 0 0 (-1) n * z ^ (n + 1) = z + z ^ 2 / 2 := by
  simp [Finset.sum_range_succ, DLcorrect, DLprinted]; ring

end

end C9Blind

namespace C9Audit

open Filter Topology Asymptotics Checked.Cosmography Checked.Cosmography.Aviles
open Checked.Cosmography.BambaY Checked.Cosmography.BambaK Checked.Cosmography.BambaA
open Checked.Cosmography.Transverse Work.Cosmography.BambaZ

/-- Same transcription of the printed coefficients. -/
theorem printed_eq (q j s l k : ℝ) :
    C9Blind.DLprinted q j s l k 1 = DL1z q ∧ C9Blind.DLprinted q j s l k 2 = DL2z q j k ∧
    C9Blind.DLprinted q j s l k 3 = DL3z q j s k ∧ C9Blind.DLprinted q j s l k 4 = printedDL4z q j s l k ∧
    C9Blind.DAprinted q j s l k 1 = DA1z q ∧ C9Blind.DAprinted q j s l k 2 = DA2z q j k ∧
    C9Blind.DAprinted q j s l k 3 = DA3z q j s k ∧ C9Blind.DAprinted q j s l k 4 = printedDA4z q j s l k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [C9Blind.DLprinted, C9Blind.DAprinted, DL1z, DL2z, DL3z, printedDL4z, DA1z, DA2z, DA3z,
      printedDA4z] <;> ring

/-- The blind's independently derived `D⁴` are our corrected ones (certified by our headlines). -/
theorem derived_eq (q j s l k : ℝ) :
    C9Blind.DLcorrect q j s l k 4 = correctDL4z q j s l k ∧
      C9Blind.DAcorrect q j s l k 4 = correctDA4z q j s l k := by
  constructor <;> simp only [C9Blind.DLcorrect, C9Blind.DAcorrect, correctDL4z, correctDA4z,
    (printed_eq q j s l k).2.2.2.1, (printed_eq q j s l k).2.2.2.2.2.2.2]

theorem SK_eq : C9Blind.SK = transverse := by
  funext K χ
  rcases lt_trichotomy K 0 with h | h | h
  · simp [C9Blind.SK, transverse, h, h.ne, not_lt.2 h.le]
  · simp [C9Blind.SK, transverse, h]
  · simp [C9Blind.SK, transverse, h]

lemma H0_eq (a : ℝ → ℝ) (t : ℝ) : C9Blind.H0 a t = hubble a t := rfl

lemma q0_eq (a : ℝ → ℝ) (t : ℝ) (ha : a t ≠ 0) : C9Blind.q0 a t = decel a t := by
  simp only [C9Blind.q0, C9Blind.H0, C9Blind.hubble, Checked.Cosmography.decel, iteratedDeriv_succ,
    iteratedDeriv_zero]
  by_cases hd : deriv a t = 0
  · simp [hd]
  · field_simp

lemma j0_eq (a : ℝ → ℝ) (t : ℝ) : C9Blind.j0 a t = cosmoCoeff 3 a t := rfl
lemma s0_eq (a : ℝ → ℝ) (t : ℝ) : C9Blind.s0 a t = cosmoCoeff 4 a t := rfl
lemma l0_eq (a : ℝ → ℝ) (t : ℝ) : C9Blind.l0 a t = cosmoCoeff 5 a t := rfl
lemma z_eq (a : ℝ → ℝ) (t₀ t : ℝ) : C9Blind.redshift a t₀ t = redshift a t₀ t := rfl

lemma curv_eq (a : ℝ → ℝ) (K t₀ : ℝ) : C9Blind.curv a 1 K t₀ = curvK K a t₀ := by
  simp [C9Blind.curv, curvK, C9Blind.H0, C9Blind.hubble, hubble]

lemma dL_eq (a : ℝ → ℝ) (K t₀ t : ℝ) :
    C9Blind.H0 a t₀ * C9Blind.dL a 1 K t₀ t / 1 = hubble a t₀ * lumDist K a t₀ t := by
  simp only [C9Blind.dL, C9Blind.r0, C9Blind.comoving, SK_eq, lumDist, comoving, redshift, H0_eq]
  ring

lemma dA_eq (a : ℝ → ℝ) (K t₀ t : ℝ) (ha0 : a t₀ ≠ 0) (ht : a t ≠ 0) :
    C9Blind.H0 a t₀ * C9Blind.dA a 1 K t₀ t / 1 = hubble a t₀ * angDist K a t₀ t := by
  simp only [C9Blind.dA, C9Blind.r0, C9Blind.comoving, SK_eq, angDist, lumDist, comoving, redshift,
    H0_eq, add_sub_cancel]
  field_simp

/-- The blind's residual for (10.38) equals ours (`c = 1`). -/
lemma remL_eq (a : ℝ → ℝ) (K t₀ t : ℝ) (ha0 : a t₀ ≠ 0) :
    C9Blind.H0 a t₀ * C9Blind.dL a 1 K t₀ t / 1 - ∑ n ∈ Finset.range 5,
        C9Blind.DLprinted (C9Blind.q0 a t₀) (C9Blind.j0 a t₀) (C9Blind.s0 a t₀) (C9Blind.l0 a t₀)
          (C9Blind.curv a 1 K t₀) n * C9Blind.redshift a t₀ t ^ (n + 1)
      = remLz printedDL4z K a t₀ t := by
  rw [dL_eq, q0_eq a t₀ ha0, curv_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, remLz, seriesZ, C9Blind.DLprinted,
    DL1z, DL2z, DL3z, printedDL4z, j0_eq, s0_eq, l0_eq, z_eq]
  ring

lemma remA_eq (a : ℝ → ℝ) (K t₀ t : ℝ) (ha0 : a t₀ ≠ 0) (ht : a t ≠ 0) :
    C9Blind.H0 a t₀ * C9Blind.dA a 1 K t₀ t / 1 - ∑ n ∈ Finset.range 5,
        C9Blind.DAprinted (C9Blind.q0 a t₀) (C9Blind.j0 a t₀) (C9Blind.s0 a t₀) (C9Blind.l0 a t₀)
          (C9Blind.curv a 1 K t₀) n * C9Blind.redshift a t₀ t ^ (n + 1)
      = remAz printedDA4z K a t₀ t := by
  rw [dA_eq a K t₀ t ha0 ht, q0_eq a t₀ ha0, curv_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, remAz, seriesZ, C9Blind.DAprinted,
    DA1z, DA2z, DA3z, printedDA4z, j0_eq, s0_eq, l0_eq, z_eq]
  ring

lemma adm_exp : C9Blind.Admissible Real.exp 1 0 :=
  ⟨Real.contDiff_exp.contDiffAt, Real.exp_pos 0, by rw [H0_eq, closedExp_vals.1]; norm_num, one_pos⟩

/-- `O(z⁶)` from the past (closed) implies `o(z⁵)` from the past (open), for `a = exp`, `t₀ = 0`. -/
lemma upgrade {f : ℝ → ℝ}
    (h : f =O[𝓝[≤] 0] fun t => C9Blind.redshift Real.exp 0 t ^ 6) :
    f =o[𝓝[<] 0] fun t => redshift Real.exp 0 t ^ 5 := by
  have hz : Tendsto (fun t => redshift Real.exp 0 t) (𝓝[<] 0) (𝓝 0) :=
    (redshift_tendsto Real.exp 0 Real.differentiable_exp.differentiableAt
      (Real.exp_pos 0).ne').mono_left nhdsWithin_le_nhds
  have h6 : (fun t => redshift Real.exp 0 t ^ 6) =o[𝓝[<] 0] fun t => redshift Real.exp 0 t ^ 5 := by
    simpa using pow_succ_mul_isLittleO hz 5 (fun _ => (1 : ℝ)) (isBigO_refl _ _)
  exact (h.mono (nhdsWithin_mono 0 Set.Iio_subset_Iic_self)).trans_isLittleO h6

/-- Our refutation refutes the blind's reading of (10.38)–(10.44) (`a = eᵗ`, `K = 1`, `c = 1`). -/
theorem blindDL_false_via_ours : ¬ C9Blind.ClaimDL_printed := by
  intro h
  have hb := upgrade (h Real.exp 1 1 0 adm_exp (Or.inr (Or.inr rfl)))
  refine printedDL4z_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [closedExp_vals.1]; norm_num) one_ne_zero ?_
  exact hb.congr' (Eventually.of_forall fun t => remL_eq Real.exp 1 0 t (Real.exp_pos 0).ne')
    EventuallyEq.rfl

/-- Same for (10.45)–(10.51). -/
theorem blindDA_false_via_ours : ¬ C9Blind.ClaimDA_printed := by
  intro h
  have hb := upgrade (h Real.exp 1 1 0 adm_exp (Or.inr (Or.inr rfl)))
  refine printedDA4z_fails_past 1 Real.exp 0 Real.contDiff_exp.contDiffAt (Real.exp_pos 0).ne'
    (by rw [closedExp_vals.1]; norm_num) one_ne_zero ?_
  exact hb.congr' (Eventually.of_forall fun t =>
    remA_eq Real.exp 1 0 t (Real.exp_pos 0).ne' (Real.exp_pos t).ne') EventuallyEq.rfl

end C9Audit
