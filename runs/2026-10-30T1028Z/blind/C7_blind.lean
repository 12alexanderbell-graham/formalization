import Mathlib

/-!
# C7 (blind restatement): Bamba–Capozziello–Nojiri–Odintsov (2012), arXiv:1205.3421v3, Sec. X,
Eqs. (10.61)–(10.63): angular-diameter distance coefficients `D³_{A,y}`, `D⁴_{A,y}` in the
y-redshift `y = z/(1+z)`, "derived for any value of the curvature parameter".

Own definitions, written from the source text only.
* (10.1)–(10.5): `H = ȧ/a`, `q = −(ä/a)/H²`, `j = (a⃛/a)/H³`, `s = (a⁗/a)/H⁴`, `l = (a⁽⁵⁾/a)/H⁵`.
* `1 + z = a(t₀)/a(t)`, `y = z/(1+z)`.
* (10.27)–(10.28): `d_A = [a(t)/a(t₀)] · a(t₀) · S_K(∫_t^{t₀} c dt'/a)`, `S_K = sin, id, sinh` for
  `K = +1, 0, −1`; emission time `t = t₀ − D/c`.
* p. 110: `Ω₀ = 1 + K c²/(H₀² a₀²)`.
* Series (not printed for `y`; by analogy with the review's z-series):
  `d_A = (c y/H₀)[D⁰ + D¹ y + D² y² + D³ y³ + D⁴ y⁴ + O(y⁵)]`.

Reading choices (most charitable to the source):
* scale factor: real-analytic (`ContDiff ℝ ω`), positive for all `t`, `H₀ > 0` (strongest
  hypotheses = weakest claim);
* `c > 0` arbitrary, `K ∈ {−1, 0, 1}` arbitrary ("any value of the curvature parameter");
* limit: emission time `t → t₀` from the past (`𝓝[<] t₀`), weaker than two-sided;
* error: little-o of the next power (`o(y⁴)` for the claim ending at `D³`, `o(y⁵)` for the one
  ending at `D⁴`), weaker than the `O(y⁵)` / `O(y⁶)` the analogy suggests;
* lower-order coefficients: (10.61) uses the printed `D⁰, D¹, D²` (they are correct for all `K`).
  For (10.62)–(10.63) the printed `D³` is itself wrong when `K ≠ 0`, so to isolate `D⁴` the
  claim `BambaDAy4Claim` uses the *correct* `D³` (`correctD3`); `BambaDAy4ClaimAllPrinted` uses
  all printed coefficients.
* (10.62)–(10.63) is read as one bracket across the equation-number break, `10j²` = `10 j₀²`.
-/

namespace C7Blind

open Filter Asymptotics Topology
open scoped ContDiff

/-- Hubble rate `H = ȧ/a`. -/
noncomputable def hub (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- `(a⁽ⁿ⁾/a)/Hⁿ`. -/
noncomputable def cosmo (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  (iteratedDeriv n a t / a t) / hub a t ^ n

noncomputable def qP (a : ℝ → ℝ) (t : ℝ) : ℝ := -cosmo 2 a t
noncomputable def jP (a : ℝ → ℝ) (t : ℝ) : ℝ := cosmo 3 a t
noncomputable def sP (a : ℝ → ℝ) (t : ℝ) : ℝ := cosmo 4 a t
noncomputable def lP (a : ℝ → ℝ) (t : ℝ) : ℝ := cosmo 5 a t

/-- Redshift `z = a(t₀)/a(t) − 1` of light emitted at `t`, received at `t₀`. -/
noncomputable def zRed (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1

/-- y-redshift `y = z/(1+z)`. -/
noncomputable def yRed (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := zRed a t₀ t / (1 + zRed a t₀ t)

/-- `∫_t^{t₀} c dt'/a(t')`. -/
noncomputable def chi (c : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ u in t..t₀, c / a u

/-- `S_K`: `sin` for `K = 1`, `sinh` for `K = −1`, identity otherwise (`K = 0`). -/
noncomputable def SK (K : ℤ) (x : ℝ) : ℝ :=
  if K = 1 then Real.sin x else if K = -1 then Real.sinh x else x

/-- (10.27): `d_A = [a(t)/a(t₀)] · a(t₀) · r₀`, `r₀ = S_K(∫_t^{t₀} c dt/a)`. -/
noncomputable def dA (c : ℝ) (K : ℤ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  (a t / a t₀) * (a t₀ * SK K (chi c a t₀ t))

/-- `Ω₀ = 1 + K c²/(H₀² a₀²)` (p. 110). -/
noncomputable def Omega0 (c : ℝ) (K : ℤ) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ :=
  1 + (K : ℝ) * c ^ 2 / (hub a t₀ ^ 2 * a t₀ ^ 2)

/-! ### Printed coefficients (verbatim) -/

noncomputable def D0 : ℝ := 1
noncomputable def D1 (q : ℝ) : ℝ := -(1 / 2) * (1 + q)
noncomputable def D2 (q j Ω : ℝ) : ℝ := -(1 / 6) * (-q - 3 * q ^ 2 + j + Ω)
/-- (10.61) as printed. -/
noncomputable def printedD3 (q j s Ω : ℝ) : ℝ :=
  -(1 / 24) * (-2 * q + 3 * q ^ 2 + 15 * q ^ 3 - j - 10 * q * j - s + 2 * Ω)
/-- (10.62)–(10.63) as printed. -/
noncomputable def printedD4 (q j s l Ω : ℝ) : ℝ :=
  -(1 / 120) * (1 - 6 * q + 9 * q ^ 2 - 15 * q ^ 3 - 105 * q ^ 4 + 10 * q * j + 105 * q ^ 2 * j
    + 15 * q * s - 3 * j - 10 * j ^ 2 + s + l + 5 * Ω)

/-! ### Correct coefficients (derived in `C7_blind_sympy.py`) -/

noncomputable def correctD3 (q j s Ω : ℝ) : ℝ :=
  -(1 / 24) * (4 * q + 3 * q ^ 2 + 15 * q ^ 3 - j - 10 * q * j - s + 2 * Ω - 6 * Ω * q)
noncomputable def correctD4 (q j s l Ω : ℝ) : ℝ :=
  -(1 / 120) * (14 * q - 36 * q ^ 2 - 15 * q ^ 3 - 105 * q ^ 4 + 10 * q * j + 105 * q ^ 2 * j
    + 15 * q * s + 7 * j - 10 * j ^ 2 + s + l + 7 * Ω - 20 * Ω * q + 45 * Ω * q ^ 2
    - 10 * Ω * j - Ω ^ 2)

/-! ### Claims -/

/-- Standing hypotheses: analytic, everywhere-positive scale factor, `H₀ > 0`, `c > 0`,
`K ∈ {−1, 0, 1}`. -/
def Admissible (c : ℝ) (K : ℤ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < c ∧ (K = -1 ∨ K = 0 ∨ K = 1) ∧ ContDiff ℝ ω a ∧ (∀ t, 0 < a t) ∧ 0 < hub a t₀

/-- `H₀ d_A/c − y[D⁰ + D¹y + D²y² + d₃ y³]`, with all `D`'s evaluated at `t₀`. -/
noncomputable def rem3 (D3 : ℝ → ℝ → ℝ → ℝ → ℝ) (c : ℝ) (K : ℤ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  let q := qP a t₀; let j := jP a t₀; let s := sP a t₀; let Ω := Omega0 c K a t₀
  let y := yRed a t₀ t
  hub a t₀ * dA c K a t₀ t / c - y * (D0 + D1 q * y + D2 q j Ω * y ^ 2 + D3 q j s Ω * y ^ 3)

/-- `H₀ d_A/c − y[D⁰ + D¹y + D²y² + d₃ y³ + d₄ y⁴]`. -/
noncomputable def rem4 (D3 : ℝ → ℝ → ℝ → ℝ → ℝ) (D4 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (c : ℝ) (K : ℤ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  let q := qP a t₀; let j := jP a t₀; let s := sP a t₀; let l := lP a t₀
  let Ω := Omega0 c K a t₀
  let y := yRed a t₀ t
  hub a t₀ * dA c K a t₀ t / c -
    y * (D0 + D1 q * y + D2 q j Ω * y ^ 2 + D3 q j s Ω * y ^ 3 + D4 q j s l Ω * y ^ 4)

/-- Claim (10.61): with printed `D⁰…D³`, `H₀ d_A/c = y[D⁰ + … + D³y³] + o(y⁴)` as `t → t₀⁻`,
for every curvature `K`. -/
def BambaDAy3Claim : Prop :=
  ∀ (c : ℝ) (K : ℤ) (a : ℝ → ℝ) (t₀ : ℝ), Admissible c K a t₀ →
    (fun t => rem3 printedD3 c K a t₀ t) =o[𝓝[<] t₀] (fun t => yRed a t₀ t ^ 4)

/-- Claim (10.62)–(10.63), isolated: lower coefficients correct (printed `D⁰…D²`, correct `D³`),
printed `D⁴`; `H₀ d_A/c = y[…] + o(y⁵)` as `t → t₀⁻`, every `K`. -/
def BambaDAy4Claim : Prop :=
  ∀ (c : ℝ) (K : ℤ) (a : ℝ → ℝ) (t₀ : ℝ), Admissible c K a t₀ →
    (fun t => rem4 correctD3 printedD4 c K a t₀ t) =o[𝓝[<] t₀] (fun t => yRed a t₀ t ^ 5)

/-- Variant: all printed coefficients `D⁰…D⁴` in the series. -/
def BambaDAy4ClaimAllPrinted : Prop :=
  ∀ (c : ℝ) (K : ℤ) (a : ℝ → ℝ) (t₀ : ℝ), Admissible c K a t₀ →
    (fun t => rem4 printedD3 printedD4 c K a t₀ t) =o[𝓝[<] t₀] (fun t => yRed a t₀ t ^ 5)

/-! ### Algebraic facts (printed − correct) -/

lemma D3_diff (q j s Ω : ℝ) : printedD3 q j s Ω - correctD3 q j s Ω = -q * (Ω - 1) / 4 := by
  unfold printedD3 correctD3; ring

lemma D4_diff (q j s l Ω : ℝ) : printedD4 q j s l Ω - correctD4 q j s l Ω =
    (Ω - 1) * (1 - 20 * q + 45 * q ^ 2 - 10 * j - Ω) / 120 := by
  unfold printedD4 correctD4; ring

/-- Flat case (`Ω₀ = 1`): printed = correct. -/
lemma flat_agree (q j s l : ℝ) :
    printedD3 q j s 1 = correctD3 q j s 1 ∧ printedD4 q j s l 1 = correctD4 q j s l 1 := by
  constructor
  · unfold printedD3 correctD3; ring
  · unfold printedD4 correctD4; ring

/-- Milne (`a = ct`, `K = −1`: `q = j = s = l = 0`, `Ω₀ = 0`; exact `H₀d_A/c = y − y²/2`):
printed `D⁴ = −1/120`, correct `0`. -/
lemma milne_D4 : printedD4 0 0 0 0 0 = -1 / 120 ∧ correctD4 0 0 0 0 0 = 0 := by
  unfold printedD4 correctD4; norm_num

end C7Blind
