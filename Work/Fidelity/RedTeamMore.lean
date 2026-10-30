import Checked.Cosmography.BambaAngular
import Checked.Cosmography.LCDMCoefficients

/-!
# Red-team mutants (deliberately WRONG definitions)

Plausible but incorrect variants of `hubble`, `decel`, `BambaA.angDist` and `Aviles.IsFlatLCDM`,
used to measure whether the fidelity test suite catches wrong definitions. Every definition here
differs from the true one for some admissible input (`a > 0`, smooth near the times involved);
each docstring names the error and gives one distinguishing input. Definitions only.
-/

namespace Work.Fidelity.RedTeamMore

open Filter Topology Checked.Cosmography Checked.Cosmography.BambaK
open Checked.Cosmography.BambaY Checked.Cosmography.Transverse

/-! ## Hubble rate (truth: `ȧ/a`) -/

/-- Error: `H = (a²)˙/(2a)` — forgot the square in the denominator (`(a²)˙/(2a²)` is right), so it
is `ȧ`; agrees whenever `a t = 1`. Input: `a = 2eᵗ`, `t = 0`: truth `1`, mutant `2`. -/
noncomputable def rh1 (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv (fun s => a s ^ 2) t / (2 * a t)

/-- Error: Hubble time vs rate confusion, `1/(d ln a/dt)`; agrees whenever `H = ±1` (e.g. `a = eᵗ`).
Input: `a = e^{2t}`, `t = 0`: truth `2`, mutant `1/2`. -/
noncomputable def rh2 (a : ℝ → ℝ) (t : ℝ) : ℝ := 1 / deriv (fun s => Real.log (a s)) t

/-- Error: conformal-Hubble formula `a'/a²` applied with the cosmic-time derivative; agrees when
`a t = 1`. Input: `a = 2eᵗ`, `t = 0`: truth `1`, mutant `1/2`. -/
noncomputable def rh3 (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t ^ 2

/-- Error: `H = √(ȧ²)/a = |ȧ|/a` (taken from `H² = (ȧ/a)²`); agrees for every expanding model.
Input: contracting `a = e^{-t}`, `t = 0`: truth `-1`, mutant `1`. -/
noncomputable def rh4 (a : ℝ → ℝ) (t : ℝ) : ℝ := Real.sqrt (deriv a t ^ 2) / a t

/-- Error: de Sitter identity `H² = ä/a` used in general (sqrt junk `0` when decelerating); exact for
every `a = C e^{Ht}`, `H > 0`. Input: `a = t²`, `t = 1`: truth `2`, mutant `√2`. -/
noncomputable def rh5 (a : ℝ → ℝ) (t : ℝ) : ℝ := Real.sqrt (deriv (deriv a) t / a t)

/-! ## Deceleration parameter (truth: `-ä a/ȧ²`) -/

/-- Error: `q = -ä/(a H²)` with `H²` mistaken for `ȧ²`, i.e. `-ä/(a ȧ²)`; agrees when `a t = 1`.
Input: `a = 2eᵗ`, `t = 0`: truth `-1`, mutant `-1/4`. -/
noncomputable def rq1 (a : ℝ → ℝ) (t : ℝ) : ℝ := -deriv (deriv a) t / (a t * deriv a t ^ 2)

/-- Error: sign slip in `q = -1 - Ḣ/H²` (written `-1 + Ḣ/H²`); agrees in de Sitter (`Ḣ = 0`).
Input: `a = t²`, `t = 1`: truth `-1/2`, mutant `-3/2`. -/
noncomputable def rq2 (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -1 + deriv (fun s => deriv a s / a s) t / (deriv a t / a t) ^ 2

/-- Error: missing square, `q = -1 - Ḣ/H`; agrees in de Sitter and whenever `H(t) = 1`
(e.g. `a = t²` at `t = 2`). Input: `a = t²`, `t = 1`: truth `-1/2`, mutant `0`. -/
noncomputable def rq3 (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -1 - deriv (fun s => deriv a s / a s) t / (deriv a t / a t)

/-- Error: the textbook identity `q = -1 - Ḣ/H²`, equal to the truth whenever `ȧ(t) ≠ 0`, but with a
different junk value at a turnaround (`ȧ = 0`): truth `0` (`x/0 = 0`), mutant `-1`.
Input: `a = 2 + cos t`, `t = 0`: truth `0`, mutant `-1`. -/
noncomputable def rq4 (a : ℝ → ℝ) (t : ℝ) : ℝ := -1 - deriv (hubble a) t / hubble a t ^ 2

/-- Error: `ȧ` instead of `ȧ²` in the denominator; agrees whenever `ȧ(t) = 1` (e.g. `a = eᵗ` at
`t = 0`) or `ä = 0`. Input: `a = e^{2t}`, `t = 0`: truth `-1`, mutant `-2`. -/
noncomputable def rq5 (a : ℝ → ℝ) (t : ℝ) : ℝ := -(deriv (deriv a) t * a t) / deriv a t

/-! ## Angular-diameter distance (truth: `d_L/(1+z)² = a(t) S_K(χ)`) -/

/-- Error: one power of `(1+z)` instead of two (gives the transverse comoving distance `a₀ S_K(χ)`);
agrees at `z = 0` (e.g. static `a`). Input: `K = 0`, `a = eᵗ`, `t₀ = 0`, `t = -1`:
truth `1 - 1/e ≈ 0.632`, mutant `e - 1 ≈ 1.718`. -/
noncomputable def ra1 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDist K a t₀ t / (1 + redshift a t₀ t)

/-- Error: `d_A = S_K(χ)/(1+z)` with the `a₀ = 1` normalization silently assumed (dropped `a₀`).
Input: `K = 0`, `a = 2eᵗ`, `t₀ = 0`, `t = -1`: truth `(e-1)/e ≈ 0.632`,
mutant `(e-1)/(2e) ≈ 0.316`. -/
noncomputable def ra2 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  transverse K (comoving a t₀ t) / (1 + redshift a t₀ t)

/-- Error: curvature sign convention flipped (`K > 0` treated as open, `sinh`); agrees for `K = 0`.
Input: `K = 1`, `a ≡ 1`, `t₀ = 0`, `t = -1`: truth `sin 1 ≈ 0.841`, mutant `sinh 1 ≈ 1.175`. -/
noncomputable def ra3 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  lumDist (-K) a t₀ t / (1 + redshift a t₀ t) ^ 2

/-- Error: curvature normalization mixed up (`S` evaluated with `K a₀²` in place of `K`); agrees for
`K = 0` and whenever `a t₀ = 1`. Input: `K = 1`, `a ≡ 2`, `t₀ = 0`, `t = -1` (`χ = 1/2`):
truth `2 sin(1/2) ≈ 0.959`, mutant `sin 1 ≈ 0.841`. -/
noncomputable def ra4 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t * transverse (K * a t₀ ^ 2) (comoving a t₀ t)

/-- Error: distance forced nonnegative via `|χ|` ("distances are positive"); agrees for all past
times `t ≤ t₀`. Input: `K = 0`, `a ≡ 1`, `t₀ = 0`, `t = 1` (`χ = -1`): truth `-1`, mutant `1`. -/
noncomputable def ra5 (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  a t * transverse K |comoving a t₀ t|

/-! ## Flat ΛCDM predicate -/

/-- Error: dropped `0 < H₀`. Model: static `a ≡ 1`, any `Ω`, `t₀ = 0` (`H ≡ 0`, `0 = 0·√…`):
truth false, mutant true. (Also contracting `a = e^{-t}`, `Ω = 0`.) -/
def rL1 (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
    hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)

/-- Error: `∃ᶠ` (frequently) instead of `∀ᶠ` (eventually). Model: `Ω = 0`, `t₀ = 0`,
`a = exp ∫₀ᵗ H` with smooth `H(t) = 1 + exp(-1/t²) sin(1/t)` (`H(0) = 1`): the equation `H = H₀`
holds on the zeros of `sin(1/t)` accumulating at `0` but on no neighbourhood: truth false,
mutant true. -/
def rL2 (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < hubble a t₀ ∧ ∃ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
    hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)

/-- Error: only the past side `𝓝[<] t₀` (observations only see `t < t₀`). Model: `Ω = 0`,
`t₀ = 0`, `a = exp(t + g t)` with smooth `g t = exp(-1/t)` for `t > 0`, `0` otherwise: `H = 1` for
`t ≤ 0`, `H = 1 + g' ≠ 1` for `t > 0`: truth false, mutant true. -/
def rL3 (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝[<] t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
    hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)

/-- Error: precedence slip `Ω(1 + z³)` for `Ω(1+z)³`; agrees for `Ω = 0` (de Sitter).
Model: Einstein–de Sitter `Ω = 1`, `a = t^{2/3}`, `t₀ = 1` (`H = H₀(1+z)^{3/2}`): truth true,
mutant false (`1/t² ≠ 1 + z³` near `1`: derivatives `-2` vs `0`). -/
def rL4 (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
    hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t ^ 3) + 1 - Ω)

/-- Error: `H₀` attached only to the matter term (`H = √(H₀² Ω (1+z)³ + 1 - Ω)`, i.e. `H₀ = 1` units
leaking in); agrees whenever `H₀ = 1` (e.g. `a = eᵗ`, or EdS at `t₀ = 2/3`).
Model: `Ω = 0`, `a = e^{2t}`, `t₀ = 0`: truth true (`H ≡ 2 = H₀`), mutant false (`2 ≠ 1`). -/
def rL5 (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
    hubble a t = √(hubble a t₀ ^ 2 * Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)

end Work.Fidelity.RedTeamMore
