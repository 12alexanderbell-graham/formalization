import Mathlib

/-!
# C6 (blind restatement): Bamba–Capozziello–Nojiri–Odintsov, Astrophys. Space Sci. 342, 155 (2012),
arXiv:1205.3421v3, Sec. X, Eqs. (10.55) and (10.56)–(10.57): the y-series coefficients
`D³_{L,y}` and `D⁴_{L,y}` of the luminosity distance, "for any value of the curvature parameter".

Source conventions used verbatim:
* (10.1)–(10.5) `H = ȧ/a`, `q = −(ä/a)/H²`, `j = (a⃛/a)/H³`, `s = (a⁗/a)/H⁴`, `l = (a⁽⁵⁾/a)/H⁵`,
  subscript 0 = value at `t₀`; `1 + z = a(t₀)/a(t)`.
* (10.26), (10.28) `d_L = [a(t₀)/a(t₀ − D/c)] · a(t₀) · r₀`, `r₀ = S_K(∫_{t₀−D/c}^{t₀} c dt/a)`,
  `S_{+1} = sin`, `S_0 = id`, `S_{−1} = sinh`. We parametrise by the emission time
  `t = t₀ − D/c` (so `D = c (t₀ − t)`).
* p. 110: `Ω₀ = 1 + K c²/(H₀² a₀²)`.
* `y = z/(1+z)` and (by analogy with (10.38))
  `d_L(y) = (c y/H₀)[D⁰_{L,y} + D¹_{L,y} y + D²_{L,y} y² + D³_{L,y} y³ + D⁴_{L,y} y⁴ + O(y⁵)]`.

## Reading choices (each chosen to be the most charitable to the source)

* **Scale-factor class.** Real-analytic `a` (`ContDiff ℝ ω a`), the strongest standard regularity
  hypothesis (fewer models ⇒ weaker universal claim). Only `a(t₀) > 0` and `H₀ > 0` are assumed:
  the claim is an asymptotic statement about the germ of `a` at `t₀`, and by continuity `a > 0` on
  a neighbourhood of `t₀`, which is all `d_L(t)` for `t` near `t₀` uses. (We do not demand
  `a > 0` on all of `ℝ`: e.g. Milne `a = ct` is a bona fide FLRW model on `t > 0`.) `H₀ > 0`
  (expanding universe) is needed for `q₀, j₀, …` to be defined and for `y` to be a local
  coordinate.
* **Curvature.** The source says the relations hold "for any value of the curvature parameter",
  so we quantify `∀ K ∈ {+1, 0, −1}` (the inductive `Curv`), with `Ω₀` defined from `K` as printed.
  `c > 0` is quantified too (any unit system); a counterexample with `c = 1` is unit-independent.
* **Filter.** Past emission only, `t → t₀⁻` (`𝓝[<] t₀`), i.e. `y → 0⁺`: physically the only
  meaningful side, and a weaker claim than the two-sided one.
* **Error size.** Little-o: for (10.55) the remainder is `o(y⁴)`, for (10.56)–(10.57) it is
  `o(y⁵)`. This is weaker than the source's Big-O (`O(y⁵)` resp. `O(y⁶)` after truncation) yet
  still pins down exactly the coefficient being tested (the `y⁴` resp. `y⁵` Taylor coefficient of
  `H₀ d_L/c`).
* **Lower-order coefficients.** (10.54) is already known to carry a wrong overall sign, so using
  the printed lower-order coefficients would make the D³ test fail for a reason unrelated to
  (10.55). We therefore **existentially quantify** all lower-order coefficients: the claim for
  (10.55) is "there are some `c₀, c₁, c₂` such that `H₀ d_L/c − y(c₀ + c₁y + c₂y² + D³y³) = o(y⁴)`",
  i.e. "the `y⁴` Taylor coefficient of `H₀ d_L/c` in `y` is the printed `D³_{L,y}`". It does not
  depend on whether (10.52)–(10.54) are right. Likewise for (10.56)–(10.57) with `c₀ … c₃`.
  These existential forms are the weakest readings; the explicit variants (lower coefficients
  = (10.52), (10.53), sign-corrected (10.54) [and, for D⁴, a given D³]) imply them
  (`claimD3Explicit_imp`), so refuting the existential form refutes every such variant.
* **Typography of (10.56)–(10.57).** The line break "… − 15q₀s₀ + (10.56) − 57j₀ …" is read as
  `… − 15 q₀ s₀ − 57 j₀ …`, and "10j²" as `10 j₀²`. (These readings make the flat, `Ω₀ = 1`,
  part of the printed D⁴ agree exactly with the independent derivation in
  `C6_blind_sympy.py`; the alternative "+57j₀" would disagree also in the flat case.)
  The Milne counterexample below has `j₀ = 0`, so it is insensitive to both readings.

## Result
Both claims are refuted in Lean by the Milne model `a(t) = t`, `c = 1`, `K = −1`, `t₀ = 1`
(`q₀ = j₀ = s₀ = l₀ = 0`, `Ω₀ = 0`, `H₀ d_L/c = y(2 − y)/(2(1−y)²) = y Σ (n+2)/2 · yⁿ`):
the true coefficients are `D³ = 5/2`, `D⁴ = 3`; the printed formulas give `13/6` and `359/120`.
-/

namespace C6Blind

open Filter Topology Asymptotics
open scoped ContDiff

/-! ### Cosmographic parameters (10.1)–(10.5) -/

/-- Hubble parameter `H = ȧ/a`. -/
noncomputable def hub (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Deceleration `q = −(ä/a)/H²`. -/
noncomputable def decel (a : ℝ → ℝ) (t : ℝ) : ℝ := -(iteratedDeriv 2 a t / a t) / hub a t ^ 2

/-- Jerk `j = (a⃛/a)/H³`. -/
noncomputable def jerk (a : ℝ → ℝ) (t : ℝ) : ℝ := (iteratedDeriv 3 a t / a t) / hub a t ^ 3

/-- Snap `s = (a⁗/a)/H⁴`. -/
noncomputable def snap (a : ℝ → ℝ) (t : ℝ) : ℝ := (iteratedDeriv 4 a t / a t) / hub a t ^ 4

/-- Lerk `l = (a⁽⁵⁾/a)/H⁵`. -/
noncomputable def lerk (a : ℝ → ℝ) (t : ℝ) : ℝ := (iteratedDeriv 5 a t / a t) / hub a t ^ 5

/-! ### Redshifts and distances -/

/-- Redshift of light emitted at `t`, observed at `t₀`: `1 + z = a(t₀)/a(t)`. -/
noncomputable def zred (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1

/-- y-redshift `y = z/(1+z)`. -/
noncomputable def yred (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := zred a t₀ t / (1 + zred a t₀ t)

/-- Comoving (angular) coordinate distance `∫_t^{t₀} c dt'/a(t')` (dimensionless, `a` a length). -/
noncomputable def comoving (c : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ s in t..t₀, c / a s

/-- Spatial curvature `K ∈ {+1, 0, −1}`. -/
inductive Curv
  | closed  -- K = +1
  | flat    -- K = 0
  | hyper   -- K = −1
  deriving DecidableEq

/-- The value of `K`. -/
def Curv.K : Curv → ℝ
  | .closed => 1
  | .flat => 0
  | .hyper => -1

/-- The transverse function `S_K` of (10.28): `sin`, `id`, `sinh`. -/
noncomputable def Curv.S : Curv → ℝ → ℝ
  | .closed => Real.sin
  | .flat => id
  | .hyper => Real.sinh

/-- Luminosity distance (10.26)–(10.28), as a function of the emission time `t = t₀ − D/c`:
`d_L = [a(t₀)/a(t)] · a(t₀) · S_K(∫_t^{t₀} c dt'/a)`. -/
noncomputable def lumDist (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  (a t₀ / a t) * (a t₀ * k.S (comoving c a t₀ t))

/-- Dimensionless luminosity distance `H₀ d_L / c`. -/
noncomputable def dLnorm (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  hub a t₀ * lumDist c k a t₀ t / c

/-- `Ω₀ = 1 + K c²/(H₀² a₀²)` (p. 110). -/
noncomputable def Omega0 (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ : ℝ) : ℝ :=
  1 + k.K * c ^ 2 / (hub a t₀ ^ 2 * a t₀ ^ 2)

/-! ### Printed coefficients -/

/-- (10.53) as printed. -/
noncomputable def printedD1 (q : ℝ) : ℝ := -(1 / 2) * (-3 + q)

/-- (10.54) with the overall sign corrected (background fact; used only in explicit variants). -/
noncomputable def correctedD2 (q j Ω : ℝ) : ℝ := (1 / 6) * (12 - 5 * q + 3 * q ^ 2 - j - Ω)

/-- (10.55) as printed:
`D³_{L,y} = (1/24)[52 − 20q₀ + 21q₀² − 15q₀³ − 7j₀ + 10q₀j₀ + s₀ − 2Ω₀(1 + 3q₀)]`. -/
noncomputable def printedD3 (q j s Ω : ℝ) : ℝ :=
  (1 / 24) * (52 - 20 * q + 21 * q ^ 2 - 15 * q ^ 3 - 7 * j + 10 * q * j + s - 2 * Ω * (1 + 3 * q))

/-- (10.56)–(10.57) as printed (reading "+ (10.56) − 57j₀" as `− 57 j₀`, "10j²" as `10 j₀²`):
`D⁴_{L,y} = (1/120)[359 − 184q₀ + 186q₀² − 135q₀³ + 105q₀⁴ + 90q₀j₀ − 105q₀²j₀ − 15q₀s₀ − 57j₀
 + 10j₀² + 9s₀ − l₀ − 5Ω₀(17 − 6q₀ + 9q₀² − 2j₀)]`. -/
noncomputable def printedD4 (q j s l Ω : ℝ) : ℝ :=
  (1 / 120) * (359 - 184 * q + 186 * q ^ 2 - 135 * q ^ 3 + 105 * q ^ 4 + 90 * q * j
    - 105 * q ^ 2 * j - 15 * q * s - 57 * j + 10 * j ^ 2 + 9 * s - l
    - 5 * Ω * (17 - 6 * q + 9 * q ^ 2 - 2 * j))

/-- Independently derived correct `D³_{L,y}` (see `C6_blind_sympy.py`), for reference only. -/
noncomputable def derivedD3 (q j s Ω : ℝ) : ℝ :=
  (1 / 24) * (60 - 32 * q + 21 * q ^ 2 - 15 * q ^ 3 - 7 * j + 10 * q * j + s - 2 * Ω * (5 - 3 * q))

/-- Independently derived correct `D⁴_{L,y}` (see `C6_blind_sympy.py`), for reference only. -/
noncomputable def derivedD4 (q j s l Ω : ℝ) : ℝ :=
  (1 / 120) * (360 - 234 * q + 186 * q ^ 2 - 135 * q ^ 3 + 105 * q ^ 4 + 90 * q * j
    - 105 * q ^ 2 * j - 15 * q * s - 57 * j + 10 * j ^ 2 + 9 * s - l
    - Ω * (87 - 80 * q + 45 * q ^ 2 - 10 * j) + Ω ^ 2)

/-! ### Model class -/

/-- Admissible data: `c > 0`, analytic scale factor, `a(t₀) > 0`, expanding at `t₀`. -/
structure Admissible (c : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop where
  c_pos : 0 < c
  analytic : ContDiff ℝ ω a
  a_pos : 0 < a t₀
  expanding : 0 < hub a t₀

/-! ### Claim statements -/

/-- Remainder for (10.55): `H₀d_L/c − y(c₀ + c₁y + c₂y² + D³_{L,y} y³)` with the printed `D³`. -/
noncomputable def rem3 (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ c₀ c₁ c₂ t : ℝ) : ℝ :=
  dLnorm c k a t₀ t - yred a t₀ t * (c₀ + c₁ * yred a t₀ t + c₂ * yred a t₀ t ^ 2
    + printedD3 (decel a t₀) (jerk a t₀) (snap a t₀) (Omega0 c k a t₀) * yred a t₀ t ^ 3)

/-- **Claim (10.55)** (weakest reading): for every `K`, `c` and admissible model there are
lower-order coefficients `c₀, c₁, c₂` such that
`H₀ d_L/c = y(c₀ + c₁y + c₂y² + D³_{L,y} y³) + o(y⁴)` as `t → t₀⁻`. -/
def ClaimD3 : Prop :=
  ∀ (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ : ℝ), Admissible c a t₀ →
    ∃ c₀ c₁ c₂ : ℝ, (fun t => rem3 c k a t₀ c₀ c₁ c₂ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4)

/-- Explicit variant of (10.55): lower coefficients (10.52), (10.53), sign-corrected (10.54). -/
def ClaimD3Explicit : Prop :=
  ∀ (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ : ℝ), Admissible c a t₀ →
    (fun t => rem3 c k a t₀ 1 (printedD1 (decel a t₀))
        (correctedD2 (decel a t₀) (jerk a t₀) (Omega0 c k a t₀)) t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 4)

/-- Remainder for (10.56)–(10.57):
`H₀d_L/c − y(c₀ + c₁y + c₂y² + c₃y³ + D⁴_{L,y} y⁴)` with the printed `D⁴`. -/
noncomputable def rem4 (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ c₀ c₁ c₂ c₃ t : ℝ) : ℝ :=
  dLnorm c k a t₀ t - yred a t₀ t * (c₀ + c₁ * yred a t₀ t + c₂ * yred a t₀ t ^ 2
    + c₃ * yred a t₀ t ^ 3
    + printedD4 (decel a t₀) (jerk a t₀) (snap a t₀) (lerk a t₀) (Omega0 c k a t₀)
        * yred a t₀ t ^ 4)

/-- **Claim (10.56)–(10.57)** (weakest reading): for every `K`, `c` and admissible model there
are `c₀, …, c₃` with `H₀ d_L/c = y(c₀ + c₁y + c₂y² + c₃y³ + D⁴_{L,y} y⁴) + o(y⁵)`, `t → t₀⁻`. -/
def ClaimD4 : Prop :=
  ∀ (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ : ℝ), Admissible c a t₀ →
    ∃ c₀ c₁ c₂ c₃ : ℝ,
      (fun t => rem4 c k a t₀ c₀ c₁ c₂ c₃ t) =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5)

/-- Explicit variant of (10.56)–(10.57): lower coefficients (10.52), (10.53), sign-corrected
(10.54) and a `D³` supplied by the user of the statement (any choice; the existential form
covers them all). Stated with the printed `D³` for definiteness. -/
def ClaimD4ExplicitPrintedD3 : Prop :=
  ∀ (c : ℝ) (k : Curv) (a : ℝ → ℝ) (t₀ : ℝ), Admissible c a t₀ →
    (fun t => rem4 c k a t₀ 1 (printedD1 (decel a t₀))
        (correctedD2 (decel a t₀) (jerk a t₀) (Omega0 c k a t₀))
        (printedD3 (decel a t₀) (jerk a t₀) (snap a t₀) (Omega0 c k a t₀)) t)
      =o[𝓝[<] t₀] (fun t => yred a t₀ t ^ 5)

theorem claimD3Explicit_imp : ClaimD3Explicit → ClaimD3 :=
  fun h c k a t₀ ha => ⟨_, _, _, h c k a t₀ ha⟩

theorem claimD4ExplicitPrintedD3_imp : ClaimD4ExplicitPrintedD3 → ClaimD4 :=
  fun h c k a t₀ ha => ⟨_, _, _, _, h c k a t₀ ha⟩

/-! ### Refutation by the Milne model `a(t) = t`, `c = 1`, `K = −1`, `t₀ = 1` -/

section Milne

/-- Peeling one Taylor coefficient off a function that is `o(y^{m+1})` as `y → 0⁺`. -/
lemma peel {b : ℝ} {g : ℝ → ℝ} (hg : Continuous g) {m : ℕ}
    (h : (fun y => b + y * g y) =o[𝓝[>] (0 : ℝ)] (fun y => y ^ (m + 1))) :
    b = 0 ∧ g =o[𝓝[>] (0 : ℝ)] (fun y => y ^ m) := by
  have T1 : Tendsto (fun y => b + y * g y) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
    have hc : Continuous (fun y => b + y * g y) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have T2 : Tendsto (fun y : ℝ => y ^ (m + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := (continuous_pow (m + 1) : Continuous fun y : ℝ => y ^ (m + 1)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hb : b = 0 := tendsto_nhds_unique T1 (h.isBigO.trans_tendsto T2)
  refine ⟨hb, ?_⟩
  subst hb
  have h' : (fun y => y * g y) =o[𝓝[>] (0 : ℝ)] (fun y => y ^ (m + 1)) := by simpa using h
  have h2 := (isBigO_refl (fun y : ℝ => y⁻¹) (𝓝[>] (0 : ℝ))).mul_isLittleO h'
  refine h2.congr' ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin] with y hy
    have : y ≠ 0 := ne_of_gt hy
    field_simp
  · filter_upwards [eventually_mem_nhdsWithin] with y hy
    have : y ≠ 0 := ne_of_gt hy
    rw [pow_succ]; field_simp

/-- Last peeling step: a function `b + y g(y)` that is `o(1)` as `y → 0⁺` has `b = 0`. -/
lemma peel0 {b : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (h : (fun y => b + y * g y) =o[𝓝[>] (0 : ℝ)] (fun y => y ^ 0)) : b = 0 := by
  have T1 : Tendsto (fun y => b + y * g y) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
    have hc : Continuous (fun y => b + y * g y) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h1 : (fun y => b + y * g y) =o[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) := by simpa using h
  exact tendsto_nhds_unique T1 ((isLittleO_one_iff ℝ).1 h1)

lemma iteratedDeriv_id_succ_succ (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 2) (fun t : ℝ => t) x = 0 := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  have h1 : deriv (fun t : ℝ => t) = fun _ => (1 : ℝ) := by funext t; simp
  rw [h1]
  have h2 : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => (0 : ℝ) := by funext t; simp
  rw [h2, iteratedDeriv_const]; split_ifs <;> rfl

lemma milne_hub : hub (fun t : ℝ => t) 1 = 1 := by simp [hub]

lemma milne_decel : decel (fun t : ℝ => t) 1 = 0 := by
  simp [decel, iteratedDeriv_id_succ_succ 0]

lemma milne_jerk : jerk (fun t : ℝ => t) 1 = 0 := by
  simp [jerk, iteratedDeriv_id_succ_succ 1]

lemma milne_snap : snap (fun t : ℝ => t) 1 = 0 := by
  simp [snap, iteratedDeriv_id_succ_succ 2]

lemma milne_lerk : lerk (fun t : ℝ => t) 1 = 0 := by
  simp [lerk, iteratedDeriv_id_succ_succ 3]

lemma milne_Omega0 : Omega0 1 .hyper (fun t : ℝ => t) 1 = 0 := by
  simp [Omega0, milne_hub, Curv.K]

lemma milne_y {t : ℝ} (ht : 0 < t) : yred (fun t : ℝ => t) 1 t = 1 - t := by
  simp only [yred, zred]
  field_simp
  ring

lemma milne_dLnorm {t : ℝ} (ht : 0 < t) :
    dLnorm 1 .hyper (fun t : ℝ => t) 1 t = (1 / t) * ((1 / t - t) / 2) := by
  simp only [dLnorm, lumDist, comoving, Curv.S, milne_hub]
  rw [integral_one_div_of_pos ht one_pos, Real.sinh_eq, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

lemma milne_admissible : Admissible 1 (fun t : ℝ => t) 1 :=
  ⟨one_pos, contDiff_id, one_pos, by rw [milne_hub]; exact one_pos⟩

/-- `t = 1 − u` maps `u → 0⁺` to `t → 1⁻`. -/
lemma tendsto_one_sub : Tendsto (fun u : ℝ => 1 - u) (𝓝[>] (0 : ℝ)) (𝓝[<] (1 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hc : Continuous (fun u : ℝ => 1 - u) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_mem_nhdsWithin] with u hu
    simp only [Set.mem_Iio]; simp only [Set.mem_Ioi] at hu; linarith

/-- (10.55) is false (in its weakest reading, hence in every explicit variant). -/
theorem not_claimD3 : ¬ ClaimD3 := by
  intro hC
  obtain ⟨c₀, c₁, c₂, h⟩ := hC 1 .hyper (fun t => t) 1 milne_admissible
  have h1 := h.comp_tendsto tendsto_one_sub
  set d : ℝ := printedD3 0 0 0 0 with hd
  have hd' : d = 13 / 6 := by rw [hd]; norm_num [printedD3]
  -- explicit form on `u ∈ (0,1)`
  have h2 : (fun u : ℝ => (1 / (1 - u)) * ((1 / (1 - u) - (1 - u)) / 2)
      - u * (c₀ + c₁ * u + c₂ * u ^ 2 + d * u ^ 3)) =o[𝓝[>] (0 : ℝ)] (fun u => u ^ 4) := by
    refine h1.congr' ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
      have ht : 0 < 1 - u := by linarith [hu.2]
      simp only [Function.comp, rem3, milne_dLnorm ht, milne_y ht, milne_decel, milne_jerk,
        milne_snap, milne_Omega0, hd]
      ring
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
      have ht : 0 < 1 - u := by linarith [hu.2]
      simp only [Function.comp, milne_y ht]
      ring
  -- multiply by the bounded factor `(1 − u)²`
  have hB : (fun u : ℝ => (1 - u) ^ 2) =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) := by
    have hc : Continuous (fun u : ℝ => (1 - u) ^ 2) := by fun_prop
    exact ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have h3 := hB.mul_isLittleO h2
  have h4 : (fun u : ℝ => 0 + u * ((1 - c₀) + u * ((-1 / 2 - (c₁ - 2 * c₀))
      + u * ((-(c₂ - 2 * c₁ + c₀)) + u * ((-(d - 2 * c₂ + c₁))
      + u * ((-(-2 * d + c₂)) + u * (-d)))))))
      =o[𝓝[>] (0 : ℝ)] (fun u => u ^ (3 + 1)) := by
    refine h3.congr' ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
      have ht : 1 - u ≠ 0 := by linarith [hu.2]
      field_simp
      ring
    · exact Eventually.of_forall fun u => by ring
  obtain ⟨-, h5⟩ := peel (by fun_prop) h4
  obtain ⟨e1, h6⟩ := peel (by fun_prop) h5
  obtain ⟨e2, h7⟩ := peel (by fun_prop) h6
  obtain ⟨e3, h8⟩ := peel (by fun_prop) h7
  have e4 := peel0 (by fun_prop) h8
  rw [hd'] at e4
  linarith

theorem not_claimD3Explicit : ¬ ClaimD3Explicit := fun h => not_claimD3 (claimD3Explicit_imp h)

/-- (10.56)–(10.57) are false (in their weakest reading, hence in every explicit variant). -/
theorem not_claimD4 : ¬ ClaimD4 := by
  intro hC
  obtain ⟨c₀, c₁, c₂, c₃, h⟩ := hC 1 .hyper (fun t => t) 1 milne_admissible
  have h1 := h.comp_tendsto tendsto_one_sub
  set d : ℝ := printedD4 0 0 0 0 0 with hd
  have hd' : d = 359 / 120 := by rw [hd]; norm_num [printedD4]
  have h2 : (fun u : ℝ => (1 / (1 - u)) * ((1 / (1 - u) - (1 - u)) / 2)
      - u * (c₀ + c₁ * u + c₂ * u ^ 2 + c₃ * u ^ 3 + d * u ^ 4))
      =o[𝓝[>] (0 : ℝ)] (fun u => u ^ 5) := by
    refine h1.congr' ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
      have ht : 0 < 1 - u := by linarith [hu.2]
      simp only [Function.comp, rem4, milne_dLnorm ht, milne_y ht, milne_decel, milne_jerk,
        milne_snap, milne_lerk, milne_Omega0, hd]
      ring
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
      have ht : 0 < 1 - u := by linarith [hu.2]
      simp only [Function.comp, milne_y ht]
      ring
  have hB : (fun u : ℝ => (1 - u) ^ 2) =O[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) := by
    have hc : Continuous (fun u : ℝ => (1 - u) ^ 2) := by fun_prop
    exact ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have h3 := hB.mul_isLittleO h2
  have h4 : (fun u : ℝ => 0 + u * ((1 - c₀) + u * ((-1 / 2 - (c₁ - 2 * c₀))
      + u * ((-(c₂ - 2 * c₁ + c₀)) + u * ((-(c₃ - 2 * c₂ + c₁))
      + u * ((-(d - 2 * c₃ + c₂)) + u * ((-(-2 * d + c₃)) + u * (-d))))))))
      =o[𝓝[>] (0 : ℝ)] (fun u => u ^ (4 + 1)) := by
    refine h3.congr' ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
      have ht : 1 - u ≠ 0 := by linarith [hu.2]
      field_simp
      ring
    · exact Eventually.of_forall fun u => by ring
  obtain ⟨-, h5⟩ := peel (by fun_prop) h4
  obtain ⟨e1, h6⟩ := peel (by fun_prop) h5
  obtain ⟨e2, h7⟩ := peel (by fun_prop) h6
  obtain ⟨e3, h8⟩ := peel (by fun_prop) h7
  obtain ⟨e4, h9⟩ := peel (by fun_prop) h8
  have e5 := peel0 (by fun_prop) h9
  rw [hd'] at e5
  linarith

theorem not_claimD4ExplicitPrintedD3 : ¬ ClaimD4ExplicitPrintedD3 :=
  fun h => not_claimD4 (claimD4ExplicitPrintedD3_imp h)

/-- Sanity: the printed and derived coefficients differ exactly by curvature terms. -/
example (q j s Ω : ℝ) : printedD3 q j s Ω - derivedD3 q j s Ω = -(Ω - 1) * (3 * q - 2) / 6 := by
  unfold printedD3 derivedD3; ring

example (q j s l Ω : ℝ) :
    printedD4 q j s l Ω - derivedD4 q j s l Ω = -(Ω - 1) * (Ω + 50 * q - 1) / 120 := by
  unfold printedD4 derivedD4; ring

end Milne

end C6Blind
