# Referee report: Work/Fidelity/BlindFR.lean (metric F(R) + dust, flat FLRW, negative-R convention)

**VERDICT: STANDS** (no mathematical or physical errors found; three usage caveats below, none of which require changing the file)

Scope: only `Work/Fidelity/BlindFR.lean` was read. Independent sympy checks (sympy 1.14) were run from scratch scripts outside the repo.

## 1. Independent derivation of the field equations

Method: I built flat FLRW `ds² = −dt² + a²dx²` symbolically, computed the Christoffel symbols, Ricci tensor and `R_c`, and formed
`E_μν = φ R^c_μν − ½ f g_μν − ∇_μ∇_ν φ + g_μν □φ − T_μν`, where `φ(t) = f′(R_c(t))` and `T = diag(ρ, p a², p a², p a²)`.

| Check | Result |
|---|---|
| `R_c = 6(Ḣ + 2H²)` | residual 0 |
| `E_00 = 3φH² − ρ − ½(φR_c − f) + 3Hφ̇` (De Felice–Tsujikawa 2.15) | residual 0, ratio 1 (sign and normalisation the same) |
| `E_00 + E_11/a² = −2φḢ − (ρ+p) − φ̈ + Hφ̇` (DFT 2.16) | residual 0 |
| Substituted `f(y) = −F(−y)`, `R = −R_c`, `p = 0`, and compared with the Lean `FRFirstEq` (LHS − RHS) | **residual 0** (exact, for an arbitrary function F) |
| Same substitution compared with the Lean `FRSecondEq` | **residual 0** |
| Bianchi consistency with `ρ̇ = −3Hρ`: `d/dt E_00 + 3H·E_2 = 0` (E_2 = Lean second eq LHS − RHS) | identically 0 |

Term by term in `FRFirstEq`:
- `3 F′(R) H²`: factor 3 is correct. F′ is evaluated at `R t`, which is correct because `F′(R) = f′(R_c)`.
- `ρ`: correct.
- `+ (F − R F′)/2`: correct. It is the image of `½(φR_c − f)`, since `φR_c − f = F′·(−R) + F`.
- `− 3 H F″(R) Ṙ`: correct. Here `φ̇ = F″(R)Ṙ`, which is convention independent because `f″(R_c) = −F″(R)` and `Ṙ_c = −Ṙ`. The first derivative is Ṙ, not R̈.

Term by term in `FRSecondEq`:
- `−2 F′ Ḣ`: correct.
- `ρ` (with p = 0): correct.
- `F‴ Ṙ² + F″ R̈`: correct (this is `φ̈`, and `f‴(R_c) = F‴(R)`).
- `− H F″ Ṙ`: correct.
- `Ḣ = deriv (s ↦ ȧ/a)`: correct.
- `deriv^[3] F = deriv (deriv (deriv F))` by `Function.iterate`: as intended.

The docstring's own derivation is also correct line by line. This includes the ii component `(Ḣ+3H²)φ − ½f + Hφ̇ − φ̈ − 3Hφ̇ = κ²p`, `∇_i∇_jφ = −aȧφ̇δ_ij`, and the derivative map `F″ = −f″`, `F‴ = f‴`.

The Bianchi identity shows that `FRSecondEq` follows from `FRFirstEq` on an interval wherever `H ≠ 0`. So the pair is consistent and not over-determined.

## 2. RicciFlatFLRWSpec and DustDensity

**`law`:** `R = −6(ä/a + (ȧ/a)²)` is `−R_c`. This is correct.
- The regularity hypotheses (`a′` is the derivative of `a` eventually near t, `a″ t` is the derivative of `a′` at t, and `a t > 0`) are exactly "twice differentiable at t".
- The law is satisfiable, for example by `Rc a t := −6(deriv (deriv a) t / a t + (deriv a t / a t)²)`, using `EventuallyEq.deriv_eq`.

**Anchors** (checked with sympy):

| Anchor | Value | Status |
|---|---|---|
| de Sitter `c·e^{ht}` | `−12h²` | ✓ |
| radiation `t^{1/2}` | `0` | ✓ |
| matter `t^{2/3}` | `−4/(3t²)` | ✓ |

- The matter remark `R_c = 4/(3t²) = ρ_EdS` (κ² = 1) is ✓.
- Every anchor lies inside the domain where `law` applies (c > 0, t > 0, rpow is smooth near t > 0), so the anchors are consequences of `law`, not extra constraints. No conflict.
- `scale_invariant` and `time_translation` are also derivable from `law` under the stated hypotheses. They are redundant but harmless.

**DustDensity:** `ρ(t) = 3H₀²Ω(a₀/a)³`, with `H₀ = ȧ(t₀)/a(t₀)` and κ² = 1.
- In metric F(R), matter is minimally coupled and the geometric side is identically divergence-free (generalised Bianchi identity, confirmed above). So `∇^μT_μν = 0`, `ρ̇ = −3Hρ` and `ρ ∝ a⁻³` all hold. This is correct.
- Ω is normalised to the GR critical density `3H₀²`, not to `3F′(R₀)H₀²`. The docstring states this explicitly.
- This is the standard cosmography convention (Capozziello–Cardone–Salzano: `H² = ρ_m/(3f′) + ρ_curv/3` with `Ω_M = ρ_M0/ρ_crit`).
- I could not check it against the text of the source paper from this file alone. Anyone comparing with Bamba et al. §XI should confirm the source's Ω_m uses the same normalisation.

## 3. GR and ΛCDM checks

- **`F = R`:** the equations reduce exactly to `3H² = ρ` and `−2Ḣ = ρ` (written as `−2ä/a + 2ȧ²/a² = ρ`) for a generic `a`. ✓
- **`F = R + 2Λ`, `Λ = 4/3`, `a = sinh^{2/3} t`, `Ω = 1/cosh² t₀`, ρ = DustDensity:** both equations give residual 0, both symbolically and numerically at (t, t₀) = (0.7, 1.3) and (2.1, 0.4). ✓
- **Control:** `F = R − 2Λ` with the same data fails the first equation with residual `8/3 = 2Λ`, while the second equation is still satisfied. So the sign of the constant is fixed by `FRFirstEq` alone. `FRSecondEq` cannot detect it, which is expected because the constant drops out of every derivative.
- **Consistency with the source:** with `F(R) = −f(−R)` and `f(R_c) = R_c − 2Λ`, we get `F(R) = −(−R − 2Λ) = R + 2Λ`. This matches the source's statement that its formulas give `F(R₀) = R₀ + 2Λ` for ΛCDM, in the convention where de Sitter has `R = −12H² < 0`. ✓

## 4. Junk-value audit

These are acceptable for a specification, provided its users add the hypotheses below.

- **Divisions** `ȧ/a` and `a₀/a`: these are junk 0 when `a = 0`. Users need `0 < a` on the relevant interval. There is no division by F′, which the file avoids by writing the equations multiplied through.
- **`deriv a t₀` inside DustDensity:** this is junk 0 if `a` is not differentiable at t₀, which would make ρ ≡ 0. Users need `a` differentiable at t₀, which is implied by any C² hypothesis.
- **`deriv^[n] F` with non-smooth F** (the main hazard):
  - If F is not C² on a neighbourhood of `R t`, then `deriv^[3] F (R t) = 0` silently. A theorem proved under "F twice differentiable" would then drop the `F‴Ṙ²` term and still type-check.
  - If F is nowhere differentiable, `FRFirstEq` collapses to `0 = ρ + F(R)/2`.
  - Hence any existence, reconstruction or uniqueness statement built on these definitions **must** assume something like `ContDiffAt ℝ 3 F (R t)`, or `ContDiff ℝ 3 F` on an open set containing the range of R. Otherwise "∃ F satisfying FRFirstEq" is exploitable by junk.
- **`deriv R t`, `deriv^[2] R t` and the Ḣ term:** R̈ involves `a⁽⁴⁾`, so `FRSecondEq` is meaningful only for `a` that is C⁴ near t, and `FRFirstEq` needs `a` C³. Under weaker hypotheses the same junk-zero collapse occurs.
- **`R` is a free argument and is not tied to `RicciFlatFLRWSpec`:** the equations are physically meaningful only when the caller sets `R = Rc a` with `RicciFlatFLRWSpec Rc` (or `R t = −6(ä/a + H²)` pointwise on an interval). A user statement that leaves R unconstrained, for example by quantifying ∃ R, is vacuous physics.
  - I recommend, without requiring it, that downstream theorems either instantiate `R := Rc a` explicitly or carry a hypothesis `∀ s ∈ I, R s = −6(...)`. Pointwise agreement at t alone is **not** enough, because `deriv R t` needs agreement on a neighbourhood.

None of these are defects of the spec. They are obligations for its users, and the docstrings mostly signal them already: "R supplied by the caller (intended R = Rc a)" and "users will add smoothness hypotheses".

## Corrections

None required. Optional, documentation only:
1. Add a sentence to the docstrings of `FRFirstEq` and `FRSecondEq` saying that the intended use has `R = Rc a` on a neighbourhood of t, `a` C⁴ (C³ for the first equation), `F` C³ near `R t`, and `a > 0`.
2. Note that `FRSecondEq` is implied by `FRFirstEq` on an interval where H ≠ 0, via `d/dt E₀₀ + 3H·E₂ = 0`. This is useful for proof engineering.
