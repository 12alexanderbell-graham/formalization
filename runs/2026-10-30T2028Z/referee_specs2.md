# Referee report: blind specifications for `redshift`, `cosmoCoeff`, `yred`, `omega0`, `curvK`

Files read: `Checked/Fidelity/RedshiftCoeffSpecs.lean`, `Checked/Fidelity/YOmegaKSpecs.lean`
(statements in full; proofs skimmed only). No program definitions were read.
Symbolic checks (sympy, scratch script outside the repo) on every closed-form anchor: all residuals 0.

| Structure | Verdict |
|---|---|
| `RedshiftSpecCore` (+ `RayOK`) | **STANDS** |
| `CosmoCoeffSpecCore` (+ `CoeffOK`) | **STANDS** |
| `YRedSpec` | **STANDS** |
| `Omega0Spec` | **STANDS-WITH-CORRECTIONS** (convention to be documented; no law is wrong) |
| `CurvKSpec` | **STANDS-WITH-CORRECTIONS** (convention to be documented; no law is wrong) |

The corrections are to docstrings and naming, not to any law. None of them lets a wrong
definition through the pin.

---

## 1. `RedshiftSpecCore`, `RayOK`: STANDS

* `integral_law`: `1+z = exp ∫_t^{t₀} ȧ/a ds`. Correct: along a radial null geodesic in FLRW,
  `dλ/λ = H dt`, and integration gives `ln(a₀/a)`. The argument order is observation time first,
  emission time second (`Z a t₀ t`), and it is used the same way in every field. The integrand uses
  Mathlib's global `deriv`. It can differ from the one-sided derivative only at the two endpoints,
  which have measure zero, so the integral is unaffected. Checked symbolically for `cosh s + 1`,
  `s^p` and `e^{hs}`.
* `RayOK`: requires `a > 0` and `C¹` on the closed interval. Both are physically right: you need
  `a > 0` for `ln a`, and `C¹` makes the FTC step clean. The hypothesis is stronger than physics
  needs. Absolutely continuous `a` would do, for example piecewise-matched era models where `ȧ`
  has a kink. The pin therefore says nothing about such `a`. This only narrows coverage and cannot
  cause unsoundness. Optional: say so in the docstring.
* `ratio_law`, `self_zero`, `compose`, `rescale_invariant`, `time_translate`, `local_dep`,
  `expanding_pos`: all textbook-correct. `self_zero` asks only for `a t > 0`, which is fine.
  `expanding_pos` uses `ȧ > 0` on the open interval and `t < t₀`, which is the right sign.
* Anchors: de Sitter `e^{h(t₀−t)} − 1` holds for any real `h` (contracting case included).
  Power law `(t₀/t)^p − 1` is stated for `t, t₀ > 0` only, which is correct because `rpow` is only
  meaningful there. Milne and static anchors are correct. The near-misses (linear Hubble law,
  inverted ratio) are well chosen.
* **Most important remark:** the pin is sound and the determining law is the right one (the
  geodesic form, not the ratio). The only limitation is coverage: rays where `a` is not `C¹` are
  not pinned.

## 2. `CosmoCoeffSpecCore`, `CoeffOK`: STANDS

* `defining`: `C_n = a⁽ⁿ⁾/(a Hⁿ)`. This matches Visser 2004 with `q = −C₂`, `j = C₃`, `s = C₄`,
  using the positive-sign jerk and snap convention of Visser and Cattoën–Visser. Some papers use
  the opposite sign for `j` or `s`. The spec avoids that ambiguity: it stores the sign-neutral
  `C_n` and fixes the `q` sign through the near-miss `not_q_sign`. Good.
* `taylor_law`: `a(t₀+Δ)/a₀ = Σ_{k≤n} C_k (H₀Δ)^k/k! + o(Δⁿ)`. This is exactly Visser's eq. (6).
  Checked symbolically to order 4 for a generic `a = e^s + s³ + 2`: the residual is 0.
* **Smoothness hypothesis** `ContDiffAt ℝ n a t₀`: correct and sufficient. In Mathlib, for finite
  `n` this means `Cⁿ` on a neighbourhood of `t₀`, which is enough for Taylor with Peano remainder
  (`taylor_isLittleO`). It is slightly stronger than the minimal Peano hypothesis (`n`-fold
  differentiable at `t₀`), but it is the clean choice. It also guarantees that `iteratedDeriv n`
  is the genuine `n`-th derivative, which matters because Mathlib's junk value 0 could otherwise
  slip in. The hypothesis is local to `t₀`, which is the right scope.
* `deriv a t ≠ 0`: necessary, since `C_n` is undefined at turnaround or bounce where `H = 0`.
  It is over-demanded for `n = 0` (`C₀ = 1` makes sense anyway), which is harmless. It also
  implies differentiability at `t`, so it never conflicts with Mathlib's junk-value semantics.
* Uniqueness: `H₀ ≠ 0` plus uniqueness of Taylor coefficients determines every `C_k` with
  `k ≤ n`. The law is therefore determining.
* Anchors, all checked symbolically:
  * power law `C_n = p(p−1)⋯(p−n+1)/pⁿ` holds for n = 0..5;
  * matter `q = 1/2`, `j = 1`;
  * radiation `q = 1`;
  * de Sitter `C_n = 1` (also for `h < 0`);
  * Milne `C_{n≥2} = 0`;
  * the `not_unnormalized` value is 4.
* **Most important remark:** the laws and the hypothesis are textbook-correct and determining.
  The only fixed convention is `q = −C₂`, `j = +C₃` (Visser), and it is stated explicitly.

## 3. `YRedSpec`: STANDS

* `law`: `y = 1 − a(t)/a(t₀) = z/(1+z)`, as in Cattoën–Visser 2007 §II. `of_z` and `inv_z`
  (`z = y/(1−y)`) were checked symbolically.
* Range `y < 1`, sign `y > 0 ⇔ a(t) < a(t₀)`, and `strictAnti_a` (larger `a(t)` gives smaller
  `z` and smaller `y`) are all correct.
* Anchors (de Sitter `1 − e^{H(t−t₀)}`, Milne `1 − t/t₀`, the value 1/2 at `z = 1`, static) and
  the near-misses (`z/(1−z)`, `z`, `−z`, sign flip, `log(1+z)`) are correct and pairwise
  distinguishing.
* Every field is demanded only for `a(t₀), a(t) > 0`, which is the physical domain. No smoothness
  is needed because `y` is algebraic in two values of `a`.
* **Most important remark:** fully correct. Note that `shift_inv` is written with `t₀ − τ`, while
  `RedshiftSpecCore.time_translate` uses `t₀ + τ`. Both are consistent; the remark is cosmetic.

## 4. `Omega0Spec`: STANDS-WITH-CORRECTIONS

* `law`: `Ω₀ = 1 + K/(a₀H₀)²`. This follows by dividing `H² = (8πG/3)ρ − K/a²` by `H²` with
  `ρ_crit = 3H²/(8πG)`. It is correct, and `friedmann` was verified symbolically.
* The rescaling `(K, a) ↦ (c²K, c·a)` is right: with `a' = ca` and `r' = r/c`, the metric
  `a²dr²/(1−Kr²)` is preserved when `K' = c²K`. With this, the spec correctly treats `K` as an
  unnormalised curvature constant, not as `k ∈ {−1, 0, +1}`.
* Anchors:
  * Milne (`a = t`, `K = −1`) gives `Ω₀ = 0`.
  * Closed de Sitter (`a = cosh t`, `K = 1`) gives `H² = 1 − 1/a²` and
    `Ω₀ = 1/H² = 1 + 1/sinh² t₀`. Both forms were checked symbolically. `t₀ ≠ 0` is the right
    exclusion (`H = 0` at the bounce).
  * `closed_value` (`a = t`, `K = 1`, so `Ω₀ = 2`) is kinematically fine. The implied fluid has
    `ρ ∝ a⁻²` (`w = −1/3`), so it is a legitimate though exotic model.
  * `not_missing_a0` gives `5/4`, not `2`. Correct.
* Hypotheses: `a₀ > 0` and `H₀ ≠ 0` are exactly where `Ω₀` is defined (`ρ_crit = 0` when
  `H₀ = 0`). `DifferentiableAt` is redundant: `deriv ≠ 0` already implies it. Harmless.
* **Correction (documentation):** the spec silently fixes **Ω₀ = total density parameter**
  (matter + radiation + Λ + …). Visser, Weinberg §1.5 and Dodelson use this convention. However,
  much ΛCDM literature (Carroll–Press–Turner, Peebles 1993, many fits) writes `Ω₀` for the matter
  density alone, with `Ω₀ + Ω_Λ − 1 = K/(a₀H₀)²`. Under that convention `law` is false whenever
  `Λ ≠ 0`. The docstring mentions `ρ_total` once. It should state the convention explicitly, so
  that downstream headlines are not read as statements about `Ω_m`.
* The curvature sign is correct for the stated metric convention (`+K` closed).

## 5. `CurvKSpec`: STANDS-WITH-CORRECTIONS

* `law`: `k = K/(H₀a₀)²`. `law_adot` (`k = K/ȧ₀²`, needs only `ȧ₀ ≠ 0`) and `friedmann`
  (`(8πG/3)ρ/H₀² = 1 + k`) are correct.
* Anchors: Milne `k = −1`; closed de Sitter `1/sinh² t₀`; `value_2t = −1`; and
  `not_missing_a0 = −4` against `K/H₀²`. All verified.
* Sign, linearity in `K`, rescaling and shift invariance are all correct.
* **Correction (documentation, convention hazard):** the spec silently fixes
  **`k = +K/(a₀H₀)² = Ω₀ − 1 = −Ω_k`**, positive for closed universes. This is the Visser /
  Cattoën–Visser cosmography convention, where `kc²/(H₀²a₀²)` appears in the `d_L` series. It is
  the **opposite sign** of the Planck, Weinberg and Dodelson `Ω_k = −K/(a₀H₀)²`. Some older papers
  also call `+K/(a₀H₀)²` "Ω_k". The spec states the relation `Ω_k = −k` and enforces it with
  `not_omega_k`, so it is internally sound. Still:
  * the docstring should warn that `curvK` is **not** `Ω_k`;
  * any headline fed observational `Ω_k` values (for example Planck `Ω_k ≈ 0.001`) must flip the
    sign.

  Without that warning this is the most likely place for a reader to misapply a pinned theorem.
* **Most important remark:** the laws are correct, but the sign convention needs an explicit
  warning wherever `curvK` appears in headline statements.

## Cross-cutting

* Each pin uses only its determining law (`integral_law`, `taylor_law`, or `law`). That law is
  correct and determining on the stated domain, so every pin is as trustworthy as the textbook
  formula it encodes.
* The extra fields add consistency checks; none of them is needed for soundness.
* No field demands a value where the quantity is physically undefined. The exceptions are the
  hypothesis-free anchors, where the value is genuinely defined:
  * `de_sitter` for all `t`;
  * `closed_value`, `milne_value`, and the other concrete values.
