# Referee report: `FriedmannCPL` (Work/Fidelity/BlindSpecs3.lean, section 4, lines 190-221)

**Verdict: STANDS**

Scope: only the definition `FriedmannCPL` and its docstring were reviewed (plus the file's
`open Filter Topology` and the conventions header, which give `𝓝` and `H = deriv a / a`).
Scratch checks: sympy 1.14.0, scripts kept outside the repo.

## 1. Field-by-field check against the intended statement

Intended statement: near `t₀`, `a` solves flat Friedmann (`8πG/3 = 1`, `c = 1`) with pressureless
matter plus a separately conserved CPL dark-energy fluid, `w(z) = w₀ + wₐ z/(1+z)` with `z`
measured from `t₀`; expanding at `t₀`; `Ω = ρ_m(t₀)/ρ_crit(t₀)`.

| Field | Check | Status |
|---|---|---|
| `∃ ρm ρde : ℝ → ℝ, (∀ᶠ t in 𝓝 t₀, …) ∧ …` | Density *functions* are chosen once, globally, and constrained on a neighbourhood. The `∃` sits outside `∀ᶠ`, so this is not a pointwise choice (pointwise would make the HasDerivAt clause meaningless). | correct |
| `0 < a t` | Physical; it also rules out a zero denominator in `H`. | correct |
| `DifferentiableAt ℝ a t` | Needed so that `deriv a t` is the true derivative. It is inside `∀ᶠ`, so it holds on a whole neighbourhood **including `t₀`**, which makes `0 < deriv a t₀` meaningful (no junk `deriv = 0` case). | correct |
| `(deriv a t / a t)^2 = ρm t + ρde t` | Flat Friedmann `H² = (8πG/3)ρ` with `8πG/3 = 1`, `K = 0`. | correct |
| `ρm t * a t^3 = ρm t₀ * a t₀^3` | Dust, `w = 0`. Where `a > 0`, this is equivalent to `ρ̇m + 3Hρm = 0` (it is the integrated form, and it forces `ρm` to be differentiable). | correct |
| `HasDerivAt ρde (-(3 H (1 + (w₀ + wₐ(1 − a t/a t₀))) ρde t)) t` | Continuity `ρ̇ + 3H(1+w)ρ = 0`, rewritten as `ρ̇ = −3H(1+w)ρ`; the sign is right. CPL: `1+z = a₀/a` ⇒ `z/(1+z) = 1 − a/a₀` (sympy: identity holds). The normalisation by `a t₀` matches "z relative to t₀", so it is not the `a₀ = 1` convention. | correct |
| HasDerivAt placement | It is inside `∀ᶠ`, so `ρde` is differentiable at **every** point of a neighbourhood of `t₀`, not only at `t₀`. That is exactly enough for uniqueness (see §2): a neighbourhood contains an interval, and the mean value theorem applies on it. | correct and sufficient |
| `0 < deriv a t₀` | Expanding at `t₀`. Together with `a t₀ > 0` this is equivalent to `H₀ > 0`. | correct |
| `Ω = ρm t₀ / (deriv a t₀ / a t₀)^2` | `ρ_crit = 3H²/(8πG) = H²` in these units. The denominator is `> 0`, so there is no junk division. | correct |

Local versus global: every dynamical constraint is local (`∀ᶠ t in 𝓝 t₀`), as asked. Values of
`a`, `ρm` and `ρde` away from `t₀` are unconstrained, which is harmless.

Lean junk audit: the divisions are `deriv a t / a t` (with `a t > 0`), `a t / a t₀` (with `a t₀ > 0`, because `t₀`
lies in its own neighbourhood) and `ρm t₀ / H₀²` (with `H₀ > 0`). `deriv` is used only where `DifferentiableAt`
holds. There is no `rpow`, `log` or `sqrt` in the definition, so there are no hidden junk branches. No
junk-value issue was found.

## 2. Integration and the equivalent closed form

**Dark energy.** Let `E(t) = (a/a₀)^{3(1+w₀+wₐ)} · exp(3wₐ(1 − a/a₀))`. Using only that `a` is
differentiable and `a > 0`, the chain rule gives
`E'/E = 3(1+w₀+wₐ) ȧ/a − 3wₐ ȧ/a₀ = 3H(1 + w₀ + wₐ(1 − a/a₀)) = 3H(1+w)`,
and therefore `(ρde·E)' = E(ρ̇de + 3H(1+w)ρde) = 0`. sympy confirms this integrating-factor identity
symbolically (residual `0`). Hence `ρde·E` is constant on an interval around `t₀`, by the mean value
theorem. This needs only differentiability on the interval and **not** continuity of `ȧ`, so there
is no Lipschitz or Picard–Lindelöf hypothesis to worry about. The solution is
```
ρde(t) = ρde(t₀) (a₀/a)^{3(1+w₀+wₐ)} exp(−3wₐ(1 − a/a₀))
       = ρde(t₀) (1+z)^{3(1+w₀+wₐ)} exp(−3wₐ z/(1+z)).
```
Checks: sympy shows the residual of `ρ̇ + 3H(1+w)ρ` is `0`. An independent `dsolve` of
`x f' = −3(1 + w₀ + wₐ(1−x))f`, with `x = a/a₀`, returns `C·x^{−3(1+w₀+wₐ)} e^{3wₐx}`, the same family.
This matches Chevallier–Polarski 2001 and Linder 2003. I did not check the equation number in
Capozziello–Lazkoz–Salzano 2011 (Eq. 17), but the formula is the standard CPL density.

**Hubble rate.** Matter gives `ρm = ρm₀(1+z)³`. At `t₀`, `H₀² = ρm₀ + ρde₀`, so `ρm₀ = ΩH₀²` and
`ρde₀ = (1−Ω)H₀²`. Therefore
```
H² = H₀² [ Ω(1+z)³ + (1−Ω)(1+z)^{3(1+w₀+wₐ)} exp(−3wₐ z/(1+z)) ] =: H₀² 𝓔(z)
```
sympy confirms `H² − H₀²𝓔(z) = 0` and `𝓔(0) = 1`.

**Equivalence.** `FriedmannCPL Ω w₀ wₐ a t₀` holds if and only if all of the following hold:
`H₀ := deriv a t₀ / a t₀ > 0`, and for all `t` near `t₀`, `a t > 0`, `a` is differentiable at `t`, and
`H(t) = H₀ √𝓔(z(t))`.

* (⇒) `ρde` is unique (above), so `H² = H₀²𝓔`. Since `a` is continuous at `t₀`, `𝓔∘z` is continuous
  and equals 1 at `t₀`, so `𝓔 > 0` near `t₀`. Hence `H ≠ 0`, so `ȧ ≠ 0` on an interval around `t₀`.
  `ȧ` is a derivative, so it has the intermediate value property (Darboux), and `ȧ(t₀) > 0`. Therefore
  `ȧ > 0` throughout that interval, and `H = +H₀√𝓔`. Darboux is genuinely needed here because `ȧ` need
  not be continuous.
* (⇐) Take `ρm := ΩH₀²(a₀/a)³` and `ρde := (1−Ω)H₀²(a₀/a)^{3(1+w₀+wₐ)}exp(−3wₐ(1−a/a₀))`. These are
  global functions; the junk values where `a ≤ 0` are irrelevant. Near `t₀`, `a > 0` and `a` is
  differentiable, so `ρde` has the required `HasDerivAt` (real power with a positive base). Friedmann
  holds because `H² = H₀²𝓔`, and `Ω` is recovered because `ρm(t₀) = ΩH₀²`.

The predicate is **not vacuous**. For any real `Ω, w₀, wₐ` and `H₀ > 0`, the ODE `ȧ = H₀ a √𝓔(a₀/a − 1)`
has a smooth right-hand side near `a = a₀` (where `𝓔 = 1`), so a local solution exists. The predicate
is also invariant under `a ↦ c·a` for `c > 0` and under time translation, as it should be.

## 3. Too weak or too strong?

* **Too weak:** nothing found. `ρde` must be differentiable on a full neighbourhood, not just at `t₀`.
  `a` must be differentiable at `t₀` too, so `deriv a t₀ > 0` is not a junk escape. The local CPL
  dynamics are pinned down exactly (see the equivalence above). The sign of `H` near `t₀` follows from
  Darboux, so no separate `ȧ > 0` clause is required.
* **Too strong:** nothing found. No sign is imposed on `Ω`, `w₀`, `wₐ`, `ρm` or `ρde`, so `Ω > 1`
  (negative `ρde₀`), phantom `w < −1`, phantom crossing, and even `Ω < 0` are all allowed. Allowing
  `Ω < 0` is a deliberate permissiveness noted in the docstring; it is not a defect. Requiring
  `ρde` to be differentiable is physically implicit in the continuity equation. Requiring `a > 0`
  is standard. No `C¹`/`C²` regularity and no acceleration equation are demanded, which is correct:
  the first Friedmann equation plus the two continuity equations already imply the Raychaudhuri
  equation wherever `H ≠ 0`.
* **Modelling choice (not a defect):** the dark energy is *separately* conserved (no interaction
  term), which is the standard CPL model and what was asked.

## Optional, cosmetic

* The docstring could add one sentence saying that the pair (local `ρde` uniqueness via the integrating
  factor, Darboux for the sign of `H`) gives the closed form `H = H₀√𝓔(z)`. That would help readers
  compare this with implementations that state the closed form. No change to the definition is needed.
