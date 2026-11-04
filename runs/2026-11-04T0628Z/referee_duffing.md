# Referee report: `Work/Sim/Duffing.lean` (frozen 2026-11-04T0628Z)

Scope: I read only `Work/Sim/Duffing.lean`. I ran no Lean build. Numerics were done in Python (mpmath, 40 digits), with scratch files in /tmp/claude-0/referee/.

**Verdict: STANDS-WITH-CORRECTIONS.** Both Lean statements say what they are meant to say, and the numbers are right with comfortable margins. All the corrections below concern the docstrings, the framing and the novelty claims. None requires changing a frozen statement.

## 1. Attack on the statements

**`IsDuffingIVP k β x₀ v₀ T x`**
- What it says: `x 0 = x₀`, and there is a function `v` with `v 0 = v₀` such that, for every t ∈ [0,T], `HasDerivAt x (v t) t` and `HasDerivAt v (-k*x t - β*x t^3) t`.
- Parsing: `-k * x t - β * x t ^ 3` parses as (−k)·x(t) − β·(x(t))³. That is x'' = −kx − βx³, the correct sign convention.
- Coercions: every numeral (`6/5`, `1192005/1000000`, `1192006/1000000`) is elaborated in ℝ, through `Icc (0:ℝ)`, `x : ℝ → ℝ` and `T : ℝ`. There is no ℕ-division junk, and the statements contain no `sqrt`, `log` or `/0`.
- `v` is pinned down: on [0,T], `v = x'`. Then v' = −kx − βx³ is continuous, so x is C² on [0,T] and really solves the second-order ODE there.
- Outside [0,T], x and v are unconstrained apart from what two-sided differentiability at 0 and T forces. That is harmless, because the conclusion only looks at times in [0, 1.192006] ⊂ [0, 6/5].
- **Two-sided `HasDerivAt` at the endpoints: harmless and slightly too strong.**
  - As a hypothesis of `duffing_first_zero`, it makes the theorem apply to fewer functions. No generality is really lost, though. The field is polynomial and the energy E = v²/2 + x²/2 + x⁴/4 = 3/4 is conserved, so solutions exist globally. Any solution with one-sided derivatives on [0,T] therefore agrees on [0,T] with a global, two-sided one. Restricted to [0,T], the set of covered functions is the same.
  - The Mathlib Grönwall lemma `dist_le_of_approx_trajectories_ODE_of_mem` needs `HasDerivWithinAt … (Ici t) t` on `Ico a b` plus continuity on `Icc a b`. Both follow from `HasDerivAt` on `Icc`, so the hypothesis fits the intended proof.
  - For `duffing_exists`, two-sided derivatives make the witness slightly harder to build, since it must be differentiable at 0 and at 6/5. That makes the existence statement stronger, which is fine.
- **Docstring error.** The convention paragraph says "(two-sided derivatives, so x solves the equation on an open set containing [0, T])". This is false. The ODE identities hold only at points of [0,T]. Two-sidedness only means the derivative at 0 and at T is a two-sided limit (correction 1).

**`duffing_first_zero`**
- Hypothesis: `IsDuffingIVP 1 1 1 0 (6/5) x`, which quantifies over *every* solution. That is the right, strong form: uniqueness comes for free from Grönwall.
- Conclusion: x > 0 on [0, 1.192005] and x(1.192006) < 0.
- Does this imply "the first zero lies in (1.192005, 1.192006)"? Yes. x is continuous on [0, 6/5], so the intermediate value theorem gives a zero in (1.192005, 1.192006), and there is none in [0, 1.192005]. Hence inf{t ∈ [0, 6/5] : x t = 0} lies in (1.192005, 1.192006). The step needs the IVT, which the docstring's "hence" leaves implicit. Uniqueness of the zero inside that interval is not stated and is not needed for the "first zero" claim.
- Not certified by these statements, though the header advertises them: that this zero is the quarter period, and the value of the period (correction 4).

**Vacuity and triviality**
- `duffing_exists` closes the vacuity hole.
- Nothing is trivial. The hypothesis is consistent (a solution exists). The conclusion is false for nearby endpoints, for example 1.1920056 in place of 1.192006. Neither theorem can be closed by `simp` or `norm_num`.
- `duffing_exists` is not free either. Mathlib's Picard–Lindelöf is local, so one has to continue the solution to [0, 6/5] using the energy bound. Mathlib has no Jacobi elliptic functions, so the closed form cannot serve as the witness.

**Feasibility (information, not a defect)**
- The margins in x are only about 6×10⁻⁷ (see §2).
- On ℝ×ℝ with the sup norm, F(x,v) = (v, −x−x³) has Lipschitz constant max(1, 1+3a²) = 4 (+) on the energy box |x| ≤ 1 (+ slack), |v| ≤ √(3/2).
- At t = 1.192006, e^{Kt} ≈ 117.7. With δ = 0, the Grönwall bound is ε·(e^{Kt}−1)/K ≈ 29.2·ε. So the defect of the approximate trajectory must satisfy ε ≲ 2.0×10⁻⁸ (or a weighted norm must be used). This is achievable, but there is little room to spare.

## 2. Independent derivation

- Closed form: with k = β = 1 and amplitude A = 1, write x = A·cn(ωt | m).
  - Substituting gives ω²(1−2m) = k and 2mω² = βA². So ω² = 1 + A² = 2 and m = A²/(2(1+A²)) = 1/4 (parameter; modulus 1/2).
  - Hence x(t) = cn(√2·t | m = 1/4) and t₁ = K(m=1/4)/√2.
- I computed t₁ four independent ways:

| Method | Result |
|---|---|
| mpmath `ellipk(1/4)` | K = 1.685750354812596042871203657799… |
| AGM: π/(2·agm(1, √3/2))/√2 | identical to 40 digits |
| Energy quadrature ∫₀¹ dx/√(3/2 − x² − x⁴/2) | agrees to ~1e−22 (endpoint singularity) |
| Taylor-series ODE integrator (mpmath `odefun`) + `findroot`, no elliptic functions | agrees to 7e−42 |

- A separate double-precision RK4 run (h ≈ 3e−5) reproduces x(1.192005) and x(1.192006) to about 1e−15 in absolute terms.

**t₁ = 1.192005507275615201576129617514…**

**Period = 4t₁ = 4.768022029102460806304518470058…**

- Margins in time: t₁ − 1.192005 = 5.0728×10⁻⁷ and 1.192006 − t₁ = 4.9272×10⁻⁷. **Confirmed: 1.192005 < t₁ < 1.192006.**
- Margins in value: x(1.192005) = +6.21283208×10⁻⁷ and x(1.192006) = −6.03461663×10⁻⁷. The values from cn and from the ODE agree to 40 digits.
- Positivity on all of [0, 1.192005]: on (0, t₁), v = −√(3/2 − x² − x⁴/2) < 0, so x decreases strictly from 1. Positivity on the whole interval is therefore equivalent to x(1.192005) > 0. A certified proof still has to bound x from below cell by cell, and the bound is tight only near the right end.
- x'(t₁) = −√(3/2) = −1.2247448713915890…
- Nit: the header writes "t₁ = 1.1920055073…". The true digits are 1.19200550727…, so "1.1920055073" is a rounding, not a truncation (correction 3).

## 3. Provenance

Sources I found and read:
- **R. H. Rand, *Lecture Notes on Nonlinear Vibrations*, Cornell eCommons, ver. 53**, §2.2 "Elliptic Functions" (https://ecommons.cornell.edu/bitstream/handle/1813/28989/NonlinearVibrations_ver53.pdf). For x'' + x + εαx³ = 0:
  - eq. 61: x = a₁ cn(a₂t + b, k)
  - eq. 67: a₂² = 1 + a₁²αε and k² = a₁²αε / (2(1 + a₁²αε))
  - eq. 69: T = 4K(k)/a₂
  - With a₁ = A and αε = 1, this is exactly T = 4K(k)/√(1+A²) with k² = A²/(2(1+A²)), the formula in the task. Wikipedia's "Duffing equation" article cites this source (pp. 13–17) for the elliptic-function solution.
- **R. Ahamed, S. Ray, "Study of Duffing oscillator using an improved Lindstedt–Poincaré method…", https://arxiv.org/pdf/2607.15233**, eq. 37: T = (4/√(1+p))·K(p/(2(1+p))) with p = εA², using the *parameter* convention. With p = 1 this gives T = 4K(m=1/4)/√2 = 4.76802…. The paper itself prints only the example ε = 0.4, A = 1.5 (T = 4.8714).

Not found or not reachable:
- I did not find the specific value 1.1920055 (or 4.768022) printed for A = 1. To our search, the number is obtained from the printed formula, not quoted from a table.
- DLMF §22.19 (https://dlmf.nist.gov/22.19), the likely standard reference for cn solutions of x'' + ax + bx³ = 0, was blocked by the fetch-permission system and is unverified.
- Convention pitfall: Rand uses the modulus (k = 1/2), while the header and mpmath use the parameter (m = 1/4). Both are consistent here. The header should write K(m = 1/4), equivalently K(k = 1/2) (correction 3).

## 4. Prior art: machine-checked and validated ODE enclosures

Proof assistants:
- **Isabelle/HOL (F. Immler).** Verified ODE enclosure solver in the AFP entry `Ordinary_Differential_Equations` (https://www.isa-afp.org/browser_info/devel/AFP/Ordinary_Differential_Equations/document.pdf). Verified reachability analysis (TACAS 2015, https://link.springer.com/content/pdf/10.1007/978-3-662-46681-0_3.pdf). "A Verified ODE Solver and the Lorenz Attractor" (J. Autom. Reasoning 2018, https://www.ncbi.nlm.nih.gov/pmc/articles/PMC6044317/), which formally re-checks the numerical part of Tucker's proof for Smale's 14th problem. The PMC page was blocked on redirect, so this citation rests on its title and indexing. Certified enclosures of *nonlinear* ODE IVPs inside a proof assistant are therefore not new.
- **Coq.** S. Park and H. Thies, "A Coq Formalization of Taylor Models and Power Series for Solving ODEs", ITP 2024, LIPIcs 309:30 (https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2024.30): certified programs that compute solutions of polynomial ODEs to any precision. Bréhard–Mahboubi–Pous, ITP 2019 (https://drops.dagstuhl.de/opus/volltexte/2019/11063/pdf/LIPIcs-ITP-2019-8.pdf), verifies Chebyshev approximations of functions and does no ODE solving. Makarov–Spitters (Picard iteration in Coq, ITP 2013) is cited from memory only; I did not fetch it.
- **Lean / Mathlib.**
  - Mathlib has Grönwall (`Mathlib/Analysis/ODE/Gronwall`, including `dist_le_of_approx_trajectories_ODE_of_mem`) and Picard–Lindelöf. Yin–Kudryashov, https://arxiv.org/pdf/2602.13247, cover integral curves on Banach manifolds and state explicitly that their work has "no computational components".
  - LeanCert (https://reservoir.lean-lang.org/@alerad/LeanCert) provides interval arithmetic, roots and integrals, with no ODE enclosures on its page.
  - A search hit, "A Lean 4 Framework for the Radii Polynomial Method" (arXiv 2610.02335), **could not be fetched** (permission system). It is potentially close prior art, since radii-polynomial computer-assisted proofs are commonly used for ODE orbits, and **must be checked** before any Lean novelty claim.

Unverified, non-formal validated tools:
- VNODE-LP (Nedialkov), CAPD (Kapela, Mrozek, Wilczak, Zgliczyński et al.) and COSY Infinity (Berz–Makino) are standard non-formal interval and Taylor-model ODE enclosure tools.
- Zhang and Yap, https://arxiv.org/pdf/2602.00162, give complete validated end-cover algorithms and compare them with CAPD and VNODE-LP. Their work is not formal.

Novelty: to our search, no Lean/Mathlib certified enclosure of a nonlinear ODE IVP solution was found. That rests on arXiv 2610.02335 being unchecked. The claim must be scoped to Lean/Mathlib: it is not new in proof assistants (Isabelle 2014–2018, Coq 2024).

## 5. Verdict: STANDS-WITH-CORRECTIONS

1. Delete or rewrite "(two-sided derivatives, so x solves the equation on an open set containing [0, T])". Suggested text: "derivatives are two-sided, so x must be differentiable as a function on ℝ at 0 and T; the ODE identities are required only at points of [0, T]."
2. Reframe the Question paragraph. The period of the undamped, unforced Duffing oscillator is *classically known in closed form* (Rand eqs. 61/67/69; Ahamed–Ray eq. 37), not "usually obtained by numerical integration or perturbation series". The closed form is the independent check. The contribution is the certified-enclosure method, not the number.
3. Notation and digits: write K(m = 1/4) (modulus 1/2) explicitly, and write t₁ = 1.19200550727… (or ≈ 1.1920055073).
4. State that "hence the first zero lies in (1.192005, 1.192006)" uses continuity and the IVT. "First zero" means inf of zeros in [0, 6/5]. The quarter-period identification and the period 4.768022… are informal remarks, not certified by these theorems. Optionally add a corollary certifying the period via the reversibility symmetry.
5. Add one sentence that two-sided `HasDerivAt` at the endpoints loses no generality, because every one-sided solution on [0,T] agrees there with a global one.
6. Scope any novelty claim to "first Lean/Mathlib certified enclosure of a nonlinear ODE solution, to our search". Cite Immler (Isabelle/HOL) and Park–Thies (Coq). Check arXiv 2610.02335 first.
7. (Planning note, not a statement change.) Required accuracy is about 6×10⁻⁷ in x near t₁. With the sup norm, K ≈ 4 and a Grönwall factor of ≈ 118, the cell defect bound must be ≲ 2×10⁻⁸.
