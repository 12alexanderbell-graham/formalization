# Referee report: `Work.Townes.Exists.townes_exists` (Work/Townes/TownesExists.lean)

Run 2026-11-07T0628Z. Frozen statement judged only (no proof exists yet; body is `sorry`).

## VERDICT: STANDS

The statement is faithful to its module doc. It is not vacuous, not trivial, and true: the
float value Q(0) ≈ 2.20620086465074607 lies about 5e-11 inside both ends. Every witness is a genuine positive, decreasing, decaying classical radial solution.
No correction is required. The non-blocking remarks R1–R4 are at the end.

## 1. Attack on fidelity

**Elaboration** (scratch files in the session scratchpad, `lake env lean`, no errors):
- `-(1 / r * φ r) + θ r - θ r ^ 3` is `((-((1/r) * φ r)) + θ r) - (θ r)^3` by `rfl`.
- That is φ' = −φ/r + θ − θ³, i.e. θ'' + θ'/r − θ + θ³ = 0.
- `norm_num` proves `(2.2062008646 : ℝ) = 22062008646/10^10` and the same for …647. The decimals are exact.

**Junk values.**
- `1/r` occurs only under `r ∈ Ioi 0`, so r = 0 (where Mathlib has 1/0 = 0) is never used.
- At r = 0 the only requirements are θ 0 = c, φ 0 = 0, the one-sided derivative of θ within `Ici 0` equal to φ 0, and continuity of φ within `Ici 0`.
- Values on r < 0 are unconstrained and irrelevant. This is an existential statement, so the freedom is harmless.

**Quantifiers.** The form is ∃ c ∈ Ioo a b, ∃ θ φ, (conjunction). This is correct. No hypothesis can make it vacuous, since there are no hypotheses. Nothing makes it trivial: any witness must be a nonconstant global solution (c − c³ ≠ 0, so θ ≡ c fails the ODE).

**Implied regularity** (Lean-checked lemma `reg`, Mathlib axioms only):
- Since `Ici 0 ∈ 𝓝 r` for r > 0, `HasDerivWithinAt θ (φ r) (Ici 0) r` is equivalent to `HasDerivAt θ (φ r) r`.
- φ is continuous on [0,∞): at 0 by the `ContinuousWithinAt` conjunct, and on (0,∞) by `HasDerivAt`.
- θ is continuous on [0,∞).
- The right-hand side −φ/r + θ − θ³ is continuous on (0,∞).
- Hence θ ∈ C¹[0,∞) (one-sided at 0) with θ' = φ, and θ ∈ C²(0,∞).
- θ''(0) and C² of x ↦ θ(|x|) at the origin are not stated. They follow from the equation: rφ(r) = ∫₀ʳ s(θ − θ³) ds gives φ(r)/r → (c − c³)/2. They are not needed for "ground state".

**Is any conjunct unprovable or self-contradictory?** No.
- `φ 0 = 0` is forced, not merely allowed. On (0,∞), (rφ)' = r(θ − θ³), and continuity of φ at 0 gives rφ(r) → 0. So rφ(r) = ∫₀ʳ s(θ − θ³) ds, hence φ(r) → 0 = φ(0). The conjunct is consistent and redundant (R1).
- `HasDerivAt φ … r` at every r > 0 is achievable: the radial solution is real-analytic on (0,∞).
- The one-sided derivative at 0 equals 0, as for the restriction of an even function.

**Can it be met by something that is not a ground state?** No.
- A witness is a positive, strictly decreasing (φ < 0 on (0,∞)) C² solution with θ → 0.
- φ → 0 and exponential decay are not stated but follow. E = φ²/2 − θ²/2 + θ⁴/4 is nonincreasing (E' = −φ²/r) and bounded below. θ → 0 and monotonicity then force φ → 0, and the linearisation θ'' + θ'/r ≈ θ gives e^{−r}/√r decay.
- By Kwong (1989) the positive decaying radial solution is unique, so any witness has c = Q(0).
- The strict sign φ < 0 is stronger than the minimum definition (positive and decaying), but it is true for Q. It does not exclude Q.

**Weaker/stronger than needed.**
- The statement does not by itself say Q(0) ∈ bracket. Only "some ground state has central value in the bracket" is formalised; uniqueness (Kwong) is cited, not formalised. The module doc says this honestly (R3).
- In conjunction with the frozen shooting events, the brackets are sharp. Lemma `endpoint_excluded` (Lean-checked; the statements of `townes_under` and `townes_over` taken verbatim as hypotheses; axioms propext, Classical.choice, Quot.sound) shows that a witness of the conjunction cannot have θ 0 = 2.2062008646 or θ 0 = 2.2062008647.
- A witness restricts to the hypotheses of the shooting lemmas: `mono` to `Icc 0 S` and `HasDerivAt.hasDerivWithinAt`, also Lean-checked. So the open interval `Ioo` is the right choice and is consistent with run 0228Z.

**Provability check** (mathematics, not Lean effort). The standard open-events argument works:
- Let A be the set of undershooting c in [a, b] and B the set of overshooting c. Both are open by continuous dependence on c at the singular point. They are disjoint, a ∈ A and b ∈ B.
- Since [a, b] is connected, there is c* ∈ (a, b) in neither set.
- For c*, the trajectory exists globally (energy). θ > 0 and φ < 0 for all r > 0:
  - a zero of φ with 0 < θ < 1 yields an undershoot;
  - a zero of φ with θ > 1 contradicts φ < 0 just before it;
  - θ = 1, φ = 0, or θ = 0, φ = 0, contradicts uniqueness.
- So θ decreases to a limit L ∈ {0, 1}. L = 1 is impossible because the linearisation at 1 (θ'' + θ'/r = −2(θ − 1)) is oscillatory (J₀(√2 r)). Hence L = 0.
- Every conjunct is therefore true for c*.
- The Lean proof will need continuous dependence on c on compact radius intervals starting from the singular point. That is the main missing infrastructure (R4).

## 2. Independent numerics

Script: `runs/2026-11-07T0628Z/scripts/referee_shoot.py`. mpmath; floating point, not rigorous.

**Method A (own Taylor stepper with bisection).**
- Start from the even series at 0, with 4(k+1)² a_{k+1} = a_k − (a³)_k, summed to r₀ = 1/4 (tail ~ 5e-154).
- Then a fixed-step Taylor recurrence for (r_c + t)θ'' + θ' = (r_c + t)(θ − θ³).
- Events are tested at step ends, and shots run to r ≤ 80.
- 30 bisections on [2.2062008646, 2.2062008647].

**Method B** (independent code path: `mpmath.odefun`, adaptive Taylor) classifies the endpoints and the bisection bracket ± 1e-15.

| Setting | dps | h | Order | Final bracket for Q(0) |
|---|---|---|---|---|
| A1 | 40 | 0.05 | 30 | [2.206200864650746074691, 2.206200864650746074785] |
| A2 | 50 | 0.04 | 36 | identical to A1 |

**Q(0) ≈ 2.2062008646507460747** (20 digits; A1 and A2 agree to all printed digits). It lies 5.075e-11 above 2.2062008646 and 4.925e-11 below 2.2062008647, so it is strictly inside the bracket. This agrees with the 0228Z referee (2.20620086465074607). The present 20-digit value is inside both of that run's brackets.

| θ(0) | A1 (dps 40) | A2 (dps 50) | B (odefun) |
|---|---|---|---|
| 2.2062008646 | UNDER, r ≈ 13.55 | UNDER, r ≈ 13.53 | UNDER, r ≈ 13.55 |
| 2.2062008647 | OVER, r ≈ 13.50 | OVER, r ≈ 13.53 | OVER, r ≈ 13.55 |
| bracket − 1e-15 | — | — | UNDER |
| bracket + 1e-15 | — | — | OVER |

Event radii are step-end values (grid 0.05, 0.04 or 0.1). They are consistent with 13.521 (under) and 13.499 (over) from 0228Z.

## 3. Prior art (search 2026-11-07)

**READ** (WebFetch):
- Li–Yang, "The linearized cubic NLS has no embedded eigenvalue", Invent. Math. 245 (2026), Springer page. It is 3D. It cites Costin–Huang–Schlag's approximate 3D ground state (error ≤ 7·10⁻⁵ e^{−r}/(1+r)). No 2D result and no enclosure of Q(0).
- Cohen–Li–Schlag, APDE 17(6) 2024 (msp.org PDF). It is 3D, uses VNODE-LP interval arithmetic, and gives a ground-state interval b ∈ [4.266, 4.433] (float b₀ ≈ 4.3373). Nothing in 2D.
- Zenodo 19916775: a Lean 4 "Hopf soliton programme" with about 120 unchecked axioms. It is not the Townes soliton and irrelevant.

**NOT READ:**
- arXiv 1310.6531, "Rigorous numerics for NLS: bound states, spectra, and controllability". The WebFetch of arxiv.org/abs timed out on permission and was not retried. Recalled, unverified: Castelli–Teismann, about 1D NLS with a potential.
- The remaining search hits were not opened. They were physics papers (experimental Townes solitons), Gagliardo–Nirenberg constants on tori, or forbidden mirrors (ar5iv, export, html).

**Searches with no relevant 2D hit:**
- "rigorous computer-assisted proof Townes soliton … interval arithmetic"
- "Townes" "2.2062"
- "computer-assisted proof radially symmetric ground state Δu − u + u³ = 0 R² …"
- "validated numerics Townes profile R(0) …"
- "Costin Huang Schlag ground state …"
- "sharp Gagliardo–Nirenberg constant two dimensions rigorous …"
- "Townes soliton Lean OR Coq OR Isabelle"

**Conclusion.** As in 0228Z, I found no published rigorous enclosure of the 2D Townes central value Q(0) and no formal proof about it. The 3D analogues (Cohen–Li–Schlag; Costin–Huang–Schlag) exist, with width at least 1e-4 for the ground-state height. A Lean-checked existence statement with a 1e-10 bracket would be new as far as this screen sees. The screen is limited by the search engine and the pages actually read.

## 4. Remarks (non-blocking; the statement stands as frozen)

- **R1.** `φ 0 = 0` is redundant: it is forced by continuity at 0 plus the equation. Positivity of θ at r = 0 is likewise implied by c > 0. Both are harmless.
- **R2.** The C² regularity at the origin of x ↦ θ(|x|) is implied, not stated. A claim that "ΔQ − Q + Q³ = 0 holds classically in ℝ²" needs that short argument (θ''(0) = (c − c³)/2) if it is ever made formally.
- **R3.** Any THE RESULT / CLAIMS wording "Q(0) ∈ (2.2062008646, 2.2062008647)" must say "given Kwong's uniqueness (1989, not formalised)". Without it, the theorem asserts only that some ground state has its central value there.
- **R4.** Proof-plan warnings:
  - Openness of the two event sets needs continuous dependence on c from the singular point r = 0 (the integral-equation formulation), on [0, 68/5].
  - The c* step must also rule out L = 1 (oscillation about 1) and the degenerate zeros (θ, φ) = (1, 0) or (0, 0) by uniqueness away from 0.
  - `Tendsto θ atTop (𝓝 0)` needs global existence (the energy bound) on all of [0,∞), not only on [0, S].
