# Math candidate screen — 2026-11-06T1028Z

Scope: numbers or yes/no answers that (a) have no rigorous enclosure in print, (b) matter to mathematicians, (c) fit one 2-hour session with the toolkit: validated Taylor ODE enclosures (including regular singular points), certified integrals, IVT roots and Chebyshev bounds.

Search budget: about 12 minutes of web search. "Not found" means not found in that time. It is not a literature-review guarantee. Each candidate's search terms are listed so the screen can be extended.

## Ranking (best first)

| # | Candidate | Certified quantity | Fit | Novelty | Interest | Risk |
|---|---|---|---|---|---|---|
| 1 | Thomas–Fermi initial slope B (neutral atom), plus the strong-field variant | enclosure of B ≈ −1.588071022611375… | high (shooting with finite-time events, singular point at 0) | high: digits in print only from numerics, explicitly not proved | OEIS A231786; sets the TF energy coefficient | separatrix instability caps the digits; needs a shooting-monotonicity lemma |
| 2 | Gelfand / Frank-Kamenetskii critical λ* for the 3-D unit ball | λ* ≈ 3.32 (turning point of the bifurcation curve) | very high (same shape as Lane–Emden ω₃: IVP at a singular point, then an IVT root) | high: only "3.32" (numerical, Frank-Kamenetskii) found | classic Gelfand problem / Joseph–Lundgren bifurcation | proving the first local maximum is the global one |
| 3 | Townes soliton height Q(0) for 2-D cubic NLS (optionally the critical mass ‖Q‖²) | Q(0) ≈ 2.2062 | high for Q(0) (two finite-time shooting events); medium for ‖Q‖² (tail) | high: rigorous work found only in 1-D (bounded domain) and 3-D, and coarsely | critical blow-up mass; sharp Gagliardo–Nirenberg constant (Weinstein) | the identification argument uses Kwong uniqueness; the norm needs a tail bound |
| 4 | Hastings–McLeod solution of Painlevé II: y(0), y′(0) | y(0) ≈ 0.36706155, y′(0) ≈ −0.29537 | medium (backward integration is stable; needs certified Airy data at x = X) | high: numerical values only | Tracy–Widom F₂; Painlevé II connection problems | Airy-function enclosure and the Volterra tail bound add work |
| 5 | Blasius constant f″(0) to more than 10 digits | f″(0) = 0.332057336… (standard normalization) | medium (needs f′(∞), tail argument) | medium: a rigorous enclosure exists, but only to 4–5 digits | classical boundary-layer constant; Boyd's survey | partial prior rigorous result; a tighter one may exist unfound |

---

## 1. Thomas–Fermi initial slope B

**Question.** Let y solve y″ = y^{3/2}/√x with y(0) = 1, y(x) → 0 as x → ∞ (the neutral-atom TF function). Enclose B = y′(0) ≈ −1.588071022611375312718684508 to 10–12 or more certified digits.

Optional second target: the strong-magnetic-field TF problem in the same paper. Its right boundary is finite, which fits the toolkit even better. Amore–Boyd–Fernández give slope −0.93896688764395889305505340187…, "accurate to 50 decimal places" by belief.

**Why it matters.**
- B fixes the Thomas–Fermi energy coefficient: E_TF(Z) = −c·Z^{7/3} with c ∝ |B|, and c ≈ 0.7687 hartree. This is the leading term of the Lieb–Simon atomic-energy asymptotics; the exact prefactor should be re-checked before quoting.
- It is a named constant: OEIS A231786, "Negative initial slope of the Thomas–Fermi equation".

**Status in print.**
- Amore, Boyd, Fernández, *Accurate calculation of the solutions to the Thomas–Fermi equations*, https://arxiv.org/abs/1205.1704. It gives 28 digits of B and 50 digits of the magnetic-case slope. The methods are Padé–Hankel, Chebyshev series and numerical integration. The authors say they are "confident" in, or "believe", the digits, and say they "cannot prove" a related singularity conjecture. These are not rigorous results.
- OEIS A231786 (https://oeis.org/A231786): 5000 digits from a Mathematica program (P. J. C. Moses). No rigor claimed.
- Boyd 2013 (J. Comput. Appl. Math. 244, 90–101), *Rational Chebyshev series for the Thomas–Fermi function*: spectral numerics.
- Approximate or rational solutions only: https://arxiv.org/abs/2011.09889, https://arxiv.org/pdf/1604.01454, https://arxiv.org/pdf/1606.07615.
- Searched for: "Thomas-Fermi" with "computer-assisted proof", "validated numerics", "rigorous bounds" or "interval". No interval or computer-assisted enclosure of B found.

**Method.**
1. Substitute x = t². This removes the √x singularity and leaves a regular-singular start at t = 0 with a Puiseux/Taylor seed y = 1 + Bx + (4/3)x^{3/2} + …, the same machinery as Lane–Emden at ξ = 0.
2. Shooting lemma (classical, by comparison; Hille / Sommerfeld-type):
   - If the slope s < B, the solution reaches y = 0 at a finite x.
   - If s > B, y′ reaches 0 while y > 0.
   - Both events happen in finite time and can be certified on a bounded interval.
3. For s_lo < s_hi, certify that the solution from s_lo hits zero and the solution from s_hi turns up. With monotonicity in s, this gives B ∈ (s_lo, s_hi).
4. No tail integral is needed.

**Difficulty.** Moderate. Near the separatrix, perturbations grow like x^{(7+√73)/2} ≈ x^{7.77}. Separating slopes 10⁻¹² apart needs integration to roughly x ≈ 20–40 with tight Taylor cells. This is comparable in effort to the Robertson certification.

**Risk.**
- The monotonicity / shooting lemma must be stated and proved, or cited with a precise reference (Hille 1969, J. Analyse Math.) and checked.
- Wrapping effects along the unstable separatrix may cap the precision at about 8–10 digits within 2 hours. That would still be a new rigorous result.

---

## 2. Critical λ* of the Gelfand (Frank-Kamenetskii) problem in the 3-D unit ball

**Question.** For Δu + λe^u = 0 in B₁ ⊂ ℝ³ with u = 0 on ∂B₁, enclose the extremal value λ*. Above λ* no solution exists. Numerically λ* ≈ 3.32 (the Frank-Kamenetskii sphere value).

**Reduction.**
- Let w solve w″ + (2/s)w′ + eʷ = 0 with w(0) = 0, w′(0) = 0. This is the Emden–Chandrasekhar isothermal equation.
- Radial solutions are u(r) = w(sr) − w(s) with λ = Λ(s) = s²e^{w(s)}.
- So λ* = max_{s>0} Λ(s). The first critical point solves s·w′(s) = −2, a transcendental root of an ODE solution on a bounded interval.

**Why it matters.**
- This is the classic Gelfand problem. Joseph–Lundgren (1973) proved the bifurcation curve has infinitely many turning points for 3 ≤ n ≤ 9; Λ(s) oscillates about 2.
- λ* is the first fold.
- The same number is the Frank-Kamenetskii critical parameter for a sphere, the thermal-explosion threshold.

**Status in print.**
- Wikipedia (Frank-Kamenetskii theory) lists δ_c ≈ 3.32 for the sphere as a "numerical solution by Frank-Kamenetskii". Exact closed forms exist for the slab (0.8785) and the cylinder (2). Source: https://en.wikipedia.org/wiki/Frank-Kamenetskii_theory (read via a mirror: https://ipfs.ssi.eecc.de/ipns/en.wikipedia-on-ipfs.org/wiki/Frank-Kamenetskii_theory).
- Gelfand / Joseph–Lundgren theory papers prove the infinitely-many-turns property but give no value, e.g. https://arxiv.org/pdf/1610.05152.
- https://arxiv.org/pdf/0801.2441 covers the biharmonic analogue only.
- Combustion literature (Boddington–Gray–Harvey era) quotes about 3.322, numerically.
- No interval or computer-assisted enclosure found. Searched for: "Gelfand problem" with "three-dimensional ball", "λ*", "3.32", "rigorous" or "computer-assisted", and "Frank-Kamenetskii sphere 3.322".

**Method.** This is almost a replay of the Lane–Emden n = 3 pipeline.
1. Taylor seed at s = 0 (regular singular point).
2. Validated IVP for (w, w′) on [0, S].
3. IVT root of g(s) = s·w′(s) + 2 at the first sign change, with g′ sign certified.
4. Enclose Λ(s*) = s*²e^{w(s*)}.

**Answer type.** A number. A yes/no add-on: "is the first fold the global maximum of Λ?"

**Difficulty.** Low to moderate. This is the cheapest candidate.

**Risk.** Certifying that λ* is the global maximum needs an argument for large s. Use the Emden–Fowler variables t = ln s, v = s·w′ + 2, z = s²eʷ − 2; this gives an autonomous planar system that spirals into (0, 0). A certified Lyapunov function or decreasing-amplitude bound from some s₀ onward closes it. Without that, the honest claim is "the first local maximum of Λ lies in […]". It is still new, and still the quantity everyone means.

---

## 3. Townes soliton: Q(0) for 2-D cubic NLS (stretch goal: critical mass)

**Question.** Let Q be the unique positive radial H¹ solution of Q″ + Q′/r − Q + Q³ = 0 on ℝ² (Kwong 1989). Enclose Q(0) ≈ 2.2062.

Stretch goal: enclose N_c = ‖Q‖₂² ≈ 11.70. This is the sharp blow-up threshold for 2-D cubic focusing NLS, and it equals the sharp Gagliardo–Nirenberg constant via Weinstein (1983, CMP 87).

**Status in print.**
- Cohen–Li–Schlag, *Uniqueness of excited states to −Δu + u − u³ = 0 in three dimensions* (Anal. PDE 17 (2024); https://par.nsf.gov/servlets/purl/10593107) uses interval arithmetic, but only in **3-D**. Its ground-state bracket is coarse (Q(0) ∈ [4.266, 4.433]). They state other dimensions are "left for another paper".
- https://arxiv.org/abs/1310.6531 (rigorous numerics for NLS) treats 1-D on (0, 1) only, and lists higher dimensions as future work.
- https://arxiv.org/abs/2412.17078 is a large-N Bogoliubov asymptotic study, not an enclosure.
- https://arxiv.org/pdf/2007.03419 (stability in GN inequalities): the numerical GN constant sits in an appendix on the disk; no rigorous enclosure seen.
- Searched for: "Townes soliton" with "computer-assisted", "rigorous enclosure", "Q(0)=2.2062", "1.8622" or "Weinstein constant numerical". No 2-D rigorous enclosure found.

**Method.**
1. Regular singular point at r = 0, as for Lane–Emden.
2. For a_lo, certify that Q′ reaches 0 with Q > 0 ("turns up"). For a_hi, certify that Q reaches 0 first.
3. A standard continuity argument plus Kwong uniqueness gives Q(0) ∈ (a_lo, a_hi).
4. Bounded intervals only, r ≲ 10–15.

**Stretch.** ‖Q‖² needs Q itself, not just the bracket. Enclose the stable manifold, or bound the tail by an explicit K₀-type supersolution for r ≥ R. Then add a certified integral on [0, R].

**Difficulty.** Q(0): moderate. N_c: hard for 2 hours.

**Risk.**
- The bracket-to-ground-state logic must be written carefully.
- The difference between the two events near the separatrix grows like e^{r}, so about 12 digits needs r ≈ 28. That is feasible.

---

## 4. Hastings–McLeod solution of Painlevé II: y(0), y′(0)

**Question.** Let y″ = xy + 2y³ with y ~ Ai(x) as x → +∞. Enclose y(0) ≈ 0.3670615515 and y′(0) ≈ −0.2953721. These are the inputs of every Tracy–Widom F₂ evaluation.

**Status in print.**
- Numerical only, as far as found:
  - Prähofer–Spohn tables: https://arxiv.org/pdf/cond-mat/0212519
  - Bornemann review, *On the numerical evaluation of distributions in random matrix theory*: https://arxiv.org/pdf/0904.1581. It gives error estimates, but not proofs.
  - Fornberg–Weideman computational study: https://www.colorado.edu/amath/node/1766
  - Riemann–Hilbert numerics (Olver): https://arxiv.org/pdf/1210.2199
- Searched for: "Hastings-McLeod" with "interval arithmetic", "validated numerics" or "computer-assisted", and the digit strings. No hits.

**Method.**
1. At x = X ≈ 8, enclose y − Ai through the Volterra equation y = Ai + ∫ₓ^∞ K(x,t)·2y³ dt. Contraction with |y| ≤ 2Ai gives an error of about Ai(X)³, roughly 10⁻²⁴.
2. Enclose Ai(X) and Ai′(X) from DLMF §9.7 asymptotics with explicit error bounds.
3. Integrate backward to 0. Backward integration is stable: the Ai-like mode grows to the left, while the Bi-like mode shrinks.

**Difficulty.** Moderate to high, because of the Airy enclosure plus the Volterra lemma.

**Risk.** Two analytic lemmas outside the current toolkit. The ODE part is easy.

---

## 5. Blasius constant to high precision

**Question.** Enclose α = f″(0) for f‴ + ½ff″ = 0 with f(0) = f′(0) = 0 and f′(∞) = 1. The value is 0.332057336215196…. In the f‴ + ff″ = 0 normalization it is 0.469600….

**Status in print.**
- A rigorous result exists but is low precision. The quasi-solution approach (https://arxiv.org/pdf/1311.0421) proves f″(0) = 0.469600 ± 0.000022, i.e. about 4–5 digits in the f‴ + ff″ = 0 normalization.
- Boyd's high-precision value (SIAM Review 2008, "The Blasius function: computations before computers…") is numerical.
- Searched for: "Blasius constant" with "rigorous", "computer-assisted" or "interval". Nothing tighter found, but this field is crowded.

**Method.**
1. Use the scaling symmetry: solve with f″(0) = 1, then α = λ^{−3/2} where λ = f′(∞).
2. Certify on [0, L] (L ≈ 10).
3. Bound the tail with f″(η) = f″(L)·exp(−½∫_L^η f) and f ≥ f(L) + (η − L)·f′(L). The Gaussian tail gives a rigorous bound on f′(∞) − f′(L).
4. A plain IVP plus a tail inequality, with no shooting needed.

**Difficulty.** Low to moderate.

**Risk.** Lower novelty: it improves an existing rigorous enclosure instead of being a first one. A tighter enclosure may exist that this search missed. The interest is mostly to applied mathematics and fluids.

---

## Notes and other ideas (not ranked)

- **Lane–Emden ξ₁ for other n** (Chandrasekhar's tables, e.g. n = 1.5, 4, 4.5). Cheap reuse of the pipeline. Rigorous enclosures exist for some exponents: Lane–Emden with sub-square exponents is done (Tanaka et al., arXiv 1607.04619). Low novelty.
- **Mathieu characteristic values** (A&S Table 20.1). A good bounded-interval eigenvalue fit via the Floquet condition and IVT. Rigorous large-parameter asymptotics exist (https://arxiv.org/pdf/1507.04984). No validated table was found, but the search was shallow. Medium interest.
- **Painlevé I tritronquée y(0), y′(0).** Tanveer et al. already prove enclosures to about 1.75·10⁻⁷ on [−0.49, 5.5) and the first pole to 4.1·10⁻⁶ (https://arxiv.org/pdf/1412.3782). The novelty would be extra digits only.
- **Bonnor–Ebert critical radius** ξ ≈ 6.451 for the isothermal sphere. Same ODE as candidate 2, but more astrophysics than mathematics.

**Recommendation.** Run #2 (Gelfand λ*) first as the low-risk win: it reuses the ω₃ pipeline almost verbatim. Then run #1 (Thomas–Fermi B), which has the highest payoff because of the OEIS constant and the explicit non-rigorous disclaimer in print. Before quoting any digits, re-check the numeric reference values above (λ* to 4+ digits, Q(0), Hastings–McLeod y′(0)). Several were recalled rather than read from a source in this screen.
