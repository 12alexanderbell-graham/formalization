# Referee report: Work/Hiemenz/Hiemenz.lean (frozen statements, run 2026-11-07T2028Z)

**VERDICT: STANDS-WITH-CORRECTIONS.** The correction is in the module doc only: the uniqueness citation range. The three Lean statements stand as written and need no change.

## 1. Attack on the statements
- **Equation and sign.** f''' = -f f'' - 1 + f'^2 gives q' = -(f q) - 1 + p^2, which is the term in all three theorems. The Hiemenz / Falkner–Skan β = 1 form and the boundary conditions f(0) = p(0) = 0, p → 1 are correct.
- **Literals.** `1.2325876568 : ℝ` is the exact rational 12325876568/10^10 (OfScientific). There is no rounding or junk issue, and there is no division or other partial operation anywhere.
- **Vacuity.** Picard–Lindelöf applies because the right-hand side is polynomial. HasDerivWithinAt on Icc 0 S makes f, p, q continuous on [0,S] and forces them to be the unique IVP solution there (Gronwall; for example Mathlib's `ODE_solution_unique_of_mem_Icc_right`). So the hypotheses pin down a single trajectory and are not junk.
  - I integrated both shooting values to η = 20. Neither blows up: at 7.5, f ≈ 6.852, |p - 1| ≤ 4.1e-9, q ≤ 1.233. The S = 15/2 instance, and every S up to at least 20, is therefore satisfiable.
  - For any larger S at which the solution might fail to exist, that instance is vacuous, which is harmless. The conclusion only looks at (0, 15/2], so the condition S ≥ 15/2 is a sound reading.
- **Events.** Under-shoot is q(η) < 0 with p < 1 on [0,η]: the profile peaks below the outer velocity. Over-shoot is p(η) > 1 with q > 0 on [0,η]: monotone overshoot. These are the right, mutually exclusive shooting events. The quantifier ranges are harmless: s = 0 in Icc 0 η is fine because p(0) = 0 < 1 and q(0) > 0.
- **Existence statement.** It asks for a global solution on [0,∞) with one-sided derivatives at 0, f(0) = p(0) = 0, p → 1 and q(0) in the open interval. This is exactly what the module doc claims.
- **Near-misses (not defects).**
  - (a) `hiemenz_exists` does not assert 0 < p < 1 or q > 0. It says "a solution", not "the physical one". Combined with uniqueness at β = 1 (section 3) it nonetheless locates the Hiemenz value. A stronger optional variant would add `∀ η ≥ 0, 0 < q η ∧ p η < 1`.
  - (b) The events alone do not exclude a non-monotone BVP solution from these initial values. The doc says this correctly ("do not give solutions with p ≤ 1 and q ≥ 0").
- **Doc correction.** "Uniqueness … (Coppel 1960, for 0 ≤ β)" is too broad.
  - Uniqueness without restriction on f' holds for 0 ≤ β ≤ 1 (Coppel 1960; Craven–Peletier, Mathematika 19 (1972) 129–133).
  - For β > 0 it holds only under 0 < f' < 1 (attributed to Hartree/Stewartson).
  - For β > 1, reverse-flow solutions exist.
  - β = 1 is covered, so the application is right. Suggested wording: "(Coppel 1960; Craven–Peletier 1972, for 0 ≤ β ≤ 1)".

## 2. Independent computation (mpmath, 40–60 digits; own Taylor-series integrator of order 40, h = 1/16, cross-checked at h = 1/32)
- **Method A, event bisection.** I bisected on the under/over classification itself, starting from [1.2325876568, 1.2325876569]. After 72 steps the bracket is [1.23258765682028102017394729892838815, 1.23258765682028102017394729892840933] (width 2.1e-32).
- **Method B, far-field matching.** I ran a secant method on q(L) = (p(L) - 1)·u'/u at f(L). Here u = e^{-x^2/2} x^{-3} Σ c_k x^{-2k}, with c_k = -c_{k-1}(2k+1)(2k+2)/(2k), is the decaying mode of u'' + x u' - 2u = 0.

  | L | f''(0) |
  |---|---|
  | 6 | 1.23258765682026588… |
  | 8 | 1.232587656820281020173905… |
  | 10 | 1.232587656820281020173947298928392… |
  | 12 | 1.232587656820281020173947298928403… |

- **Result: f''(0) = 1.2325876568202810201739472989284** (31 significant digits; methods A and B agree to about 1e-31).
- Distances to the frozen bounds: α* - 1.2325876568 = 2.03e-11 and 1.2325876569 - α* = 7.97e-11. The true value lies strictly inside, so `hiemenz_exists` is true.
- **α = 1.2325876568 (under-shoot).**
  - q first hits 0 at η = 6.645414369. There p = 1 - 8.32e-10, which is max p on [0,η]. The witness for any η in (6.6454, 7.5] is valid.
  - Values along the trajectory:

    | η | p - 1 | q |
    |---|---|---|
    | 6.75 | -8.39e-10 | -1.29e-10 |
    | 7.5 | -1.03e-9 | -2.93e-10 |

  - Recommended witness: η = 7.5, with margins q = -2.9e-10 and 1 - sup p = 8.3e-10.
  - Event-time margin to 15/2 is 0.85.
- **α = 1.2325876569 (over-shoot).**
  - p first exceeds 1 at η = 5.972944660, where q = 1.53e-8 (q is decreasing up to that point).
  - Values along the trajectory:

    | η | p - 1 | q |
    |---|---|---|
    | 6.5 | +2.87e-9 | 1.62e-9 |
    | 7.5 | +4.04e-9 | 1.15e-9 |

  - min q on [0,7.5] ≈ 1.09e-9, near η ≈ 7.0.
  - Recommended witness: η = 6.5, with margins p - 1 = 2.9e-9 and min q = 1.6e-9.
  - Event-time margin to 15/2 is 1.53.
- **Proof-engineering note.** These margins (about 1e-10 to 1e-9 in p and q, against α offsets of 2e-11 and 8e-11) require a validated integrator: Taylor models or high-order interval Taylor with step control, about 1e-12 absolute accuracy over [0,7.5]. An interval Euler scheme is hopeless at this accuracy. The under case is the tighter one: q margin 2.9e-10.

## 3. Prior art
- **Rigorous enclosure.** None found. Several searches for computer-assisted, interval-arithmetic or verified enclosures of the Falkner–Skan / Hiemenz f''(0) returned nothing relevant, and the one β = 1 paper found says it "do[es] not constitute a formal proof". To my knowledge no published rigorous enclosure exists. A 10-digit formally checked enclosure here would appear to be new.
- **Floating-point values in print** (only what I actually read):
  - Boundary Value Problems 2013:4, Table 1: 1.232588 (Wang; Yacob–Ishak) and 1.2325877 ("present study"), i.e. 7–8 significant digits.
  - An anonymous draft on Falkner–Skan adjoint boundary conditions: 1.2326.
  - The common textbook and Wikipedia-level value is about 1.2326. I found no printed value beyond 8 digits.
  - The module doc's 1.2325876… matches my computation.
- **Existence and uniqueness.**
  - Weyl (1942): existence for every β of a physical solution with positive, monotonically decreasing f''.
  - Coppel 1960, Phil. Trans. R. Soc. A 253, 101–136 (doi 10.1098/rsta.1960.0019). I read only the abstract: "simpler proof of Weyl's result and properties of all solutions".
  - Uniqueness without the 0 < f' < 1 restriction for 0 ≤ β ≤ 1 (Coppel; Craven–Peletier 1972). I took this from Fazio's secondary survey (arXiv 2011.07725 and arXiv 1212.5057). The primary papers were not read.
  - Hartman, *ODEs*, Ch. XIV: not read. Fazio cites Hartman only for IVP well-posedness.
- **Not read:** the Coppel and Craven–Peletier full texts (only scilit metadata); the supplement to arXiv 1907.09912, which has no β = 1 value in its main text; the sanad.iau.ir page, which had no abstract content.

## Sources
- https://scilit.com/publications/02f00eab5c9ba5d704cce460768c735d (Coppel 1960 metadata)
- https://scilit.com/publications/8b315d08d747e27f36716512bcec7211 (Craven–Peletier 1972 metadata)
- https://arxiv.org/pdf/2011.07725 , https://arxiv.org/pdf/1212.5057 (Fazio; existence and uniqueness summary)
- https://arxiv.org/pdf/1907.09912 (Falkner–Skan approximant; no β = 1 value)
- https://boundaryvalueproblems.springeropen.com/articles/10.1186/1687-2770-2013-4/tables/1 (1.232588 / 1.2325877)
- https://idrori.github.io/open/problems/FL/d0-boundary-conditions-falkner-skan/paper/main.pdf (1.2326). Scripts: /tmp/claude-0/referee/
