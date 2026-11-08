# Referee report: Falkner–Skan β = 1/2 in the class −1 ≤ f' ≤ 1 (frozen `FSHalfBounded_frozen.lean`)

Referee run inside run 2026-11-08T1628Z, written 2026-11-08. Frozen file:
`runs/2026-11-08T1628Z/lean/FSHalfBounded_frozen.lean` (three statements, all `sorry`).
Context read: `Checked/FalknerSkan/FSScale.lean`, `Checked/FalknerSkan/Bounded.lean`,
`Checked/FalknerSkan/FalknerSkan.lean`, `runs/2026-11-08T1228Z/lean/FSHalfBounded.lean`.
No Lean was compiled by the referee. No file other than this report was written in the repository.

**Verdict: STANDS-WITH-CORRECTIONS.** The three Lean statements say what their docstrings say,
are non-vacuous and are not trivially true. All corrections are prose (docstrings, novelty
framing); no statement needs to change.

---

## 1. Statement attack

### 1.1 Mechanical comparisons
- `fs_half_bounded_window` and `fs_half_bounded_equal` are textually identical (diff, signature
  through `:= by`) to the compiled scratch proofs in run 1228Z. The scratch proofs use
  `Work.FalknerSkan.Bounded`. Its `homann_bounded_window` / `homann_bounded_equal` statements are
  textually identical to the ones in `Checked.FalknerSkan.Bounded` (diff), so the scratch proofs
  should carry over to the `Checked` import with only the namespace changed.
- `fs_half_exists_bounded` is `Checked.FalknerSkan.Bounded.homann_exists_bounded` with only two
  differences: the ODE line (`-(f η * q η) - 1 / 2 * (1 - p η ^ 2)` instead of
  `-(2 * f η * q η) - 1 + p η ^ 2`) and the window. It is also `Checked.FalknerSkan.fs_half_exists`
  plus the single conjunct `∀ η ∈ Ici 0, 0 ≤ p η ∧ p η < 1`.
- No name clashes: `fs_half_bounded_*`, `fs_half_exists_bounded` and the namespace
  `Checked.FalknerSkan.HalfBounded` do not occur in any other `.lean` file of the checkout.

### 1.2 ODE form
`hq : HasDerivWithinAt q (-(f η * q η) - 1 / 2 * (1 - p η ^ 2))`, with f' = p and p' = q, means
f''' = −f f'' − ½(1 − f'²), i.e. f''' + f f'' + ½(1 − f'²) = 0. That is Falkner–Skan with β = 1/2
in the Hartree normalisation f''' + f f'' + β(1 − f'²) = 0, which is the docstring's equation.
`1 / 2` is real division (= 0.5), not truncating ℕ division, because the expression is typed in ℝ.
In the other common normalisation, f''' + ((m+1)/2) f f'' + m(1 − f'²) = 0, this case is m = β/(2 − β) = 1/3
and the printed wall shear differs by a factor √((m+1)/2). The Lean statement is unambiguous
because it writes the ODE out. See correction P4.

### 1.3 Boundary conditions and quantifiers
- f(0) = 0, p(0) = 0 and `Tendsto p atTop (𝓝 1)` are the standard Falkner–Skan conditions
  f(0) = f'(0) = 0, f'(∞) = 1. There is no condition f''(∞) = 0. That is standard, and it is not needed.
- Window: universally quantified over (f, p, q) satisfying all hypotheses. The conclusion is strict on
  both sides, as the docstring says.
- Equal: universally quantified over two triples. The conclusion is pointwise equality of f, p, q
  on `Ici 0` only, which matches "for every η ≥ 0". Nothing is claimed for η < 0, where the functions are
  unconstrained junk. That is correct scoping.
- Existence: ∃ f p q with the same system, the same boundary conditions, `0 ≤ p η ∧ p η < 1` on `Ici 0`
  (the half-open unit interval, as the module docstring says) and the window.

### 1.4 Class hypotheses
- Window and equal assume `-1 ≤ p η ∧ p η ≤ 1` on `Ici 0`, as the docstring says. The class is
  closed. The upper bound p ≤ 1 cannot be attained under the hypotheses, but that does not create a gap.
  If p(η₀) = 1 with p ≤ 1, then q(η₀) = 0, and IVP uniqueness gives the solution with f' ≡ 1, which
  contradicts p(0) = 0. So the class is effectively −1 ≤ f' < 1. This fact is not needed for the
  statements. It matters only for the literature comparison in §3.
- Existence concludes 0 ≤ p < 1, which lies inside the hypothesis class of the other two. So the
  witness of statement 3 instantiates the hypotheses of statements 1 and 2.

### 1.5 One-sided derivatives, junk values
- `HasDerivWithinAt _ _ (Ici 0) η` at η > 0 is the ordinary two-sided derivative, because `Ici 0` is a
  neighbourhood of η. At η = 0 it is the right derivative, which is the intended meaning at the wall.
- `Ici 0` has unique derivatives at 0, so `q 0` is determined by p (it is the right derivative
  p'(0)). The window therefore constrains the true wall shear, not a junk value. By the same argument
  p is determined by f and q by p on `Ici 0`.
- q is differentiable within `Ici 0`, hence continuous there. So f is effectively C³ on [0, ∞), and no
  pathological solution concepts creep in.
- The numerals `0.927680039` etc. are `OfScientific` literals in ℝ, which are exact rationals. The same
  literals already appear in the checked `fs_half_exists`.

### 1.6 Vacuity and triviality
- Non-vacuous. The hypotheses of the window and equal statements are satisfied by the witness of
  `fs_half_exists_bounded`, since [0, 1) ⊂ [−1, 1]. Independently of that statement:
  1. the checked `fs_half_exists` (from Homann by c = √2) gives a β = 1/2 solution;
  2. my own RK4 shooting finds the β = 1/2 solution with f''(0) ≈ 0.9276800398, and its f' rises
     monotonically to 1.
- Not trivial. The window confines q 0 to a 10⁻⁹ interval around a nonzero number. Equal is a genuine
  uniqueness claim. Existence is the conjunction of a BVP solution, the class and the window. None of
  the conclusions follows from the hypotheses by algebra alone.
- The two hypothesis sets of `fs_half_bounded_equal` are independent copies. No hypothesis ties the
  two triples together, so the statement is not secretly about a single triple.

### 1.7 Docstring accuracy (prose)
- Statement docstrings: accurate, including "one-sided at 0" and "q has derivative −f q − (1 − p²)/2".
- Module docstring: it says the results are obtained "by the similarity scaling … with c the reciprocal
  of the square root of two". That is right for window and equal (Falkner–Skan → Homann). Existence
  goes the other way (Homann → Falkner–Skan), which is `FSScale.scale` with c = √2, as in the checked
  `fs_half_exists`. See correction P1.

---

## 2. Independent derivation

### 2.1 ODE under the scaling
Suppose f solves f''' + f f'' + ½(1 − f'²) = 0 on [0, ∞). Fix c > 0 and set F(s) = c f(s/c) for s ≥ 0.
By the chain rule, with η = s/c:
- F'(s) = f'(η),
- F''(s) = f''(η)/c,
- F'''(s) = f'''(η)/c².
- Hence F F'' = (c f)(f''/c) = f f''.

Substituting:

F''' + 2 F F'' + 1 − F'² = f'''/c² + 2 f f'' + 1 − f'².

With c² = 1/2 the right side is

2 f''' + 2 f f'' + (1 − f'²) = 2 [f''' + f f'' + ½(1 − f'²)] = 0.

So F solves the Homann equation F''' + 2 F F'' + 1 − F'² = 0. This agrees with `FSScale.scale`: the
coefficients (a, b) go to (a/c², b/c²), and (1, ½) with c² = ½ goes to (2, 1).

### 2.2 Boundary data and class
- F(0) = c f(0) = 0.
- F'(0) = f'(0) = 0.
- F'(s) = f'(s/c) → 1 as s → ∞, because s/c → ∞ (`FSScale.scale_lim`).
- s ↦ s/c is a bijection of [0, ∞) onto itself. So {F'(s) : s ≥ 0} = {f'(η) : η ≥ 0}, and the class
  −1 ≤ f' ≤ 1 maps onto −1 ≤ F' ≤ 1. The same holds for 0 ≤ f' < 1.
- Wall shear: F''(0) = f''(0)/c = √2 f''(0).

### 2.3 Window transfer (interval arithmetic)
Rigorous rational bounds: 1.4142135623 < √2 < 1.4142135624. Both are checked by squaring in
`fractions.Fraction`. They are the bounds `lt_sqrt2` and `sqrt2_lt` of FSScale.

The Homann window 1.3119376938 < F''(0) < 1.3119376939 gives, for f''(0) = F''(0)/√2:
- lower: f''(0) > 1.3119376938 / 1.4142135624 = 0.92768003976257…, which exceeds
  0.927680039 by 7.6·10⁻¹⁰;
- upper: f''(0) < 1.3119376939 / 1.4142135623 = 0.92768003989888…, which is below
  0.927680040 by 1.0·10⁻¹⁰.

As cross-multiplied rational checks, which are what `nlinarith` has to find:
0.927680039 × 1.4142135624 < 1.3119376938 and 0.927680040 × 1.4142135623 > 1.3119376939. Both are true.

With Decimal(2).sqrt() at 50 digits the image of the Homann window is
(0.927680039780220…, 0.927680039850931…), which lies strictly inside the frozen window.

Optional (not a correction): the same √2 bounds also prove the 10-digit window
0.9276800397 < f''(0) < 0.9276800399. The margins are 6.3·10⁻¹¹ and 1.1·10⁻¹², so the upper one is
tight but positive. The frozen 9-digit window keeps the number already printed in `fs_half_exists`.

### 2.4 Uniqueness transfer
For two β = 1/2 solutions in the class, both images F₁ and F₂ are Homann solutions in the class. By
`homann_bounded_equal`, F₁ = F₂, F₁' = F₂' and F₁'' = F₂'' on [0, ∞). Evaluate at s = cη, η ≥ 0:
- c f₁(η) = c f₂(η) gives f₁(η) = f₂(η) (cancel c ≠ 0),
- p₁(η) = p₂(η),
- q₁(η)/c = q₂(η)/c gives q₁(η) = q₂(η).

This is exactly the scratch proof's route.

### 2.5 Existence by the inverse scaling
Take the Homann solution of `homann_exists_bounded`, with 0 ≤ F' < 1 and window 1.3119376938 < F''(0) < 1.3119376939.
Set f(η) = √2 F(η/√2), i.e. `FSScale.scale` with c = √2 and (a, b) = (2, 1). The coefficients become
(2/2, 1/2) = (1, ½), which is the β = 1/2 equation. Then:
- f(0) = 0, f'(0) = F'(0) = 0, f' → 1;
- {f'(η)} = {F'(s)} ⊂ [0, 1);
- f''(0) = F''(0)/√2, which lies in the window by §2.3.

The checked `fs_half_exists` already does this except for the class conjunct. That conjunct transfers
pointwise, because p(η) = F'(η/√2) and η/√2 ≥ 0.

### 2.6 Numerical sanity check (not a proof)
I wrote my own RK4 shooting code (h = 10⁻³, L = 8, bisection on whether f' overshoots 1). Results:
- β = 1/2: f''(0) ≈ 0.927680039837;
- Homann: F''(0) ≈ 1.311937693880, and dividing by √2 gives 0.927680039837.

Both values are consistent with the window and with the literature value in §3.

---

## 3. Prior art

### 3.1 Wall shear value
**Belden, Dickman, Weinstein, Archibee, Burroughs, Barlow, "Asymptotic approximant for the Falkner–Skan
boundary-layer equation", arXiv:1907.09912.**
- Read first-hand via arxiv.org/pdf, through WebFetch's summariser, so the digits were read through a
  model, not by eye.
- Normalisation: f''' + f f'' + β(1 − f'²) = 0, f(0) = f'(0) = 0, f'(∞) = 1, m = β/(2 − β). This is
  the same as the frozen file.
- Printed value: κ = f''(0) = 0.927680039836653 for β = 0.5, i.e. 15 significant digits. It appears in
  the captions of Figs. 2 and 3. Method: shooting with RK4, step 10⁻⁴; the authors state convergence to
  the digits reported.
- The same paper prints 0.469599988361 for β = 0, which is consistent with the checked `fs_zero_wall_shear` window.
- The printed β = 1/2 value lies inside the frozen window (checked with exact fractions) and agrees with
  my shooting to about 13 digits. The formal window is therefore 9-digit agreement with a 15-digit
  published value, and novel only as a certified enclosure.
- Classical tables (e.g. White, Viscous Fluid Flow) print about 0.92768. That is from memory and was
  not read in this run.

### 3.2 Uniqueness for β = 1/2
- **Restricted class 0 < f' < 1, β > 0.** Uniqueness is classical. The attributions vary by source:
  - Hartman, *Ordinary Differential Equations* (1964), per Veldman & van de Vooren 1980;
  - Hartree 1937 / Stewartson 1954, per Fazio 2020;
  - Iglisch 1954 and Craven & Peletier 1972, per a Caltech annotated bibliography.

  All of this is second-hand.
- **Unrestricted (the class condition dropped) for 0 ≤ β ≤ 1 (or β < 1).** Two independent secondary
  sources state that Coppel (1960) and Craven & Peletier (1972) proved the restriction 0 < f' < 1 can
  be omitted:
  - Veldman & van de Vooren, "On a generalized Falkner–Skan equation", J. Math. Anal. Appl. 75 (1980)
    102–111 (core.ac.uk PDF, read first-hand through the summariser): "Coppel [1] and Craven and
    Peletier [2] have proved that this restriction can be omitted when λ < 1", with λ playing the role of β.
  - R. Fazio, "Existence and uniqueness of BVPs defined on semi-infinite intervals: insight from the
    iterative transformation method", arXiv:2011.07725 (arxiv.org/pdf, read first-hand through the
    summariser): Coppel and Craven–Peletier "pointed out that the above restriction on the first
    derivative can be omitted when 0 ≤ β ≤ 1".
  - Primary sources:
    - W. A. Coppel, Phil. Trans. R. Soc. A 253 (1960) 101–136: not read.
    - A. H. Craven & L. A. Peletier, Mathematika 19 (1972) 129–133, doi:10.1112/S0025579300005052:
      not read. The Cambridge abstract page was blocked (permission request timed out) and was not
      retried by other means. scilit shows no abstract.

  So the unrestricted claim is second-hand only, and its exact hypotheses are unverified by me. In
  particular I could not check whether the class is "f'(∞) = 1, no further condition" or something
  like f' bounded.
- **β > 1 is different:** reverse-flow solutions (Craven & Peletier 1972b) and solutions with many
  oscillations (Hastings & Troy, J. Differential Equations 1988, zbMATH review read via the MaRDI
  portal) exist. β = 1/2 is outside that range.
- **Is uniqueness in −1 ≤ f' ≤ 1 already implied by published results?** Yes, on the second-hand
  reports above. Unrestricted uniqueness at β = 1/2 (0 ≤ β ≤ 1) implies uniqueness in any subclass.
  Even the weaker "f' < 1" uniqueness would cover the frozen class, since −1 ≤ f' ≤ 1 forces f' < 1
  (§1.4). Hartman's restricted 0 < f' < 1 result does not by itself cover the class. Bridging it needs
  exactly the "|f'| ≤ 1 ⇒ f' > 0" step that the repository proves as `BoundedTools.pos_of_abs_le`.
- **Conclusion.** The mathematical content of all three statements is classical. The novelty is the
  machine-checked proof and the certified 9-digit enclosure, not the theorem. The Lean uniqueness
  result is weaker than the published one: it assumes −1 ≤ f' ≤ 1, while the literature removes the
  restriction for 0 ≤ β ≤ 1.
- Homann (axisymmetric stagnation) ↔ Falkner–Skan β = 1/2 is the classical Mangler-type
  correspondence. Fazio 2020 also mentions "β = 1/2 (Homann flow)".

### 3.3 Sources and how they were read
| Source | How read |
|---|---|
| Belden et al., arXiv:1907.09912 | first-hand (arxiv.org/pdf, WebFetch summariser) |
| Fazio, arXiv:2011.07725 | first-hand for its own statements; second-hand for Coppel / Craven–Peletier / Hartree / Stewartson |
| Veldman & van de Vooren, JMAA 75 (1980), core.ac.uk/download/232385502.pdf | first-hand for its own statements; second-hand for Coppel / Craven–Peletier / Hartman |
| Caltech annotated bibliography (authors.library.caltech.edu …/Chapter_4.pdf) | first-hand, low weight (annotations only) |
| Hastings & Troy, JDE 1988 | second-hand (zbMATH review via MaRDI portal) |
| Lan & Yang, Canad. Math. Bull. 51 (2008) | abstract page only; no uniqueness content |
| Brighi & Hoernel, arXiv:math/0601332 | first-hand; not relevant (other equation) |
| Coppel 1960; Craven & Peletier 1972 (both papers); Hartman 1964 book | **not read** (Craven–Peletier Cambridge page blocked/timed out; not retried) |

---

## 4. Verdict: STANDS-WITH-CORRECTIONS

The statements are correct as frozen: right ODE (β = 1/2, Hartree normalisation), right boundary
conditions, right quantifiers and scoping to [0, ∞), correct one-sided handling at 0, no junk-value
loophole, non-vacuous, not trivial. The window follows from the Homann window with explicit √2 bounds
(margins 7.6·10⁻¹⁰ and 1.0·10⁻¹⁰) and contains the published 15-digit value 0.927680039836653.
**No statement correction.**

Prose corrections:
- **P1 (module docstring of the frozen file).** "with c the reciprocal of the square root of two"
  applies to window and equal (Falkner–Skan → Homann). Existence uses the inverse scaling, c = √2
  (Homann → Falkner–Skan), as in `fs_half_exists`. Suggested wording: "… by the similarity scaling of
  `FSScale` with c = 1/√2 (window, uniqueness) and its inverse c = √2 (existence)."
- **P2 (novelty framing in any README, CHANGELOG or paper text).** Do not present β = 1/2
  uniqueness as new.
  - Restricted uniqueness (0 < f' < 1, β > 0) is classical.
  - Coppel 1960 and Craven & Peletier 1972 are reported (second-hand: Veldman–van de Vooren 1980;
    Fazio 2020) to have removed the restriction for 0 ≤ β ≤ 1.
  - The −1 ≤ f' ≤ 1 hypothesis is a formalisation scope choice, so the formal result is weaker than
    the literature. State this explicitly.
  - The window is a certified 9-digit enclosure of a value published to 15 digits (Belden et al., arXiv:1907.09912).
- **P3 (stale note, after promotion).** The module docstring of `Checked/FalknerSkan/FalknerSkan.lean`
  says "uniqueness of the half-β solution is not formalised". Once these statements are promoted,
  qualify it as "not formalised outside the class −1 ≤ f' ≤ 1 (see `HalfBounded`)". (Not edited by the referee.)
- **P4 (normalisation).** Wherever the value is quoted without the ODE, name the normalisation:
  f''' + f f'' + β(1 − f'²) = 0, β = 1/2, equivalently m = 1/3. In the m-normalisation the printed
  number would differ by a factor √(2/3).

Optional, not required: the existing √2 bounds also prove the 10-digit window
0.9276800397 < f''(0) < 0.9276800399 (upper margin 1.1·10⁻¹²).

Process notes:
- Scripts and outputs are in the session scratchpad, outside the repository:
  - `/tmp/claude-0/-home-claude-formalization/ec101f05-8d20-5e50-ba02-b884dc42fd1b/scratchpad/scripts/interval.py`
  - `/tmp/claude-0/-home-claude-formalization/ec101f05-8d20-5e50-ba02-b884dc42fd1b/scratchpad/scripts/shoot.py`
- No PDFs were downloaded; all web reading went through WebSearch/WebFetch.
- arXiv was read only via arxiv.org/pdf. The one www.arxiv.org/pdf fetch was a search-result URL of the same host.
