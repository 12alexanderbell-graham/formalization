VERDICT: STANDS

# Referee report: `Work.Math.ThomasFermi.tf_initial_slope`

Repo HEAD at review: 67f4410337f1fbd98a3197e94a1b06092209be03 (the FREEZE commit). Only `Work/Math/ThomasFermi.lean` was read.
Scratch: /tmp/tf_ref/ (shoot.py, Check.lean, run1-4.log, dl/abf.pdf, dl/abf.txt).

## 1. Truth: independent value of B = y'(0)

Method. In t = sqrt(x), with p = dy/dx, the problem becomes the *nonsingular* analytic system
  dy/dt = 2 t p,  dp/dt = 2 y^{3/2},  y(0) = 1, p(0) = B
(the 1/sqrt(x) cancels against dx = 2t dt). I integrated it with a Taylor-series method
(order N, y^{3/2} via the recurrence u' y = (3/2) u y', step 0.25 x estimated radius) in mpmath,
and bisected on B starting from [-1.6, -1.5]: "y reaches 0" => B too low, "p reaches 0 with y > 0" => B too high.
A step-size collapse below 1e-15 (convergence onto the branch point y = 0) is classified as "y reaches 0".

| run | dps | order N | t_max (x_max) | bracket for B after bisection |
|---|---|---|---|---|
| 1 | 34 | 30 | 60 (3600) | [-1.58807102261137531188650, -1.58807102261137531188582] (truncation-limited at digit 19) |
| 2 | 44 | 48 | 60 (3600) | [-1.588071022611375312719303, -1.588071022611375312717948] |
| 4 | 50 | 56 | 100 (10^4) | [-1.5880710226113753127186847071, -1.5880710226113753127186843762] |
| 3 | 60 | 70 | 150 (22500) | [-1.5880710226113753127186845096277, -1.5880710226113753127186845093045] |

Runs 2-4 are nested and consistent; run 3 gives

  **B = -1.58807102261137531271868450946...** (about 28 significant digits; floating point, not certified).

Run 1 (low order) drifts at the 19th digit, which shows truncation error is the limiting factor and that runs 2-4 have it under control.

Margins to the interval [-1.58807103, -1.58807102]:
- distance to lower end: B - (-1.58807103) = 7.388624687281e-9
- distance to upper end: -1.58807102 - B = 2.611375312719e-9
Both are ~10^19 times larger than the numerical uncertainty. The claim is true.

Shooting characterisation. For the IVP y(0)=1, y'(0)=b: if b < B, y has a finite zero (beyond it y^{3/2} is undefined;
physically the "ionised ion" solutions); if b > B, y' vanishes at some finite x0 while y > 0, after which y is convex and
increasing and blows up at finite x; b = B is the unique solution decaying to 0 (y ~ 144/x^3, Sommerfeld). The sets of b
giving each behaviour are open and disjoint (continuous dependence), so they meet at exactly one point B, which gives
existence. Monotonicity in b (comparison: y_b is increasing in b while both are positive) gives uniqueness.
Classical sources (from my background knowledge; I did not open them during this review, except that the Hille 1970 metadata was confirmed on MaRDI):
A. Mambriani, Rend. Accad. Lincei (6) 9 (1929) 620-622 (existence/uniqueness);
G. Sansone, *Equazioni differenziali nel campo reale*, vol. II (1949);
E. Hille, "On the Thomas-Fermi equation", PNAS 62 (1969) 7-10;
E. Hille, "Some aspects of the Thomas-Fermi equation", J. Analyse Math. 23 (1970) 147-170, doi:10.1007/BF02795497
(metadata confirmed on portal.mardi4nfdi.de, Publication:2543392);
C. A. Coulson and N. H. March, Proc. Phys. Soc. A 63 (1950) 367 (the three solution classes).

## 2. Fidelity of the Lean encoding

Elaboration. `lake build Work.Math.ThomasFermi` (needed to produce the .olean; build artifact only) and then
`lake env lean /tmp/tf_ref/Check.lean`. Result: clean. `#check` prints
`∀ (y φ : ℝ → ℝ), (∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x) → (∀ x, 0 < x → HasDerivAt φ (y x ^ (3 / 2) / √x) x) →
ContinuousWithinAt φ (Ici 0) 0 → y 0 = 1 → (∀ x, 0 ≤ x → 0 < y x) → Tendsto y atTop (𝓝 0) → -1.58807103 ≤ φ 0 ∧ φ 0 ≤ -1.58807102`.
Axioms: propext, sorryAx, Classical.choice, Quot.sound (sorryAx only from the pending proof).

Hypothesis by hypothesis:
- Decimal literals: `norm_num` proves `(-1.58807103 : ℝ) = -(158807103/10^8 : ℚ)` and likewise for -1.58807102. These are exact rationals, not floats.
  `-1.58807103 ≤ φ 0` parses as `(-(1.58807103)) ≤ φ 0`, as intended.
- `y x ^ ((3:ℝ)/2)` is `Real.rpow`; the exponent is the real 3/2, not ℕ-division (which would give 1). For y x > 0 it is exp((3/2) log y), the intended y^{3/2}.
  Junk: for y < 0, Mathlib's rpow is exp(log|y|·3/2)·cos(3π/2) = 0 (I checked the `rpow_def_of_neg` unfolding).
  This never matters because `hpos` forces y > 0 on [0, ∞) and `hφ` is only used at x > 0.
- `Real.sqrt x` for x > 0 is > 0 (checked), so the division is genuine; the junk values x/0 = 0 and sqrt(neg) = 0 are never reached.
- `HasDerivWithinAt y (φ x) (Ici 0) x` for x ≥ 0: at x > 0, Ici 0 is a neighbourhood, so this is the two-sided derivative. At 0 it is the right derivative, which is the intended meaning of y'(0).
  It also gives continuity of y on [0, ∞).
- `HasDerivAt φ (…) x` for x > 0 is the ODE y'' = y^{3/2}/sqrt(x) on (0, ∞).
- `Tendsto y atTop (𝓝 0)` is the boundary condition at infinity. `y 0 = 1` is the boundary condition at 0.
- Values of y and φ on x < 0 are unconstrained and never used in the hypotheses at x ≥ 0 (within-Ici derivatives), so they are harmless.

Can an unintended function satisfy the hypotheses? No. Any two admissible y1, y2 coincide on [0, ∞), by a maximum principle.
Let d = y1 - y2. It is continuous on [0, ∞) with d(0) = 0 and d → 0, and twice differentiable on (0, ∞) with
d'' = (y1^{3/2} - y2^{3/2})/sqrt(x), which has the sign of d. If d > 0 somewhere, then d has a positive maximum at some x0 > 0,
where d'' ≤ 0, but d''(x0) > 0. Contradiction; symmetrically for d < 0.
So d ≡ 0 on [0, ∞), and φ1(0) = φ2(0) because both are the right derivative of the same function. The conclusion is therefore about the TF solution's slope only.

Satisfiable? Yes. The classical TF solution (Mambriani 1929, Hille 1969/70) is analytic in t = sqrt(x) near 0:
y = 1 + Bx + (4/3)x^{3/2} + …. Extend y to x < 0 by, e.g., 1 + Bx and set φ := y' on (0, ∞), φ(0) := B. Then all six hypotheses hold.
The hypothesis set is consistent, so the theorem is not vacuous.

Redundancy / strength:
- `hφ0` (continuity of φ at 0 from the right) is **redundant**. By `hφ`, φ is increasing on (0, ∞) (φ' > 0), so φ(0+) exists in [-∞, ∞).
  By the mean value theorem on [0, h], (y(h) - 1)/h = φ(ξ_h) with ξ_h ∈ (0, h). The left side → φ(0) and the right side → φ(0+), so φ(0+) = φ(0).
  It is harmless, because it is implied, so it does not shrink the class. The prover may simply use it.
- `hpos` (y > 0 on [0, ∞)) is needed for rpow to mean y^{3/2} and is true of the TF solution, so it is not too strong.
  (Even without it, y < 0 would give y'' = 0 in Lean's junk semantics, which is a different problem; keeping it is right.)
- Nothing is too strong; nothing is missing.

Near misses. The interval has width 1e-8 and B sits 2.61e-9 from the upper end and 7.39e-9 from the lower end.
- Narrowing the upper end to -1.588071023 makes the statement false.
- Shifting the window by one unit in the 8th decimal, e.g. [-1.58807102, -1.58807101] or [-1.58807104, -1.58807103], also makes it false.
- [-1.588071023, -1.588071022] and [-1.5880710227, -1.5880710226] would still be true.
- The digits 0.0000000026 to the upper end are a comfortable margin for an interval-ODE proof but not lavish: the certified tube must be accurate to about 2e-9 in B.

## 3. Prior art: rigorous enclosure in print?

None found. Searches (WebSearch, standard plus extended) for computer-assisted / interval / validated enclosures of the TF initial slope returned only floating-point or series/Padé work.
- Amore-Boyd-Fernández (arXiv:1205.1704v2, read from the arxiv.org/pdf copy in /tmp/tf_ref/dl/) state no formal error bound.
  The PHM value "was estimated from sequences of roots of the Hankel determinants". The check is Mathematica NDSolve with WorkingPrecision up to 1000,
  after which "we are confident that all the digits in those tables are exact". This is heuristic, not a proof.
- Their Table 1 lists earlier values (quoted exactly):
  - Ref. [3] Kobayashi et al., J. Phys. Soc. Japan 10 (1955) 759: "-1.588071"
  - Ref. [5] Torrens 1972: "-1.5880710"
  - Ref. [22] Fernández, Appl. Math. Comput. 207 (2011): "-1.588071022611375313"
  - Ref. [23] Abbasbandy-Bervillier, Appl. Math. Comput. 218 (2011) 2178: "-1.5880710226113753127189±7 × 10−22" (an estimated, not certified, error)
  - Ref. [24] Boyd, JCAM 2012: "-1.5880710226113753127186845"
- R. Iacono, "An exact result for the Thomas-Fermi equation: a priori bounds for the potential slope at the origin",
  J. Phys. A 41 (2008) 455204, doi:10.1088/1751-8113/41/45/455204. This gives *rigorous a priori* bounds from integral identities.
  I could not retrieve its numbers (abstract only, via sostenibilita.enea.it/pubs/5725). From the abstract these are analytic bounds, almost certainly far coarser than 1e-8.
  The prover should check it before claiming novelty of *any* rigorous bound; a 1e-8 rigorous enclosure still appears to be new.
- Blocked or unavailable: arxiv.org/abs/1205.1704 and oeis.org/A231786 (WebFetch permission request not answered; not retried or worked around);
  ui.adsabs.harvard.edu (robots), sciencedirect.com (client error), pmc.ncbi.nlm.nih.gov (captcha).

## 4. Consistency with Amore-Boyd-Fernández and OEIS A231786

ABF print (arXiv:1205.1704v2, p. 7, and Table 1 "Present (PHM)"), exactly:
  "u′ (0) = −1.588071022611375312718684508"
Their integration value (Table 1 "Present (integration)") is "-1.588071022611375312718684".
For the sensitivity test they also used "u′L (0) = −1.588071022611375312718684509" and "u′R (0) = −1.588071022611375312718684507".

- −1.58807103 ≤ −1.588071022611375312718684508 ≤ −1.58807102: **consistent**, with the margins in Section 1.
- My run 3 agrees with ABF through 26 decimals. At the 27th decimal my bracket gives …684509(46), i.e. it rounds to …509 rather than the printed …508.
  This is a last-digit discrepancy of about 1.5e-27, within ABF's own L/R bracket, and irrelevant for this statement.
- OEIS A231786: the page could not be fetched (permission not granted), so its digits are **not verified** here.
  The search engine lists it as the TF initial-slope constant. Flag: if A231786 is cited in the proof file, someone must quote it from the page itself.

## Summary for the prover
- The statement is true with margins of 2.6e-9 (upper) and 7.4e-9 (lower). The encoding is faithful, has no junk-value loophole, and is satisfiable; `hφ0` is redundant but harmless.
- The t = sqrt(x) substitution gives the polynomial-like analytic system dy/dt = 2tp, dp/dt = 2y^{3/2}, which is convenient for the planned tubes.
- Endpoint shots (/tmp/tf_ref/ends.py, dps 40): with b = -1.58807103, y reaches 0 at x ≈ 51.3; with b = -1.58807102, y' reaches 0 (y > 0) at x ≈ 54.1.
  So the two certificates need validated integration only to x ≈ 55 (t ≈ 7.4), followed by a rigorous comparison argument (b < B iff y hits 0; b > B iff y' hits 0).
