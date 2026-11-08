# Referee report: bounded-class headlines (run 2026-11-08T1228Z)

VERDICT: STANDS-WITH-CORRECTIONS. The six Lean statements say what their docstrings say, are non-vacuous, and the
mathematics behind the new helper lemmas is correct. The corrections are to the prose: the README attributes the
class to the wrong author and calls a question "open" that the literature (secondary sources) treats as settled for Homann.

## 1. Statement attack (Headlines.part): verdict OK
- Equations: Hiemenz `q' = -(f q) - 1 + p^2` is f''' + f f'' + 1 - f'^2 = 0. Homann `q' = -(2 f q) - 1 + p^2` is
  f''' + 2 f f'' + 1 - f'^2 = 0. Both match their docstrings. Homann is Falkner-Skan with beta = 1/2: put f(eta) = g(sqrt2 eta)/sqrt2.
  This gives g''' + g g'' + (1/2)(1 - g'^2) = 0 and g''(0) = 1.31194/sqrt2 = 0.9277, which matches the classical beta = 1/2 value (recalled).
- Quantifiers and junk values: the hypotheses are universal over f, p, q : R -> R and constrain only [0, inf). The limit uses atTop and the
  conclusions are on [0, inf). There is no division and no junk value. The derivatives are HasDerivWithinAt on Ici 0, which is a two-sided
  derivative at eta > 0 (Ici 0 is a neighbourhood there) and one-sided at 0. The docstrings say "one-sided at 0". OK.
- Strength: given p(0) = 0 and p -> 1, the old class "q > 0" lies inside 0 <= p < 1 (`bounded_of_pos`), and that lies inside -1 <= p <= 1. So the hypothesis
  is strictly weaker and the window and uniqueness theorems are strictly stronger than the frozen q > 0 versions. Nothing is trivially true:
  the window is a 1e-10 interval, and uniqueness excludes, for example, reverse-flow profiles with -1 <= f' < 0 somewhere.
- Non-vacuity: `*_exists_bounded` gives a witness with 0 <= p < 1, which satisfies `hb`, so the window theorems have a non-empty class.
  Uniqueness is meaningful, not vacuous: it applies to that witness and to any other candidate.
- Docstrings, word by word: the window, unique and exists docstrings match the Lean exactly. That covers "-1 <= p <= 1 on [0, inf)",
  "0 <= p < 1", "equal on [0, inf): same f, same p = f', same q = f''", and the strict decimal bounds. Minor point:
  `pos_of_abs_le`'s docstring omits that the lemma holds for every real k and needs the ODE. Acceptable for a helper.
- Naturalness: |f'| <= 1 means the speed never exceeds the free-stream speed, |u| <= U_e. Reverse flow is allowed, but faster than U_e is not.
  The condition "|f'| <= 1 everywhere" does occur in the literature (Stewartson 1954, via the Caltech annotated bibliography; not read in the original).
  The classical uniqueness class is 0 < f' < 1 for eta > 0 (Hartman's book, per Veldman-van de Vooren 1980; Iglisch).
  -1 <= f' <= 1 is a genuine widening of it. It is NOT "Coppel's class"; see Corrections.

## 2. Independent derivation: verdict CORRECT
(a) -1 < p < 1 and p -> 1 imply q > 0 on [0, inf), for every real k. At a zero of q, q' = -k f*0 - 1 + p^2 = p^2 - 1 < 0, so k
  drops out and its sign is irrelevant. Suppose q(eta0) <= 0. A zero of q can only be crossed downward. This is the fencing step:
  q <= B = 0, and the strict inequality q' < B' = 0 holds wherever q = B. Mathlib's `image_le_of_deriv_right_lt_deriv_boundary'` with right derivatives on Ico
  matches this, so q <= 0 on [eta0, inf). Then p is non-increasing, so p <= p(eta0) < 1 on [eta0, inf). Since p -> 1, eventually p > p(eta0),
  a contradiction. The argument uses |p| < 1 at every later zero of q, not just at eta0, and the hypothesis supplies this on all of [0, inf). f(0) and p(0) are not used. OK.
(b) p(0) = 0 and -1 <= p <= 1 imply -1 < p < 1. Suppose p(eta1) = +1 or -1 with eta1 > 0 (eta1 = 0 is excluded by p(0) = 0). Then eta1 is an interior maximum or minimum of p,
  which is differentiable there, so q(eta1) = 0. The lines Z(eta) = (c + s(eta - eta1), s, 0) with s = +1 or -1 and c = f(eta1) solve the system for EVERY k:
  f' = s = p, p' = 0 = q, and q' = 0 = -k f*0 - 1 + s^2 = 0 (checked symbolically, and against `start_of_touch`, where fsV k (Z t) reduces to (s, 0, 0) via s^2 = 1).
  The two solutions agree at eta1. The field (f,p,q) -> (p, q, -k f q - 1 + p^2) is polynomial, hence Lipschitz on compact sets. Backward uniqueness on
  [0, eta1] then gives p(0) = s, which contradicts p(0) = 0. In `uniq_left`, the left derivatives on Ioc 0 eta1 come from two-sided derivatives at interior points. OK.
(c) Equal (f,p,q)(0) give equal solutions on [0, inf). This is forward Gronwall/Picard uniqueness on each [0, eta], with the Lipschitz constant taken on the compact union
  of the two trajectory images (`ODE_solution_unique_of_mem_Icc_right`, right derivatives on Ico, continuity on Icc). OK.
  Combined with the frozen same-wall-shear theorems, (a)+(b)+(c) give the unique and window headlines exactly as written.

## 3. The previous referee's equivalence (referee_mw.md section 1): the GAP IS REAL; the claim is unproved, with numerical evidence for it
- Gap: "once q < 0, p decreases, p < 1 stays, so q' < 0 at every later zero" fails at zeros where p <= -1, because there q' = p^2 - 1 >= 0.
  A zero at p = -1 exactly is ruled out by (b), so the remaining case is p < -1. The side remark "q(0) <= 0 impossible (q'(0) = -1)" does not prove anything either:
  q'(0) = -1 only shows that q becomes negative. The audit (README) is right.
- Reduction: if p < 1 everywhere, p -> 1, and q is not positive everywhere, then q has a LAST zero eta2. There q goes from <= 0 to > 0, so
  p(eta2) < -1. After eta2, p rises monotonically from below -1 to 1 without reaching it. A counterexample is therefore a trajectory from (0,0,s)
  that "turns" below -1 and then creeps up to 1 from below.
- Numerics (scripts in /tmp/claude-0/referee_scratch/: shoot.py, scan*.py, fate.py, chk*.py, turnmap.py, locus.py; scipy DOP853/LSODA/Radau,
  rtol 1e-11 to 1e-12). Shooting over s = q(0) for both k:
  * k = 1, s in [-200, s* - 1e-8] (about 6200 values, 3 solvers spot-checked at 8 values, all agree): every s < s* gives exactly one
    turn below -1, followed by p crossing 1 ("TO"). During the rise, q stays >= 0.087 on p in [-0.9, 0.9] (for s <= s* - 1e-3), far from a second zero.
    As s -> s*, the turn approaches (f,p) = (0,-1) (for example s* - 1e-6: turn at f = -2.6e-6, p = -1 - O(1e-6), eta = 2170). This is the linear regime around
    the line p = -1 (hence a fixed scaled linear profile), and the outcome is still a crossing of 1. If s > s*, p crosses 1 before q vanishes. No s other than s* gives p < 1 and p -> 1.
  * k = 2: every s < ~1.18 blows up (p -> -inf in finite eta) with q < 0 after the first zero, so p decreases and there is no counterexample. For s in (1.18, s*), the descent
    follows an EXACT unstable invariant family that exists only for k = 2: q = -c, p = B - c*eta, f = (1 - p^2)/(2c) (verified: q' = 0 = (1 - p^2) - 1 + p^2).
    The trajectory leaves it near f of about -7.5 and p of about -1.9, either by blow-up or by a turn followed by an explosive crossing of 1 (q of about 30 to 50 at p = 1).
    WHICH of the two happens depends on the solver (round-off amplified by the unstable family), so the k=2 fate map is not trustworthy pointwise. But NEITHER outcome
    is a counterexample. A boundary point between the two cannot turn (turning is an open condition), so after its first zero q < 0 forever and p decreases. No "turn then q = 0 with |p| < 1"
    pattern was ever seen for k = 2.
- Strength of evidence: moderate. The numerics are floating-point and uncertified. The grid would miss windows narrower than about 0.008 in s (1e-3 near s*), and the k=2 long-time fate is
  ill-conditioned. The structural arguments (reduction to a last turn; boundary points between O and B cannot turn) are rigorous.
  Status: for k = 1 and k = 2, "p < 1 alone implies q > 0" is UNPROVED in this repo, numerically supported, and probably implied by the classical unrestricted-uniqueness results in section 4
  (if the unique BVP solution is the monotone one, any p<1 solution is it). Do not use it in a statement. "Open" is right only as "open here".

## 4. Prior art
- READ (WebFetch summary plus targeted verbatim quotes, introduction only): Veldman & van de Vooren, "On a generalized Falkner-Skan equation", JMAA 75 (1980)
  102-111 (core.ac.uk/download/232385502.pdf). Quotes: "case A possesses a unique solution under the additional requirement 0 < y' < 1 for x > 0 (see
  for instance the book of Hartman [4])" and "Coppel [1] and Craven and Peletier [2] have proved that this restriction can be omitted when [lambda] < 1".
  The OCR renders lambda as "h", and whether the inequality is < or <= is uncertain from the OCR. [1] is Coppel, Phil. Trans. R. Soc. A 253 (1960) 101-136; [2] is Craven & Peletier, Mathematika 19 (1972) 129-133.
- READ (WebFetch summary of the introduction): Fazio, arXiv 2011.07725. It credits Hartree/Stewartson with uniqueness for beta > 0 under the "normal flow" condition 0 < f' < 1, and says the restriction
  "can be omitted when 0 <= beta <= 1" (Coppel; Craven & Peletier).
- READ (WebFetch summary of an annotated bibliography): Caltech thesis Chapter 4 (authors.library.caltech.edu, 57fsb-47g85). It annotates Craven & Peletier 1972a as "solution with
  0 < f' < 1 is unique for 0 < beta < 1" (this summary conflicts with the two sources above) and Craven & Peletier 1972b (reverse flow for lambda > 1) as "not beta = 1". It lists Iglisch: unique if no reverse flow and 0 < f' < 1.
- READ (abstract only, irrelevant): Brauner-Laine-Nicolaenko, Mathematika 29 (1982), beta = -1.
- NOT READ: Coppel 1960 and Craven & Peletier 1972 in the original (the scilit pages were challenge pages); Hartman, ODE, ch. XIV; Tam 1970 (Canad. Math. Bull.;
  the Cambridge PDF fetch got no permission answer in time, not retried); McLeod (not located).
- Conclusion (from secondary sources only): uniqueness WITHOUT any restriction on f' is classical (Coppel 1960; Craven-Peletier 1972) for beta < 1, so Homann
  (beta = 1/2) is covered. For Hiemenz (beta = 1, the endpoint), two secondary sources say <= 1 and one OCR'd source says < 1, so it is unresolved here.
  I found no statement of "unique in -1 <= f' <= 1" as such. For Homann it is a corollary of the classical unrestricted result, so the mathematical
  content of the new theorems is NOT new. What is new is a machine-checked proof plus the certified 1e-10 window. Hiemenz should be described with the
  same caution until Coppel or Craven-Peletier has been read.

## Corrections required (prose only; the Lean statements may be frozen as they are)
1. README "THE RESULT" calls -1 <= f' <= 1 "Coppel's physical class". That is wrong. The classical restricted class is 0 < f' < 1 (Hartman/Iglisch), and Coppel's
   contribution (with Craven-Peletier) is removing the restriction for beta < 1 (or <= 1). Rephrase as "a class that contains the classical 0 < f' < 1".
2. README "Whether f' < 1 alone suffices is open": say "not proved here; numerically supported (k = 1, 2); implied by classical unrestricted
   uniqueness for beta < 1 (Homann) if that is confirmed from the primary source".
3. Any headline or README prose must not present uniqueness in |f'| <= 1 as stronger than the literature. It is weaker than the classical result for Homann.
4. Optional: in the bottleneck paragraph, cite the class as "0 < f' < 1 (Hartman ch. XIV; Iglisch)" rather than "(Coppel 1960)".
