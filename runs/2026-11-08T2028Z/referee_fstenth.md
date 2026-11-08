# Referee: Work/FalknerSkan/TenthBounded.lean (FS beta = 1/10, class -1 <= f' <= 1)

VERDICT: STANDS

## 1. Statement attack (files read: TenthBounded.lean, FSScale.lean only)
- ODE: f'=p, p'=q, q' = -(f q) - 1/10 (1 - p^2) is exactly f''' + f f'' + beta(1 - f'^2) = 0 with beta = 1/10.
  The literal `1 / 10` is real division (f eta : R forces R); no Nat-division trap. Sign of the beta term correct.
- Decimal literals 0.5870352191 etc. are exact rationals (OfScientific on R); strict inequalities.
- Derivatives: HasDerivWithinAt ... (Ici 0) at every eta >= 0, so one-sided at 0 and two-sided inside; no
  hypotheses about eta < 0, so junk values off [0,inf) are unconstrained and irrelevant. All conclusions are
  restricted to Ici 0 (equal theorem concludes only for eta in Ici 0, correct).
- BCs: f 0 = 0, p 0 = 0, Tendsto p atTop (nhds 1): faithful. q->0 not assumed (follows from the ODE; assuming
  less is stronger, fine).
- Class: hb (-1 <= p <= 1 on [0,inf)) is a hypothesis for window/equal. It is weaker than the classical normal-flow
  class 0<p<1, and the literature (Coppel; Craven-Peletier) says the restriction can be dropped for 0<=beta<=1, so
  the hypothesis is not suspiciously strong. Not vacuous: fs_tenth_exists_bounded gives an explicit member
  (0 <= p < 1 implies -1 <= p <= 1), and my numerics confirm a solution exists. Existence class 0<=p<1 on [0,inf)
  with p 0 = 0 is consistent (p(0)=0 allowed by non-strict 0 <=). No gap between existence class and uniqueness
  class (existence class is a subclass), so window+equal+exists together give: unique in the larger class.
- Existence theorem has no extra free parameters; window conclusion for the same witness; no way to satisfy it
  trivially (p->1 and f(0)=p(0)=0 force a genuine FS profile).
- Scaling: to_k10 uses c = 1/sqrt 10; scale gives a/c^2 = 10, b/c^2 = (1/10)*10 = 1 (hc2 : c^2 = 1/10 consistent).
  In exists, scale with c = sqrt 10 from (10,1) gives (1, 1/10), correct direction. q(0)/c = sqrt10 q(0) used
  correctly (hq0), and the two nlinarith transfers use sqrt10_lt / lt_sqrt10 in the right directions
  (lower bound uses the upper bound of sqrt10 on q0 > 1.8563683593/sqrt10, etc.). Dependence on
  Work.FSTenth.F10Bounded is sorry-free-pending (the three k10_* statements are not visible here; not read, per
  instructions); I cannot judge their exact form beyond the call shapes, which are type-consistent with
  F''' + 10 F F'' + 1 - F'^2 = 0.
- Minor remarks (no correction needed): the docstring says "wedge exponent m = 1/19" (beta = 2m/(m+1) = 1/10
  gives m = 1/19: correct). Window width 2e-10 is non-trivially tight but contains the true value with margin
  about 9.8e-11 below and 1.0e-10 above.

## 2. Independent computation (scratch: /tmp/claude-0/ref/s.py, mpmath 40 digits, order-45 Taylor, step 1/20)
Shooting on a = f''(0) with exact event logic: "over" = first time p > 1 (with q>0); "under" = first time q < 0
with p < 1; bisection to 1e-16, no undecided cases.
- beta = 1/10, f''' + f f'' + (1-f'^2)/10 = 0:  f''(0) in [0.58703521919769752, 0.58703521919769761]
  => 0.5870352191977 (13 digits). Strictly inside (0.5870352191, 0.5870352193). OK.
- Scaled problem F''' + 10 F F'' + 1 - F'^2 = 0: F''(0) in [1.85636835940092680, 1.85636835940092688]
  => 1.8563683594009; strictly inside (1.8563683593, 1.8563683595). OK.
- sqrt10 = 3.16227766016837933...; F''(0)/sqrt10 = 0.58703521919769759 (matches f''(0)); sqrt10 * f''(0)
  = 1.85636835940092660 (matches F''(0)). Scaling F(s) = c f(s/c), F' = p, F'' = q/c,
  F''' = q'/c^2 = -10 F F'' - (1 - F'^2) verified by hand (f = F/c, q = c F'').
- 1.8563683593/3.1622776602 > 0.5870352191: True. 1.8563683595/3.1622776601 < 0.5870352193: True.
  3.1622776601 < sqrt10 < 3.1622776602: True (sqrt10 = 3.16227766016838).
  (Hand: 1.8563683593/3.1622776602 = 0.58703521913..; 1.8563683595/3.1622776601 = 0.58703521925..)

## 3. Prior art
- WebSearch for tables (beta=0.1, 0.587035): results listed titles only (Vilnius Tech MMA iterative
  transformation paper, Springer note, ResearchGate flow analysis, etc.); I did not open them => "not read".
  Table value at beta = 0.1 (~0.587035) is from the task statement, not verified from a source by me;
  my independent computation agrees with it to the printed 6 digits.
- WebFetch arxiv.org/pdf/1212.5057 (Toepfer's algorithm and extension): read. Its tables cover only negative beta
  (-0.01 ... -0.18), so no beta = 0.1 value there. It states: Coppel and Craven-Peletier showed the normal-flow
  restriction 0<f'<1 can be dropped for 0 <= beta <= 1; Weyl: for each beta a physical solution exists with f''
  positive and decreasing to 0; for beta>0 under normal flow Hartree/Stewartson give uniqueness. (second-hand
  summary by the fetch tool, not a primary reading.)
- Not read: Mathematika "On the uniqueness of solutions of the Falkner-Skan equation", arXiv 2011.07725,
  MDPI Fluids review 6(4):153 (search hits only).
- Conclusion: statements agree with the literature (existence + uniqueness for 0<=beta<=1, even beyond the bounded
  class); the formalized class -1<=p<=1 is a subclass of what is classically unique.

## Verdict: STANDS
Faithful ODE, correct one-sided quantification, non-vacuous (existence part witnesses hypotheses), scaling
arithmetic and sqrt10 bounds verified, window verified numerically to 13 digits. Caveat: the F10Bounded
dependency was out of scope and unread.
