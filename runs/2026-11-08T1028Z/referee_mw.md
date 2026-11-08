# Referee report: MonotoneWindow (hiemenz_/homann_monotone_window)

VERDICT: STANDS-WITH-CORRECTIONS (statement true and non-vacuous; planned proof sound in outline;
one wrong sentence in the module doc, one real gap in how the certified lemmas are applied, one optional strengthening)

## 1. Statement attack
- Quantifiers/junk: no division, no limits other than `Tendsto p atTop (nhds 1)`, decimals are exact reals
  (1.2325876568 etc.). Values of f,p,q off [0,inf) are irrelevant. HasDerivWithinAt on Ici 0 gives continuity
  (one-sided at 0) and is the faithful formalisation of C^1-on-[0,inf); a two-sided derivative on (0,inf) plus
  continuity at 0 would be equivalent. No hypothesis is a junk-value artefact.
- Non-vacuous: Hiemenz and Homann flows with f'>0, f''>0, f'<1 exist classically (f''(0)=1.2326, 1.3119 numerically; shooting:
  the sets {a: q hits 0 with p<1} and {a: p crosses 1 with q>0} are open, disjoint, both nonempty by the
  certified under/over events, so the connectedness of (a_under,a_over) yields a with q>0,p<1 for ever; then
  p increasing, bounded, limit L<=1, and L=1 follows since q'->(L^2-1)<0 would force q<0). `hiemenz_exists` itself
  only gives *a* solution with p->1 in the window, not q>0, so q>0 existence is a separate (classical) fact; the theorem
  does not need it, but nobody should read the pair exists+window as "the monotone solution is in the window"
  unless q>0 existence is also proved (or the next remark is used).
- Naturalness / strength of hypothesis: given p->1, "q>0 on [0,inf)" is EQUIVALENT to "p<1 on [0,inf)" (Coppel's
  0<f'<1 class). Proof: at any zero of q with p<1, q'=-1+p^2<0 so q goes + to -; once q<0, p decreases, p<1 stays,
  so q' <0 at every later zero, q can never return to 0 from below, p is decreasing and cannot tend to 1; also q(0)<=0 is
  impossible (q'(0)=-1). So the stated class is exactly the physical attached/monotone class. Suggest ADDING
  (or proving as lemma) the variant hypothesis `∀ η ≥ 0, p η < 1`; strictly stronger theorem, same proof.
  Hypothesis p(0)=0,f(0)=0 both used (D(0),E(0)=0). Nothing superfluous.
- Not covered: solutions with p>1 somewhere that still tend to 1 (the full uniqueness problem). Docstring
  must not claim "every solution of the BVP"; module doc says "**every** solution of the boundary-value problem
  whose profile is ...", acceptable, but the headline "wall shear of every monotone solution" is OK only with that qualifier.

## 2. Independent derivation (Crocco)
- With q>0 on the range, t=f' is a C^1 diffeo (dt/deta=q>0), z(t)=f'', F(t)=f. Then dF/dt = f'/f'' = t/z;
  z dz/dt = f''' = -kFz -1 + t^2, so dz/dt = -kF - (1-t^2)/z. MATCHES the doc. z(0)=a, F(0)=0.
- Differences (z2-z1 = D, F2-F1 = E): E' = t(1/z2-1/z1) = -tD/(z1z2); D' = -kE - (1-t^2)(1/z2-1/z1) = -kE + (1-t^2)D/(z1z2).
  MATCHES. CORRECTION: the doc calls (D,E) "cooperative"; it is not (both off-diagonals are <=0). The system
  is cooperative in (D, -E): with u=D, v=-E: u' = c u + k v, v' = d u, c=(1-t^2)/(z1z2)>=0 (needs t<=1), k>=0, d=t/(z1z2)>=0 (t>=0).
  From u(0)=D(0)>0, v(0)=0: u>0, v>=0 persist (first-exit argument), hence u'>=cu>=0 and D>=D(0) on the common range.
  k>=0 used for sign of kv, t<1 (t<=1) for c>=0. For t>1 (overshoot beyond 1) c<0 and the bound fails, but is not needed.
- Case analysis (the doc's last sentence is imprecise; here is the correct one). Let a*=q(0) of the monotone BVP solution; its Crocco
  range is [0,1) (p strictly increasing to 1, never reaching it).
  * a* <= a_under impossible: a*=a_under contradicts IVP uniqueness (BVP has q>0,p<1; undershoot has q<0 somewhere);
    a*<a_under: z1=BVP, z2=undershoot, D>=D0>0, so z2>D0 on [0,T), T=p(first zero eta0 of q)<1 (first zero exists by IVT, q>0 before it,
    p(eta0)<1 by the event). But z2(t)->q(eta0)=0 as t->T^-. Contradiction. (Here z->0 is for the UNDERSHOOT solution, by continuity of q; no
    assumption on f''->0 of the BVP solution is needed. The doc's phrase "z must become small near t->1" is therefore not what is used.)
  * a* >= a_over impossible: equality by uniqueness (overshoot has p>1); a*>a_over: z1=overshoot (positive on all of [0,1], since q>0 on [0,eta],
    p(eta)>1), z2=BVP, z2>=z1+D0>=m+D0 with m=min z1>0 on [0,1]. So q(eta)=z2(p(eta))>=m>0 for all eta, p'=q>=m, p unbounded,
    contradicting p->1. (Again not "z->0": the contradiction is with p->1 / boundedness.) Correct the module doc accordingly.
- Strictness at the window ends: obtained from the equality case via IVP uniqueness (Gronwall; polynomial RHS, locally Lipschitz). Needed in Lean;
  without it only <= / >= follow. The strict end values are exactly the certified rationals, so fine.
- Smoothness bookkeeping: z=q∘(p|)^{-1}, F=f∘(p|)^{-1} are C^1 on [0,T) (one-sided at 0) because p'=q>0; inverse-function derivative on a half-open interval is a
  technical but routine Lean point; avoid it by doing the comparison in eta-time? (Not possible directly: the two solutions have different time scales; keep Crocco.)

## 2b. GAP (real) in applying the certified lemmas
`hiemenz_under/over`, `homann_under/over` are hypothetical: "for every solution on [0,S], S>=15/2 (resp. 6)". To USE them one must produce a
solution of the IVP with q(0)=1.2325876568 (resp. ...569) on all of [0,S], S>=15/2. Mathlib's Picard-Lindelof gives only a local solution; global
existence on [0,15/2] needs an a priori bound. For the undershoot it is easy to get as far as the first zero of q (q decreasing, 0<p<1, f<=eta), but the lemma needs the
solution to continue to S. For the overshoot, after p reaches 1 the equation q'=p^2-1-k f q is Riccati-like, so no blow-up before 15/2 must be proved (f>0 damping,
q bounded via q'<=p^2-1 with p<=1+...? needs an explicit bound). Fix options: (i) prove a priori bounds on [0,S] (p<=C, q<=C') with a continuation lemma;
(ii) restate the four certified lemmas with a conclusion "...or the maximal solution ends before eta" (cannot, they are frozen/proved); (iii) apply the lemmas to a
solution obtained by truncating/modifying the ODE after the event (not allowed: hypotheses fix the ODE). Option (i) is the honest path; budget it
as the main extra work, comparable to the comparison lemma. The module doc says "no new numerical certificate" -- true, but a new analytic lemma is needed.

## 3. Prior art (what I actually read)
- READ: mdpi.com/2311-5521/6/4/153 (via WebFetch, summary only): states Weyl (f'>0), Coppel (assumed 0<f'<1, beta>=0, extends Weyl), Tam (removed Coppel's
  assumption, shooting), Craven et al. (existence+uniqueness for 0<=beta<1 by showing 0<f'<1), Hartman only cited as a general reference. It names no specific
  uniqueness proof for beta=1.
- READ (metadata only, no abstract): scilit page: Craven & Peletier, "On the uniqueness of solutions of the Falkner-Skan equation", Mathematika 19 (1972) 129-133.
- NOT READ (only seen in search listings / my memory): Coppel 1960 Phil. Trans. A 253, Hartman ch. XIV, Hastings-McLeod, Tam, the Cambridge "note on existence ... Falkner-Skan",
  the Caltech chapter, Springer BF00944877. I could not confirm argument-level details from any of them.
- From memory (unverified): Coppel's uniqueness for beta>=0 in the class 0<f'<1 uses a Crocco-type change of variables (his paper is the source of the "f''
  as a function of f'" device), and Hartman/Hastings-McLeod present uniqueness of the monotone solution via comparison in Crocco variables or via a Sturm-type
  argument on f'' differences. So the planned argument is very likely the classical one for the class 0<f'<1 (= our q>0 class, by the equivalence in section 1);
  uniqueness in the full class (solutions with f'>1 somewhere) is a different, harder result (Tam / Craven-Peletier for some beta ranges) and is NOT what the theorem claims. Treat all of this as
  "cited/recalled, not verified" before putting it in a README.

## Summary of required corrections
1. Module doc: replace "cooperative (D,E)" by "cooperative in (D,-E)"; replace the contradiction sentence by the two-case argument above (undershoot: z->0 at the first
   zero; overshoot: q>=m>0 contradicts p->1).
2. Add the equivalence "q>0 <-> p<1" as a lemma (or state hypothesis as p<1); keeps the theorem physical.
3. Plan the global-existence/continuation lemma for the IVP solutions on [0,S] (section 2b); it is the main unplanned work.
4. Plan IVP uniqueness (Gronwall) for the equality cases.
