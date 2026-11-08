# Referee report: Falkner-Skan rows (fs_half_exists, fs_zero_wall_shear)
Files read: FalknerSkan.lean, Homann.lean, Blasius.lean, FSRows.lean only. Scripts in /tmp/referee_fs.

## 1. Statement attack
- Equation: g''' + g g'' + beta(1-g'^2) = 0 as f'=p, p'=q, q' = -f q - beta(1-p^2).
  The field `-(f η * q η) - 1/2 * (1 - p η ^ 2)` is exactly this with beta = 1/2.
  The beta = 0 field `-(f η * q η)` is exactly beta = 0.
- Quantifiers: fs_half_exists is a plain ∃ with strict window and all of ODE, f0, p0, limit inside the ∃. Fine.
  fs_zero_wall_shear is ∀ over (f,p,q) with the hypotheses as hypotheses, closed window. Fine.
- One-sided derivatives: HasDerivWithinAt on Ici 0 at every η ≥ 0, so at 0 it is the right derivative. Correct.
  Values of f,p,q on η<0 are unconstrained and irrelevant (q 0 only uses the point 0). No junk-value issue:
  no division, sqrt or partial function appears in either statement.
- Tendsto p atTop (𝓝 1) is the right condition g' -> 1.
- Vacuity of the beta = 0 hypotheses: not vacuous mathematically. A solution exists (Blasius profile, classical;
  my numerics below integrate one to 40 digits, wall shear 0.46959998836101330). The statement does NOT prove
  existence; it is a pure bound, so if no solution existed it would be vacuously true but still not false.
  Side remark: the row says nothing about existence at beta = 0; that would need a separate theorem if wanted.
- Module doc matches the statements (windows, normalisation, "uniqueness not part of statements").
  Doc says "Hiemenz is beta = 1 as it stands": correct (f''' + f f'' + 1 - f'^2 = 0).
- Nit: the β = 0 and β = 1/2 rows are logically asymmetric (existence vs. universal bound), as the doc says.
  The β = 1/2 row is existence only: it does not say every solution has that shear (uniqueness not claimed).

## 2. Scaling check (sympy + exact rationals, /tmp/referee_fs/c.py)
- F(s) = c f(s/c): sympy gives F''' + (a/c^2) F F'' + (b/c^2)(1-F'^2) = (1/c^2) * [f''' + a f f'' + b(1-f'^2)](s/c). Confirmed.
  F''(0) = f''(0)/c (F'' = f''(s/c)/c). Confirmed. The Lean `scale` (Q = q(s/c)/c, P = p(s/c)) matches.
- Homann (a=2,b=1), c = √2: a/c^2 = 1, b/c^2 = 1/2 -> beta = 1/2 with F''(0) = 1.3119.../√2. Correct.
- WARNING (wording only, not Lean): in the task text/doc, "c = √2 maps Blasius f''' + f f''/2 = 0 to beta = 0" is
  backwards for the formula F = c f(s/c): a = 1/2 gives a/c^2 = 1 only for c = 1/√2.
  The Lean proof uses the correct direction: it takes a beta=0 solution g (a=1) and scales by c = √2 to get a = 1/2
  (Blasius form), and g''(0) = √2 * f''(0). Module doc says "maps ... divides wall shear by c. With c=√2 the Homann
  problem becomes beta=1/2 and the Blasius problem ... becomes beta=0": second half is imprecise (should read:
  the beta=0 problem becomes Blasius, or c = 1/√2). Harmless to the frozen Lean text (doc comment only).
- Windows, exact rational arithmetic with √2 in [1.41421356237309, 1.41421356237310] (squares checked <2< / >2):
  Homann: 1.3119376938/1.41421356237310 = 0.92768003978 > 0.927680039; 1.3119376939/1.41421356237309 = 0.92768003985 < 0.92768004. OK.
  Blasius: 0.33205733621519*1.41421356237309 = 0.46959998836100... >= 0.4695999883610 (value 4695999883610.027e-13);
           0.33205733621520*1.41421356237310 = 0.46959998836102... <= 0.4695999883611 (4695999883610.202e-13). OK.
  The lower margin is only 2.7e-14 relative to window units 1e-13: tight but valid (exact rationals).
- FSRows.lean uses coarser √2 bounds (1.4142135623, 1.4142135624) for the Homann row: check by hand:
  1.3119376938/1.4142135624 = 0.927680039..78 > 0.927680039 ok; 1.3119376939/1.4142135623 = 0.92768003985 < .04 ok.
  Blasius row uses the 14-digit bounds above (sqrt2_le', le_sqrt2'), consistent with my check.

## 3. Independent numerics (mpmath odefun Taylor shooting + findroot, dps 30 and 40; agree to 30+ digits)
  Homann (2,1)        1.311937693879805135481646170683425860209
  FS beta=1/2         0.9276800398366511392192687825603081186435
  FS beta=0           0.4695999883610133045093336534475884587807
  Blasius (a=1/2)     0.3320573362151962989371812381621035958416
  Consistency: Homann/√2 = FS(1/2) and √2*Blasius = FS(0) hold to the digits of my inputs (30 dps).
  All lie inside the windows: 0.927680039837 in (…039, …040); 0.46959998836101330 in [..3610, ..3611];
  1.31193769388 in (…938, …939); 0.332057336215196 in [..519, ..520].
  Caveat: single method (shooting from η=0 with truncated domain T=10/14, tail error exponentially small, two precisions agree).
  Not a second independent method; the literature value in §4 is the cross-check.

## 4. Prior art (web)
READ (WebFetch succeeded):
- arXiv:1907.09912 (Asymptotic Approximant for the Falkner-Skan Boundary-Layer equation), Fig. 2 caption: beta = 0.5,
  f''(0) = 0.927680039836653; beta = 0, f''(0) = 0.469599988361 (the paper says its beta = 0 value is √2 times the literature value,
  i.e. other scaling). So 0.927680039836653 printed (15 digits; mine 0.927680039836651, differs by 2e-15, last digit of print),
  0.469599988361 printed (12 digits; mine 0.4695999883610133 rounds to it). No existence/uniqueness statement; no Homann mention.
- Fluids 6(4):153 (2021), "On Solving the Nonlinear Falkner-Skan Boundary-Value Problem: A Review" (https://www.mdpi.com/2311-5521/6/4/153),
  via the fetch tool's summary only: Weyl [6] existence+uniqueness assuming f'>0 by fixed point; Coppel [7] assumed 0<f'<1;
  Tam [8] removed that assumption by shooting; Craven & Peletier [9] proved existence and uniqueness for 0<=beta<1 (arguing 0<f'<1 holds there);
  Hartman [14] listed only. Homann: review mentions Shin's result for a variant of the Crocco-Wang form with (β0,β)=(1,1/2); no direct identity stated.
- arXiv:2010.05682 (Jaya Runge-Kutta): prints Blasius-type f''(0) = 0.332057 (refs Zhang, Asaithambi 0.33205). Names a "Homann ... beta0=1, beta=0.5" case
  but states no equivalence.
NOT READ / second-hand only (my knowledge, unverified here): H. Weyl, "On the differential equations of the simplest boundary-layer problems",
  Ann. Math. 43 (1942) 381-407; W. A. Coppel, "On a differential equation of boundary-layer theory", Phil. Trans. R. Soc. A 253 (1960) 101-136;
  A. H. Craven & L. A. Peletier, "On the uniqueness of solutions of the Falkner-Skan equation", Mathematika 19 (1972) 129-135; Hartman, ODE (1964/2002), Ch. XIV;
  Asaithambi; Salama; Fazio; White, Viscous Fluid Flow (the Homann = beta 1/2 correspondence and its wall-shear digits, I believe in White's
  chapter 4 and in Schlichting-Gersten, but not read). The equivalence Homann <=> FS beta=1/2 by this scaling is verified by me algebraically
  (§2); a print citation for it is not confirmed. Several searches hit paywalled Elsevier/Springer pages; those count as not read.
Takeaway: published theory (Weyl/Coppel/Craven-Peletier) gives uniqueness within 0<f'<1 or (CP) for 0<=beta<1; the frozen beta=0 row quantifies
  over ALL solutions with only p->1, no monotonicity, and this is covered by the certified Blasius theorem (no class restriction), so no prior art needed.
  The beta=1/2 existence row avoids uniqueness altogether.

VERDICT: STANDS
