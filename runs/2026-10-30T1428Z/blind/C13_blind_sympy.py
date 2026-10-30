"""Blind sympy re-derivation of Bamba-Capozziello-Nojiri-Odintsov (arXiv:1205.3421v3),
Section XI, Eqs. (11.10)-(11.13), (11.21)-(11.31), (11.39)-(11.40).

Conventions taken from the paper:
  R = -6 (Hdot + 2 H^2)                         (11.6)
  (11.1)+(11.2): H^2 = (1/3)[rhoM/F' + (1/F')((F - R F')/2 - 3 H Rdot F'')]
  (11.5):        Hdot = -(1/(2F'))[3 H0^2 Om a^-3 + Rddot F'' + Rdot (Rdot F''' - H F'')]
  rhoM = 3 H0^2 Om a^-3, a(t0) = 1
  q = -a'' a / a'^2, j = a''' a^2/a'^3, s = a'''' a^3/a'^4, l = a''''' a^4 / a'^5  at t0
Closure: (11.1)@t0, (11.5)@t0, d/dt(11.5)@t0, F'(R0) = 1, F''''(R0) = 0.
"""
import sympy as sp

H0, Om, q, j, s, l, tau = sp.symbols('H0 Omega_M q0 j0 s0 l0 tau', real=True)
F0, F2, F3 = sp.symbols('F0 F2 F3')   # F(R0), F''(R0), F'''(R0)

out = []
def say(*a):
    print(*a)

# ---------------------------------------------------------------------------
# 1. Direct differentiation: a(t0 + tau) Taylor polynomial up to tau^5 (enough
#    for H up to 4th derivative, R up to 3rd derivative at t0).
a = 1 + H0*tau - q*H0**2*tau**2/2 + j*H0**3*tau**3/6 + s*H0**4*tau**4/24 + l*H0**5*tau**5/120
H = sp.diff(a, tau)/a
Hd = [sp.simplify(sp.diff(H, tau, k).subs(tau, 0)) for k in range(5)]
Rt = -6*(sp.diff(H, tau) + 2*H**2)
Rd = [sp.expand(sp.simplify(sp.diff(Rt, tau, k).subs(tau, 0))) for k in range(4)]

say("== Check (10.6)-(10.9) [H derivatives] ==")
p106 = -H0**2*(1+q)
p107 = H0**3*(j+3*q+2)
p108 = H0**4*(s-4*j-3*q*(q+4)-6)
p109 = H0**5*(l-5*s+10*(q+2)*j+30*(q+2)*q+24)
for name, d, p in [("10.6", Hd[1], p106), ("10.7", Hd[2], p107), ("10.8", Hd[3], p108), ("10.9", Hd[4], p109)]:
    say(f"  ({name}) direct - printed =", sp.expand(d - p))

say("== Check (11.10)-(11.13) [R derivatives] ==")
p1110 = -6*H0**2*(1-q)
p1111 = -6*H0**3*(j-q-2)
p1112 = -6*H0**4*(s+q**2+8*q+6)
p1113 = -6*H0**5*(l-s+2*(q+4)*j-6*(3*q+8)*q-24)
for name, d, p in [("11.10", Rd[0], p1110), ("11.11", Rd[1], p1111), ("11.12", Rd[2], p1112), ("11.13", Rd[3], p1113)]:
    say(f"  ({name}) direct  =", sp.factor(d))
    say(f"  ({name}) direct - printed =", sp.factor(sp.expand(d - p)))

# ---------------------------------------------------------------------------
# 2. Field equations as functions of t via a total-derivative operator on
#    jet variables:  aa (scale factor), h_k = d^k H/dt^k, r_k = d^k R/dt^k,
#    f_k = F^{(k)}(R(t)), with D f_k = f_{k+1} r_1, D aa = aa h_0.
NJ = 6
h = sp.symbols('h0:%d' % NJ)
r = sp.symbols('r0:%d' % NJ)
f = sp.symbols('f0:%d' % NJ)
aa = sp.Symbol('aa')
def D(e):
    res = sp.diff(e, aa)*aa*h[0]
    for k in range(NJ-1):
        res += sp.diff(e, h[k])*h[k+1] + sp.diff(e, r[k])*r[k+1] + sp.diff(e, f[k])*f[k+1]*r[1]
    return sp.expand(res) if not isinstance(e, sp.Equality) else None

rhoM = 3*H0**2*Om*aa**-3
# (11.1)+(11.2), multiplied by 3 F'
E1_t = 3*f[1]*h[0]**2 - (rhoM + (f[0] - r[0]*f[1])/2 - 3*h[0]*r[1]*f[2])
# (11.5), multiplied by 2F':   2F' Hdot + [ ... ] = 0
E5_t = 2*f[1]*h[1] + (rhoM + r[2]*f[2] + r[1]*(r[1]*f[3] - h[0]*f[2]))
# Sanity: R relation and consistency (11.5) <= d/dt (11.1) + matter continuity
Rrel = r[0] + 6*(h[1] + 2*h[0]**2)
# d/dt(E1_t) should be a combination of E1_t, E5_t and the R-relation:
dE1 = D(E1_t)
sub_r = {r[0]: -6*(h[1]+2*h[0]**2)}
chk = sp.simplify((dE1 - 3*h[0]*E5_t).subs(sub_r))
say("== Consistency: d/dt[E(11.1)] - 3H*E(11.5), using R = -6(Hd+2H^2) only:", chk, "(0 => (11.5) is d/dt of (11.1) when H != 0)")

# Exact time derivative of (11.5) (divided form): Hddot = d/dt of RHS
rhs5 = -(rhoM + r[2]*f[2] + r[1]*(r[1]*f[3] - h[0]*f[2]))/(2*f[1])
# quotient rule through D on the numerator and on 2F'
num = rhoM + r[2]*f[2] + r[1]*(r[1]*f[3] - h[0]*f[2])
Dnum = D(num)
Dden = D(2*f[1])
Hdd_exact = -(Dnum*2*f[1] - num*Dden)/(2*f[1])**2

# Printed (11.18)
Hdd_print = (r[1]**2*f[3] + (r[2]-h[0]*r[1])*f[2] + 3*H0**2*Om*aa**-3)/(2*(r[1]*f[2])**-1*f[1]**2) \
    - (r[1]**3*f[4] + (3*r[1]*r[2] - h[0]*r[1]**2)*f[3])/(2*f[1]) \
    - ((r[3] - h[0]*r[2] + h[1]*r[1])*f[2] - 9*H0**2*Om*h[0]*aa**-3)/(2*f[1])
say("== (11.18): exact d/dt of (11.5) minus printed (11.18) ==",
    sp.factor(sp.simplify(Hdd_exact - Hdd_print)))

# ---------------------------------------------------------------------------
# 3. Evaluate at t0 with cosmographic values; F'(R0)=1, F''''(R0)=0, a(t0)=1.
at0 = {aa: 1, h[0]: H0, h[1]: Hd[1], h[2]: Hd[2], h[3]: Hd[3], h[4]: Hd[4],
       r[0]: Rd[0], r[1]: Rd[1], r[2]: Rd[2], r[3]: Rd[3],
       f[0]: F0, f[1]: 1, f[2]: F2, f[3]: F3, f[4]: 0}

eq14 = sp.expand(E1_t.subs(at0))                          # (11.14)
eq15 = sp.expand(E5_t.subs(at0))                          # (11.15)
eq20_exact = sp.expand(sp.numer(sp.together((h[2] - Hdd_exact).subs(at0))))
eq20_print = sp.expand(sp.numer(sp.together((h[2] - Hdd_print).subs(at0))))

def solve_closure(eq20, label):
    # (11.20) contains F2*(...)-type quadratic terms; use (11.15) [linear in F2,F3]
    # to solve F3 first is not possible linearly in general, so solve the system.
    sol = sp.solve([eq15, eq20], [F2, F3], dict=True)
    say(f"  [{label}] number of solutions for (F2,F3):", len(sol))
    res = []
    for so in sol:
        f2 = sp.factor(so[F2]); f3 = sp.factor(so[F3])
        f0 = sp.factor(sp.solve(eq14.subs({F2: f2}), F0)[0])
        res.append((f0, f2, f3))
    return res

# Printed results
P0 = (j-q-2)*l - (3*s+7*j+6*q**2+41*q+22)*s - ((3*q+16)*j+20*q**2+64*q+12)*j \
     - (3*q**4+25*q**3+96*q**2+72*q+20)
Q0 = (q**2-j*q+2*q)*l + (3*q*s+(4*q+6)*j+6*q**3+44*q**2+22*q-12)*s \
     + (2*j**2+(3*q**2+10*q-6)*j+17*q**3+52*q**2+54*q+36)*j \
     + 3*q**5+28*q**4+118*q**3+72*q**2-76*q-64
P2 = 9*s+6*j+9*q**2+66*q+42
Q2 = -(6*(q+1)*s + (2*j-2*(1-q))*j + 6*q**3+50*q**2+74*q+32)
P3 = 3*l+3*s-9*(q+4)*j-(45*q**2+78*q+12)
Q3 = -(2*(1+q)*l + 2*(j+q)*s - (2*j+4*q**2+12*q+6)*j - (30*q**3+84*q**2+78*q+24))
Rc = (j-q-2)*l - (3*s-2*j+6*q**2+50*q+40)*s + ((3*q+10)*j+11*q**2+4*q+18)*j \
     - (3*q**4+34*q**3+246*q+104)

pr_F0 = -6*H0**2*(P0*Om+Q0)/Rc
pr_F2 = -(P2*Om+Q2)/Rc/(6*H0**2)
pr_F3 = -(P3*Om+Q3)/((j-q-2)*Rc)/(6*H0**2)**2

def compare(res, label):
    for (f0, f2, f3) in res:
        say(f"--- [{label}] derived ---")
        n0 = sp.expand(sp.numer(sp.together(f0/(6*H0**2))))
        d0 = sp.expand(sp.denom(sp.together(f0/(6*H0**2))))
        say("  F(R0)/(6H0^2)      =", sp.factor(f0/(6*H0**2)))
        say("  F''(R0)*6H0^2      =", sp.factor(f2*6*H0**2))
        say("  F'''(R0)*(6H0^2)^2 =", sp.factor(f3*36*H0**4))
        # normalise: denominator of F''*6H0^2 written as R_derived with l-coefficient (j-q-2)
        g2 = sp.together(f2*6*H0**2)
        N2, D2 = sp.fraction(sp.factor(g2))
        D2p = sp.Poly(sp.expand(D2), l)
        lc = sp.factor(D2p.coeff_monomial(l))
        scale = sp.factor(lc/(j-q-2))
        Rder = sp.expand(D2/scale)
        say("  derived R (normalised so coeff of l0 is (j0-q0-2)):")
        say("     R_der =", sp.collect(Rder, [l, s, j]))
        say("     R_der - R_printed =", sp.factor(sp.expand(Rder - Rc)))
        # numerators with that R
        N0 = sp.expand(sp.cancel(-f0/(6*H0**2)*Rder))
        N2n = sp.expand(sp.cancel(-f2*6*H0**2*Rder))
        N3n = sp.expand(sp.cancel(-f3*36*H0**4*(j-q-2)*Rder))
        for nm, Nn, Pp, Qp in [("0", N0, P0, Q0), ("2", N2n, P2, Q2), ("3", N3n, P3, Q3)]:
            Pd = sp.expand(sp.diff(Nn, Om)); Qd = sp.expand(Nn - Pd*Om)
            say(f"  P{nm}_der =", sp.collect(Pd, [l, s, j]))
            say(f"  Q{nm}_der =", sp.collect(Qd, [l, s, j]))
            say(f"  P{nm}_der - P{nm}_printed =", sp.factor(sp.expand(Pd - Pp)))
            say(f"  Q{nm}_der - Q{nm}_printed =", sp.factor(sp.expand(Qd - Qp)))
        say("  F0_der - F0_printed (simplified) =", sp.factor(sp.simplify(f0 - pr_F0)))
        say("  F2_der - F2_printed (simplified) =", sp.factor(sp.simplify(f2 - pr_F2)))
        say("  F3_der - F3_printed (simplified) =", sp.factor(sp.simplify(f3 - pr_F3)))

say("\n== Closure with the EXACT time derivative of (11.5) ==")
res_exact = solve_closure(eq20_exact, "exact")
compare(res_exact, "exact")
say("\n== Closure with the PRINTED (11.18)/(11.20) (sign +Hdot*Rdot) ==")
res_print = solve_closure(eq20_print, "printed-11.20")
compare(res_print, "printed-11.20")

# ---------------------------------------------------------------------------
# 4. LCDM values (11.39), compare with (11.40): F(R0) = R0 + 2 Lambda, F''=F'''=0,
#    Lambda = 3 H0^2 (1 - Om)  (flat LCDM: H^2 = H0^2 (Om a^-3 + 1 - Om)).
say("\n== LCDM check (11.39)/(11.40) ==")
lcdm = {q: sp.Rational(1, 2) - sp.Rational(3, 2)*(1-Om), j: 1,
        s: 1 - sp.Rational(9, 2)*Om, l: 1 + 3*Om + sp.Rational(27, 2)*Om**2}
# verify (11.39) from a flat LCDM a(t): use H^2 = H0^2(Om a^-3 + 1 - Om) via jet operator
Hsq = lambda A: H0**2*(Om*A**-3 + 1 - Om)
A = sp.Function('A')(tau)
# a' = a H(a); compute derivatives of a by chain rule
adot = A*sp.sqrt(Hsq(A))
ders = [A, adot]
for k in range(4):
    ders.append(sp.simplify(sp.diff(ders[-1], tau).subs(sp.Derivative(A, tau), adot)))
H0p = sp.Symbol('H0p', positive=True)   # H0 > 0 resolves sqrt(H0^2) = H0
vals = [sp.simplify(dd.subs(A, 1).subs(H0, H0p)) for dd in ders]
Hz = H0p
say("  q0 from LCDM a(t):", sp.simplify(-vals[2]/Hz**2 - lcdm[q]), "(diff vs 11.39)")
say("  j0 from LCDM a(t):", sp.simplify(vals[3]/Hz**3 - lcdm[j]), "(diff vs 11.39)")
say("  s0 from LCDM a(t):", sp.simplify(vals[4]/Hz**4 - lcdm[s]), "(diff vs 11.39)")
say("  l0 from LCDM a(t):", sp.simplify(vals[5]/Hz**5 - lcdm[l]), "(diff vs 11.39)")
Lam = 3*H0**2*(1-Om)
R0L = sp.expand(Rd[0].subs(lcdm))
target_F0 = sp.expand(R0L + 2*Lam)
say("  printed R at LCDM:", sp.factor(Rc.subs(lcdm)))
say("  printed P0*Om+Q0 at LCDM:", sp.factor(sp.expand((P0*Om+Q0).subs(lcdm))))
say("  printed P2*Om+Q2 at LCDM:", sp.factor(sp.expand((P2*Om+Q2).subs(lcdm))))
say("  printed P3*Om+Q3 at LCDM:", sp.factor(sp.expand((P3*Om+Q3).subs(lcdm))))
say("  printed (j-q-2) at LCDM:", sp.factor((j-q-2).subs(lcdm)))
say("  printed F(R0) at LCDM:", sp.factor(sp.simplify(pr_F0.subs(lcdm))), " target R0+2Lambda =", sp.factor(target_F0))
say("  printed F'' at LCDM:", sp.factor(sp.simplify(pr_F2.subs(lcdm))))
say("  printed F''' at LCDM:", sp.factor(sp.simplify(pr_F3.subs(lcdm))))
for label, res in [("exact", res_exact), ("printed-11.20", res_print)]:
    for (f0, f2, f3) in res:
        say(f"  [{label}] derived F(R0) at LCDM:", sp.factor(sp.simplify(f0.subs(lcdm))),
            " minus target:", sp.factor(sp.simplify(f0.subs(lcdm) - target_F0)))
        say(f"  [{label}] derived F'' at LCDM:", sp.factor(sp.simplify(f2.subs(lcdm))))
        say(f"  [{label}] derived F''' at LCDM:", sp.factor(sp.simplify(f3.subs(lcdm))))
# Only (q0,j0) fixed to LCDM (paper's remark after (11.40))
qj = {q: lcdm[q], j: 1}
say("  printed F'' with only (q0,j0)=LCDM:", sp.factor(sp.simplify(pr_F2.subs(qj))))
say("  printed F''' with only (q0,j0)=LCDM:", sp.factor(sp.simplify(pr_F3.subs(qj))))
say("  printed F(R0) with only (q0,j0)=LCDM minus R0+2Lambda:",
    sp.factor(sp.simplify(pr_F0.subs(qj) - target_F0)))
for (f0, f2, f3) in res_exact:
    say("  [exact] F'' with only (q0,j0)=LCDM:", sp.factor(sp.simplify(f2.subs(qj))))
    say("  [exact] F''' with only (q0,j0)=LCDM:", sp.factor(sp.simplify(f3.subs(qj))))
    say("  [exact] F(R0) with only (q0,j0)=LCDM minus R0+2Lambda:", sp.factor(sp.simplify(f0.subs(qj) - target_F0)))

# ---------------------------------------------------------------------------
# 5. Diagnostics: could the printed (11.13) typo explain the printed R?
say("\n== Diagnostic variants (denominator R only) ==")
R3 = sp.Symbol('R3')
at0_r3 = dict(at0); at0_r3[r[3]] = R3
for label, Hdd in [("exact (11.18)", Hdd_exact), ("printed (11.18)", Hdd_print)]:
    e20 = sp.expand(sp.numer(sp.together((h[2] - Hdd).subs(at0_r3))))
    so = sp.solve([eq15, e20.subs(R3, p1113)], [F2, F3], dict=True)[0]
    N2, D2 = sp.fraction(sp.factor(sp.together(so[F2]*6*H0**2)))
    lc = sp.Poly(sp.expand(D2), l).coeff_monomial(l)
    Rv = sp.expand(D2/sp.factor(lc/(j-q-2)))
    say(f"  {label} + printed (11.13): R - R_printed =", sp.factor(sp.expand(Rv - Rc)))

# Degenerate case Rdot0 = 0 (j0 = q0 + 2): F''' drops out of (11.15) and (11.20).
say("\n== Degenerate case j0 = q0 + 2 (Rdot0 = 0), exact (11.18) ==")
deg = {j: q + 2}
e15d = sp.expand(eq15.subs(deg)); e20d = sp.expand(eq20_exact.subs(deg))
say("  F3 appears in (11.15)?", e15d.has(F3), " in (11.20)?", e20d.has(F3))
f2d = sp.solve(e15d, F2)[0]
say("  F''(R0)*6H0^2 from (11.15) alone =", sp.factor(f2d*6*H0**2))
say("  residual of (11.20) (extra consistency condition) =", sp.factor(e20d.subs(F2, f2d)))
f0d = sp.solve(eq14.subs(deg).subs(F2, f2d), F0)[0]
for (f0, f2, f3) in res_exact:
    say("  general derived F0 formula at j0=q0+2 minus direct value =",
        sp.factor(sp.simplify(f0.subs(deg) - f0d)))
    say("  general derived F2 formula at j0=q0+2 minus direct value =",
        sp.factor(sp.simplify(f2.subs(deg) - f2d)))
