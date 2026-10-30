# CDL 2019 Sec. 7: f(T) relations. Conventions from the paper: T = -6H^2 (143),
# H^2 = (rho_m + rho_T)/3 (144), rho_T = T f' - f/2 - T/2 (146), rho_m = 3 H0^2 Om (1+z)^3 (kappa = 1).
import sympy as sp
z, Om, H0 = sp.symbols('z Omega_m0 H0', positive=True)
F1, F2, F3, F4, f0 = sp.symbols('F1 F2 F3 F4 f0')
q, j, s = sp.symbols('q0 j0 s0')
# (144)+(146) with 3H^2 = -T/2  =>  f/2 - T f_T = rho_m.
# --- (252)-(254): expand f about T0; tau = (H/H0)^2; T = T0 tau, T0 = -6 H0^2.
tau = sp.Symbol('tau'); T0 = -6*H0**2
Fs = [F1, F2, F3, F4]
fT = f0 + sum(Fs[i-1]*T0*(tau-1)**i/sp.factorial(i) for i in range(1, 5))          # f(T)
fprime = sum(Fs[i-1]*(tau-1)**(i-1)/sp.factorial(i-1) for i in range(1, 5))        # df/dT
eq = fT/2 - T0*tau*fprime - 3*H0**2*Om*(1+z)**3
f0sol = sp.solve(eq.subs({tau: 1, z: 0}), f0)[0]
print('f(T0) from Friedmann at z=0:', sp.factor(f0sol), ' | with F1=1:', sp.factor(f0sol.subs(F1, 1)), ' (paper (251): 6H0^2(Om-2))')
eq = sp.expand(eq.subs(f0, f0sol))
# tau = 1 + t1 z + t2 z^2 + t3 z^3
t1, t2, t3 = sp.symbols('t1 t2 t3')
ser = sp.expand(eq.subs(tau, 1 + t1*z + t2*z**2 + t3*z**3))
sol = {}
for k, tk in ((1, t1), (2, t2), (3, t3)):
    c = sp.expand(ser.coeff(z, k).subs(sol))
    sol[tk] = sp.simplify(sp.solve(c, tk)[0])
E = sp.series(sp.sqrt(1 + sum(sol[tk]*z**k for k, tk in ((1, t1), (2, t2), (3, t3)))), z, 0, 4).removeO()
E1, E2, E3 = [sp.simplify(E.coeff(z, k)*sp.factorial(k)) for k in (1, 2, 3)]
q0d = sp.simplify(E1 - 1)
j0d = sp.simplify(E2 + q0d**2)
s0d = sp.simplify(-(E3 - 3*q0d**2 - 3*q0d**3 + j0d*(3 + 4*q0d)))   # E3 = 3q^2+3q^3-j(3+4q)-s (verified in check_series.py)
Ot = Om/F1; F2t, F3t, F4t = F2/F1, F3/F1, F4/F1
q252 = -1 + 3*Ot/(2*(1+2*F2t))
j253 = 1 - 9*Ot**2*(3*F2t+2*F3t)/(2*(1+2*F2t)**3)
s254 = (1 - 9*Ot/(2*(1+2*F2t)) + 45*Ot**2*(3*F2t+2*F3t)/(2*(1+2*F2t)**3)
        + 27*Ot**3*(3*F2t+12*F3t+4*F4t)/(4*(1+2*F2t)**4) - 81*Ot**3*(3*F2t+2*F3t)**2/(2*(1+2*F2t)**5))
print('(252) printed - derived:', sp.simplify(q252 - q0d))
print('(253) printed - derived:', sp.simplify(j253 - j0d))
print('(254) printed - derived:', sp.simplify(s254 - s0d))
print('derived s0:', sp.factor(sp.simplify(s0d.subs(F1, 1))))
# --- (248), (249) and (250)
Hf = sp.Function('H')(z)
ff = sp.Function('f')(z)
Tz = sp.diff(-6*Hf**2, z)
print('dT/dz =', Tz, '  => d/dT = (1/T_z) d/dz = -1/(12 H H\') d/dz ; printed (248): -12 H H\' d/dz')
# first-order relation: f/2 - T f_T = 3H0^2 Om (1+z)^3 with f_T = f_z/T_z
g = ff/2 - (-6*Hf**2)*sp.diff(ff, z)/Tz
# eliminate Om: d/dz g = 3 g/(1+z)
ode_mine = sp.simplify(sp.diff(g, z) - 3*g/(1+z))
# printed (249): (f_z)^-1 [H(1+z) f_zz + 3 f H_z] = (1/H)(H_z)^-1 [3 H_z + (1+z) H_zz]
Hz, Hzz = sp.diff(Hf, z), sp.diff(Hf, z, 2)
fz, fzz = sp.diff(ff, z), sp.diff(ff, z, 2)
lhs = (Hf*(1+z)*fzz + 3*ff*Hz)/fz
rhs_pr = (3*Hz + (1+z)*Hzz)/(Hf*Hz)
rhs_alt = Hf*(3*Hz + (1+z)*Hzz)/Hz
# test on LCDM exact solution f = T + 6H0^2(Om-1)
HL = H0*sp.sqrt(Om*(1+z)**3 + 1 - Om)
fL = -6*HL**2 + 6*H0**2*(Om-1)
sub = lambda e: sp.simplify(e.subs(ff, fL).subs(Hf, HL).doit())
print('LCDM f=T-2Lambda satisfies my ODE:', sub(ode_mine) == 0)
print('LCDM: (249) LHS - printed RHS =', sub(lhs - rhs_pr))
print('LCDM: (249) LHS - RHS with H in place of 1/H =', sub(lhs - rhs_alt))
fzL = sp.diff(fL, z).subs(z, 0)
print('LCDM df/dz at z=0 =', sp.simplify(fzL), ' (= T_z(0) = -12 H0^2 (1+q0)); printed (250): 1')
