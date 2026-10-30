import sympy as sp
z, y, q0, j0, Om = sp.symbols('z y q0 j0 Omega0')
J = j0 + Om
# standard d_L(z)/(d_H z) to z^2 (derived in C1_derive.py)
dLz = 1 + (1 - q0)/2*z - sp.Rational(1, 6)*(-q0 - 3*q0**2 + J)*z**2
R = sp.Rational
ps = {'L': 0, 'F': R(1, 2), 'P': 1, 'Q': R(3, 2), 'A': 2}
paper_z = {  # Eqs (20)-(24)
 'L': 1 - R(1,2)*(-1+q0)*z + R(1,6)*(q0+3*q0**2-J)*z**2,
 'F': 1 - R(1,2)*q0*z + R(1,24)*(3+10*q0+12*q0**2-4*J)*z**2,
 'P': 1 - R(1,2)*(1+q0)*z + R(1,6)*(3+4*q0+3*q0**2-J)*z**2,
 'Q': 1 - R(1,2)*(2+q0)*z + R(1,24)*(27+22*q0+12*q0**2-4*J)*z**2,
 'A': 1 - R(1,2)*(3+q0)*z + R(1,6)*(12+7*q0+3*q0**2-J)*z**2}
paper_y = {  # Eqs (56)-(60)
 'L': 1 - R(1,2)*(-3+q0)*y + R(1,6)*(12-5*q0+3*q0**2-J)*y**2,
 'F': 1 - R(1,2)*(-2+q0)*y + R(1,24)*(27-14*q0+12*q0**2-4*J)*y**2,
 'P': 1 - R(1,2)*(-1+q0)*y + R(1,6)*(3-2*q0+3*q0**2-J)*y**2,
 'Q': 1 - q0/2*y + R(1,12)*(3-2*q0+12*q0**2-4*J)*y**2,
 'A': 1 - R(1,2)*(1+q0)*y + R(1,6)*(q0+3*q0**2-J)*y**2}
paper_ln = {  # Eqs (61)-(65): ln(d_X/(y d_H))
 'L': -R(1,2)*(-3+q0)*y + R(1,24)*(21-2*q0+9*q0**2-4*J)*y**2,
 'F': -R(1,2)*(-2+q0)*y + R(1,24)*(15-2*q0+9*q0**2-4*J)*y**2,
 'P': -R(1,2)*(-1+q0)*y + R(1,24)*(9-2*q0+9*q0**2-4*J)*y**2,
 'Q': -R(1,2)*q0*y + R(1,24)*(3-2*q0+9*q0**2-4*J)*y**2,
 'A': -R(1,2)*(1+q0)*y + R(1,24)*(-3-2*q0+9*q0**2-4*J)*y**2}
for X, p in ps.items():
    dz = sp.expand(sp.series(dLz*(1+z)**(-p), z, 0, 3).removeO())
    dy = sp.expand(sp.series((dLz*(1+z)**(-p)*z/y).subs(z, y/(1-y)), y, 0, 3).removeO())
    ln = sp.expand(sp.series(sp.log(dy), y, 0, 3).removeO())
    print(X, 'z-eq diff:', sp.simplify(dz - paper_z[X]), '| y-eq diff:', sp.factor(dy - paper_y[X]), '| ln-eq diff:', sp.simplify(ln - paper_ln[X]))
# Does the PRINTED (59) exponentiate/log-consistently with printed (64)? 
lnp = sp.expand(sp.series(sp.log(paper_y['Q']), y, 0, 3).removeO())
print('ln(printed 59) - printed 64:', sp.factor(lnp - paper_ln['Q']))
# Attack: any exponent p making linear coeff -q0/2 and y^2 coeff = printed?
p = sp.symbols('p')
dy = sp.expand(sp.series((dLz*(1+z)**(-p)*z/y).subs(z, y/(1-y)), y, 0, 3).removeO())
print('linear coeff general p:', sp.factor(dy.coeff(y, 1)))
print('solve y^2 coeff == printed for p:', sp.solve(sp.expand(dy.coeff(y, 2) - paper_y['Q'].coeff(y, 2)), p))
