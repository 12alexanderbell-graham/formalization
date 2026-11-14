# eps(t) = t^8 sin(1/t): k-th derivative = A_k(t) sin(1/t) + B_k(t) cos(1/t), A_k, B_k polynomials.
import sympy as sp
t = sp.symbols('t')
A, B = t**8, sp.Integer(0)
out = [(A, B)]
for k in range(1, 5):
    A, B = sp.expand(sp.diff(A, t) + B / t**2), sp.expand(sp.diff(B, t) - A / t**2)
    out.append((A, B))
for k, (A, B) in enumerate(out):
    print(k, 'A =', A, '| B =', B)
# check against direct derivatives
e = t**8 * sp.sin(1/t)
for k, (A, B) in enumerate(out):
    assert sp.simplify(sp.diff(e, t, k) - (A*sp.sin(1/t) + B*sp.cos(1/t))) == 0
print('ok')

# t^6 cos(1/t) = A sin(1/t) + B cos(1/t) with A = 0, B = t^6 (the order-3 witness: its third derivative has
# A(0) = -1, B(0) = 0, so Lean's formula value at 0 is the true value 0).
A, B = sp.Integer(0), t**6
e = t**6 * sp.cos(1/t)
for k in range(0, 4):
    assert sp.simplify(sp.diff(e, t, k) - (A*sp.sin(1/t) + B*sp.cos(1/t))) == 0
    print('cos', k, 'A =', A, '| B =', B)
    A, B = sp.expand(sp.diff(A, t) + B / t**2), sp.expand(sp.diff(B, t) - A / t**2)
print('ok')
