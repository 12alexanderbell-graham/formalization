"""Symbolic check of the identities used in REPORT.md.
System: f' = p, p' = q, q' = -K f q - 1 + p^2,  L' = K f L  (L = Lambda = exp(K int_0 f)),
        M' = 2 f M (M = exp(2 int_0 f)).  r := q' expressed as a polynomial."""
import sympy as sp
f, p, q, K, L, M = sp.symbols('f p q K Lambda M')
r = -K*f*q - 1 + p**2                       # q'
def d(expr):                                 # total eta-derivative along the flow
    return sp.expand(sp.diff(expr, f)*p + sp.diff(expr, p)*q + sp.diff(expr, q)*r
                     + sp.diff(expr, L)*K*f*L + sp.diff(expr, M)*2*f*M)
checks = {
  "E  = q^2/2 - p^3/3 + p ;  E' = -K f q^2":            (q**2/2 - p**3/3 + p,      -K*f*q**2),
  "Phi = L (f r - p q) ;  Phi' = -L q (q + 2(K-1) f p)": (L*(f*r - p*q),            -L*q*(q + 2*(K-1)*f*p)),
  "R  = L r ;  R' = (2-K) L p q":                         (L*r,                      (2-K)*L*p*q),
  "Om = M (p^2 - 1 - 2 f q) ;  Om' = 2(K-2) M f^2 q":     (M*(p**2 - 1 - 2*f*q),     2*(K-2)*M*f**2*q),
  "r' = -K f r - (K-2) p q":                              (r,                        -K*f*r - (K-2)*p*q),
}
ok = True
for name, (expr, claimed) in checks.items():
    good = sp.simplify(d(expr) - sp.expand(claimed)) == 0
    ok &= good
    print(("OK  " if good else "FAIL"), name)
print("all identities verified" if ok else "SOME IDENTITY FAILED")
