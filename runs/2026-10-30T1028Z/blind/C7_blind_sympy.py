# C7 blind: angular-diameter distance y-series coefficients D^k_{A,y}, general K.
# Kinematic: a(t)/a0 Taylor to 5th order; x = H0 (t0 - t); c = H0 = 1 units handled via Ok = Omega0 - 1.
import sympy as sp
x, y, q, j, s, l, Om, X = sp.symbols('x y q j s l Omega0 X')
N = 6  # need d_A/y to y^4, i.e. d_A to y^5
A = 1 - x - q*x**2/2 - j*x**3/6 + s*x**4/24 - l*x**5/120   # a(t0-T)/a0, x = H0 T
# chi * a0 H0 / c = int_0^x dx'/A
invA = sp.series(1/A, x, 0, N).removeO()
Xs = sp.integrate(invA, x)
Ok = Om - 1   # = K c^2/(H0^2 a0^2)
# a0 S_K(chi) * H0/c = X - Ok X^3/6 + Ok^2 X^5/120 + ...   (K^2 = 1 for K = +-1; exact for K = 0)
SK = Xs - Ok*Xs**3/6 + Ok**2*Xs**5/120
dA = sp.expand(sp.series(A*SK, x, 0, N).removeO())   # H0 d_A / c as series in x
# invert y = 1 - A(x)
yx = sp.expand(1 - A)
# x = sum c_k y^k
cs = sp.symbols('c1:6')
xy = sum(cs[k]*y**(k+1) for k in range(5))
eq = sp.expand(sp.series(yx.subs(x, xy), y, 0, N).removeO() - y)
sol = sp.solve([eq.coeff(y, k) for k in range(1, N)], cs, dict=True)[0]
xy = xy.subs(sol)
dAy = sp.expand(sp.series(dA.subs(x, xy), y, 0, N).removeO())
D = [sp.factor(sp.expand(dAy.coeff(y, k+1))) for k in range(5)]
printed = [
    sp.Integer(1),
    -sp.Rational(1,2)*(1+q),
    -sp.Rational(1,6)*(-q - 3*q**2 + j + Om),
    -sp.Rational(1,24)*(-2*q + 3*q**2 + 15*q**3 - j - 10*q*j - s + 2*Om),
    -sp.Rational(1,120)*(1 - 6*q + 9*q**2 - 15*q**3 - 105*q**4 + 10*q*j + 105*q**2*j + 15*q*s
                         - 3*j - 10*j**2 + s + l + 5*Om),
]
for k in range(5):
    print(f"D{k}_Ay correct  =", sp.expand(D[k]))
    print(f"D{k}_Ay printed  =", sp.expand(printed[k]))
    print(f"   printed-correct =", sp.factor(sp.expand(printed[k]-D[k])))
# also in the "-(1/n!)(...)" form
for k in range(2,5):
    f = sp.factorial(k+1) if k>0 else 1
    print(f"-{f}*D{k}_correct =", sp.expand(-sp.factorial(k+1)*D[k]))

# --- exact model checks ---
z = sp.symbols('z')
def check(name, dA_exact_of_y, subsd):
    ser = sp.series(dA_exact_of_y/y, y, 0, 5).removeO()
    print(name)
    for k in range(5):
        ex = sp.nsimplify(sp.expand(ser.coeff(y, k)))
        cor = sp.simplify(D[k].subs(subsd)); pr = sp.simplify(printed[k].subs(subsd))
        print(f"  k={k}: exact={ex}  correct={cor}  printed={pr}  ok={sp.simplify(ex-cor)==0}")
# Milne a = c t, K = -1: H0 = 1/t0, a0 = c t0 => Omega0 = 0; q=j=s=l=0. d_A H0/c = y(1-y/2)
w = sp.symbols('w', positive=True)  # w = 1+z = 1/(1-y)
dA_milne = (sp.sinh(sp.log(w))/w).subs(w, 1/(1-y))
check("Milne (K=-1, a=ct)", sp.simplify(dA_milne.rewrite(sp.exp)), {q:0,j:0,s:0,l:0,Om:0})
# closed coasting a = c t, K = +1: Omega0 = 2; d_A H0/c = sin(ln(1+z))/(1+z)
dA_cc = (sp.sin(sp.log(w))/w).subs(w, 1/(1-y))
check("closed coasting (K=+1, a=ct)", dA_cc, {q:0,j:0,s:0,l:0,Om:2})
# de Sitter flat a = e^{Ht}: q=-1, j=1, s=1, l=1, Om=1; chi = z/(a0 H), d_A H/c = z/(1+z) = y
check("flat de Sitter", y, {q:-1,j:1,s:1,l:1,Om:1})
# Einstein-de Sitter a ~ t^(2/3), K=0: q=1/2, j=1, s=-7/2, l=35/2; d_A H0/c = 2(1-1/sqrt(1+z))/(1+z) = 2(1-y)(1-sqrt(1-y))
check("EdS (K=0)", 2*(1-y)*(1-sp.sqrt(1-y)), {q:sp.Rational(1,2),j:1,s:-sp.Rational(7,2),l:sp.Rational(35,2),Om:1})
# closed with nonzero q etc: a(t) = sin-type? use a = c*t^p? generic check: K=+1, a = t^2 (c=1): numeric
p = sp.Rational(2)
t, t0 = sp.symbols('t t0', positive=True)
a = t**p
H0 = p/t0; qv = -(p*(p-1))/p**2; jv = p*(p-1)*(p-2)/p**3; sv = p*(p-1)*(p-2)*(p-3)/p**4; lv = p*(p-1)*(p-2)*(p-3)*(p-4)/p**5
# K=+1, c=1, t0 chosen: Omega0 = 1 + 1/(H0^2 a0^2)
t0v = sp.Rational(3,2)
a0 = t0v**p; H0v = p/t0v
Omv = 1 + 1/(H0v**2*a0**2)
# chi(t) = int_t^t0 dt'/t'^2 = 1/t - 1/t0 ; 1+z = (t0/t)^2 => t = t0*sqrt(1-y)
tt = t0v*sp.sqrt(1-y)
chi = 1/tt - 1/t0v
dA_ex = H0v * (tt/t0v)**p * a0 * sp.sin(chi)
check("closed a=t^2, t0=3/2, K=+1", dA_ex, {q:qv,j:jv,s:sv,l:lv,Om:Omv})
