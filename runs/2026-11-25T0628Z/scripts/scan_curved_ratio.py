# For l19_sq_curved hypotheses 1 and 8: the distance-integral ratio J5/J3 needed (from the 1/4-mag conclusion and the
# printed quartic) against the ratio of Einstein-de Sitter, (1 - w5)/(1 - w3), and the actual J5/J3 (flat/curved,
# transverse factor ignored: sin lowers T5/T3 below J5/J3 for closed models, sinh raises it for open ones).
import mpmath as mp
l = mp.log10(2)
def P(x, a2=3.075, a3=4.466, a4=-3.716): return x + a2*x**2 + a3*x**3 + a4*x**4
x3, x5 = 1.5*l, 2.5*l
need = mp.power(10, 0.05) * P(x5)/P(x3) / 2
w3, w5 = mp.power(2, -0.75), mp.power(2, -1.25)
print("needed T5/T3 >", float(need), " EdS ratio", float((1-w5)/(1-w3)))
def J(Om, O0, w):
    k = 1 - O0
    return mp.quad(lambda v: 2/mp.sqrt(Om + k*v**2 + (1-Om-k)*v**6), [w, 1])
for O0 in [1.1, 1.0, 0.9, 0.5, 0.0, -1, -3, -10, -100]:
    row = []
    for Om in [-0.02, 0.0, 0.05, 0.1, 0.5, 1.0]:
        try:
            k = 1 - O0
            f = lambda v: Om + k*v**2 + (1-Om-k)*v**6
            if min(f(v) for v in mp.linspace(w5, 1, 200)) <= 0: row.append("unreach"); continue
            row.append(f"{float(J(Om,O0,w5)/J(Om,O0,w3)):.3f}")
        except Exception as e: row.append("err")
    print("O0", O0, "Om [-0.02,0,0.05,0.1,0.5,1]:", row)
