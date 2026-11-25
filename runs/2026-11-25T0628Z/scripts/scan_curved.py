# Float scan: l19_sq_curved hypotheses 1 (1/10 <= Omega) and 8 (1 <= Omega0). Difference m5 - m3 (statement: > 1/4).
import mpmath as mp
l = mp.log10(2)
z3, z5 = 2*mp.sqrt(2)-1, 4*mp.sqrt(2)-1
def P(z, a2=3.075, a3=4.466, a4=-3.716):
    x = mp.log10(1+z); return x + a2*x**2 + a3*x**3 + a4*x**4
def dL(Om, O0, z):
    E = lambda y: mp.sqrt(Om*(1+y)**3 + (1-O0)*(1+y)**2 + O0 - Om)
    chi = mp.quad(lambda y: 1/E(y), [0, z]); k = O0 - 1   # K/(H0 a0)^2 = O0 - 1 (H0=a0=1)
    if k > 0: T = mp.sin(mp.sqrt(k)*chi)/mp.sqrt(k)
    elif k < 0: T = mp.sinh(mp.sqrt(-k)*chi)/mp.sqrt(-k)
    else: T = chi
    return (1+z)*T
def diff(Om, O0):
    zz = mp.linspace(0, z5, 400)
    if min(Om*(1+y)**3 + (1-O0)*(1+y)**2 + O0 - Om for y in zz) <= 0: return 'unreachable'
    return 5*mp.log10(dL(Om,O0,z5)/P(z5)) - 5*mp.log10(dL(Om,O0,z3)/P(z3))
for Om in [0.1, 0.05, 0.0, -0.05, -0.1, -0.2]:
    print("O0=1 Om", Om, diff(Om, 1))
for O0 in [1, 0.9, 0.7, 0.5, 0.2, 0.0, -0.5, -1, -3]:
    for Om in [0.1, 0.3, 1]:
        try: print("O0", O0, "Om", Om, diff(Om, O0))
        except Exception as e: print("O0", O0, "Om", Om, "err", e)
