"""First-order (in r) prediction of (q_k - L)/(lambda_k - 2) from the half-turn integral."""
import mpmath as mp
mp.mp.dps = 30
s7 = mp.sqrt(7)
def xy(th):
    p, q = mp.cos(th), mp.sin(th)
    x = p / s7; y = (q - p / s7) / 2
    return p, q, x, y
def c1(th):
    p, q, x, y = xy(th); return -4 * x * (4 * x**2 + 4 * x * y - y**2)
def c2(th):
    p, q, x, y = xy(th); return p * (-3 * p**2 + 2 * s7 * p * q + 7 * q**2) / 14
th0 = mp.atan(1 / s7)  # ray y = 0, x > 0
I = mp.quad(lambda th: mp.e ** (-(th - th0) / s7) * (c1(th) / s7 + 2 * c2(th) / 7), [th0, th0 + mp.pi])
L = -mp.e ** (-mp.pi / s7)
print("predicted (q_k-L)/(lambda_k-2) =", mp.nstr(L * mp.sqrt(2) * I, 12))
