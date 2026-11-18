"""Exact rational interval check of the Einstein-de Sitter witnesses (run 2026-11-18T0628Z).
Prints, per witness and source, the bounds used in the Lean proofs and checks the band conditions
0.98 * Pu <= dl and du <= 1.02 * Pl.  Lean re-checks every number; this only chooses them."""
from fractions import Fraction as F
import math
s2l, s2u = F('1.41421'), F('1.41422')
vb = {1: (F('0.8408'), F('0.8409')), 3: (F('0.5946'), F('0.5947')), 5: (F('0.4204'), F('0.4205'))}
Zc = {1: 1, 3: 2, 5: 4}          # Z = Zc * sqrt 2
kk = {1: F(1, 2), 3: F(3, 2), 5: F(5, 2)}
ll, lu = F('0.30101'), F('0.30105')
Ll, Lu = F('2.30249'), F('2.30268')
def dist(i):
    vl, vu = vb[i]
    return 3 * Zc[i] * s2l * (1 - vu), 3 * Zc[i] * s2u * (1 - vl)
def Bb(a2, a3, i):
    k = kk[i]; lo = k * ll; hi = k * lu
    for c, n in ((a2 * k**2, 2), (a3 * k**3, 3)):
        lo += c * (ll**n if c >= 0 else lu**n)
        hi += c * (lu**n if c >= 0 else ll**n)
    return lo, hi
def down(x, d=6): return F(math.floor(x * 10**d), 10**d)
def up(x, d=6): return F(math.ceil(x * 10**d), 10**d)
W = {'fit17': (F(47, 4), F(9, 2), F('2.1832'), (3, 5)),
     'fit18': (F(171, 4), F(-23), F('3.5495'), (1, 5)),
     'fit19': (F(8), F(-21, 4), F('1.0706'), (1, 3)),
     'fit9': (F(1, 2), F(7, 2), F('0.5895'), (1, 3, 5)),
     'rl11': (F('3.45'), F('1.66'), F('0.7993'), (1, 5))}
def main():
    ok = True
    for name, (a2, a3, H, keep) in W.items():
        print(name, 'a2', a2, 'a3', a3, 'H', H)
        for i in (1, 3, 5):
            Bl, Bu = Bb(a2, a3, i); Bl, Bu = down(Bl), up(Bu)
            print(f'  B{i} in [{float(Bl)}, {float(Bu)}]', 'pos' if Bl > 0 else 'NOT POS')
            if i in keep:
                dl, du = dist(i); dl, du = down(dl), up(du)
                Pl, Pu = Ll / H * Bl, Lu / H * Bu
                c1 = F(98, 100) * Pu <= dl; c2 = du <= F(102, 100) * Pl
                ok &= c1 and c2 and Bl > 0
                print(f'    d{i} in [{float(dl)}, {float(du)}]  y in [{float(dl/Pu):.5f}, {float(du/Pl):.5f}]', c1, c2)
    print("ALL OK" if ok else "FAIL")


if __name__ == '__main__':
    main()
