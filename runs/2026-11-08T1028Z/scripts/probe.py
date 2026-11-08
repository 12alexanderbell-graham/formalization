import sys; sys.path.insert(0, '.')
from gen_ball import run
from fractions import Fraction as Fr
mode = sys.argv[1]
for d in [Fr(1,10**10), Fr(1,10**8), Fr(1,10**6), Fr(1,10**4), Fr(1,100), Fr(1,10), Fr(1,2)]:
    A0 = Fr('1.2325876568') if mode == 'under' else Fr('1.2325876569')
    A = A0 - d if mode == 'under' else A0 + d
    best = None
    for k in range(1, 40):
        r = d / 2 ** k
        ok, cells, info = run(A, r, Fr(15, 2), 8, 12, 20, Fr(1, 2), Fr(2), mode)
        if ok: best = (k, len(cells), info); break
    print(float(d), best, flush=True)
