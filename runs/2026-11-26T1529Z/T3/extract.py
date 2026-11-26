#!/usr/bin/env python3
"""Extract AlphaEvolve's rank-48 <4,4,4> decomposition from mathematical_results.ipynb and print the
Lean data lists of T3Check.lean (entries doubled to Gaussian integers). Run 2026-11-26T1529Z.

  python3 -I extract.py <path to mathematical_results.ipynb>

The notebook cell text is numpy literal data; it is parsed with `ast.literal_eval` after removing the
`np.array(` wrappers (no code is executed). Also re-checks the tensor identity exactly in ℤ[i].
"""
import ast, json, re, sys
nb = json.load(open(sys.argv[1]))
cell = next(''.join(c['source']) for c in nb['cells'] if 'decomposition_444 =' in ''.join(c['source']))
body = cell[cell.index('decomposition_444'):]
arrs = re.findall(r'np\.array\((\[.*?\])\s*(?:,\s*dtype=[^)]*)?\)', body, flags=re.S)
assert len(arrs) == 3
mats = [ast.literal_eval(a) for a in arrs]
def g(z):
    z = complex(z); x, y = 2 * z.real, 2 * z.imag
    assert x == round(x) and y == round(y), z
    return (int(round(x)), int(round(y)))
G = [[[g(z) for z in row] for row in M] for M in mats]
assert all(len(M) == 16 and all(len(r) == 48 for r in M) for M in G)
def mul(p, q): return (p[0]*q[0] - p[1]*q[1], p[0]*q[1] + p[1]*q[0])
for a in range(16):
    for b in range(16):
        for c in range(16):
            s = (0, 0)
            for r in range(48):
                t = mul(mul(G[0][a][r], G[1][b][r]), G[2][c][r]); s = (s[0] + t[0], s[1] + t[1])
            T = 8 if (a // 4 == c % 4 and a % 4 == b // 4 and b % 4 == c // 4) else 0
            assert s == (T, 0), (a, b, c, s)
for name, M in zip(['Ud', 'Vd', 'Wd'], G):
    print(name, json.dumps(M))
print('exact tensor check in Z[i]: OK', file=sys.stderr)
