"""Feasibility (float, run 2026-11-05T0428Z) of a certified LOWER bound F >= c for the profiled
oLCDM chi^2 of Moresco 2016 Table 4 over boxes of (Om, OL).
F = gamma - beta^2/alpha, alpha = w0 + sum w_i y_i (linear), beta = w0*73 + sum w_i H_i sqrt(y_i).
On a box: sqrt(y) <= (y + s^2)/(2s) (any s > 0) makes beta <= L(Om, OL) linear; then
L^2 - (gamma - c) alpha is convex, so checking it <= 0 at the 4 corners proves F >= c on the box
(given y >= 0 on the box). Adaptive bisection; reports the number of boxes."""
import math, sys
T = [(0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
 (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
 (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2), (0.44497, 92.8, 12.9),
 (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12),
 (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17),
 (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]
w0 = 1/2.4**2
gamma = w0*73**2 + sum(h*h/s/s for z, h, s in T)
def y(z, m, l): return (1+z)**2*(1+m*z-l) + l
def alpha(m, l): return w0 + sum(y(z, m, l)/s/s for z, h, s in T)
def ok(box, c):
    m0, m1, l0, l1 = box
    mc, lc = (m0+m1)/2, (l0+l1)/2
    corners = [(m0, l0), (m0, l1), (m1, l0), (m1, l1)]
    # y >= 0 on the box (linear: corners)
    # y >= 0 is needed only at the point itself (hypothesis), not on the whole box;
    # a box on which some y_i < 0 everywhere (all corners) contains no admissible point
    if any(all(y(z, m, l) < 0 for m, l in corners) for z, h, s in T): return True
    sv = [math.sqrt(max(y(z, mc, lc), 0.01)) for z, h, s in T]
    def L(m, l): return w0*73 + sum(h/s/s*(y(z, m, l)+si*si)/(2*si) for (z, h, s), si in zip(T, sv))
    return all(L(m, l)**2 <= (gamma - c)*alpha(m, l) for m, l in corners)
def run(c, region, maxn=200000):
    todo, done, bad = [region], 0, 0
    while todo:
        b = todo.pop()
        r = ok(b, c)
        if r: done += 1; continue
        m0, m1, l0, l1 = b
        if (m1-m0) < 1e-4 or done+len(todo) > maxn:
            bad += 1; continue
        if r is None and (m1-m0) < 1e-3: bad += 1; continue
        if m1-m0 >= (l1-l0)/2:
            mm = (m0+m1)/2; todo += [(m0, mm, l0, l1), (mm, m1, l0, l1)]
        else:
            lm = (l0+l1)/2; todo += [(m0, m1, l0, lm), (m0, m1, lm, l1)]
    return done, bad
c = float(sys.argv[1]) if len(sys.argv) > 1 else 14.96
for reg in [(-1.0,1.0,0.0,4.0)]: print(c, reg, run(c, reg))
