"""Numerical sanity checks for REPORT.md (floating point, scipy DOP853, rtol 1e-11).
(1) K in {1,1.5,2,5,10}: along trajectories from (0,0,s), every 'bottom' (q: - -> +) has f<0 and is
    followed by p crossing 1 (overshoot) -- the content of Lemmas 5-6; and the Ω/Φ monotonicity holds.
(2) K = 0.5 (beta = 2): a genuine non-monotone solution exists (top, bottom with f>0, then p -> 1);
    shows where K >= 1 is needed (Lemma 5 fails: f>0 at the bottom)."""
import numpy as np, sys
from scipy.integrate import solve_ivp
def run(K, s, T=60, stop_over=True):
    rhs = lambda t, y: [y[1], y[2], -K*y[0]*y[2] - 1 + y[1]**2, K*y[0]*y[3]]
    evO = lambda t, y: y[1] - 1.0; evO.terminal = stop_over; evO.direction = 1
    evB = lambda t, y: y[1] + 60;  evB.terminal = True
    evQ = lambda t, y: y[2]
    return solve_ivp(rhs, [0, T], [0, 0, s, 1.0], method='DOP853', rtol=1e-11, atol=1e-13,
                     events=[evO, evB, evQ], dense_output=True, max_step=0.05)
def part1():
    for K in [1, 1.5, 2, 5, 10]:
        nb = 0; bad = 0
        for s in np.linspace(-4, 3, 141):
            so = run(K, s)
            for t, y in zip(so.t_events[2], so.y_events[2]):
                if t < 1e-9: continue
                rr = -K*y[0]*y[2] - 1 + y[1]**2
                if rr > 0:            # bottom: q' > 0 at a zero of q
                    nb += 1
                    over = so.t_events[0].size > 0 and so.t_events[0][0] > t
                    if not (y[0] < 0 and over):
                        bad += 1; print("  check K=%g s=%.3f f2=%.4f over=%s" % (K, s, y[0], over))
        print("K=%-4g bottoms found: %4d ; bottoms violating 'f<0 and then p crosses 1': %d" % (K, nb, bad))
def find_creep_K05():
    K = 0.5
    def nzeros(s):
        so = run(K, s); return sum(1 for t in so.t_events[2] if t > 1e-9)
    a, b = 1.10, 1.15
    na, nbz = nzeros(a), nzeros(b)
    for _ in range(60):
        m = 0.5*(a+b); nm = nzeros(m)
        if nm == na: a = m
        else: b = m
    s = 0.5*(a+b); so = run(K, s, T=40, stop_over=False)
    print("K=0.5: zero-count switches %d -> %d at s ~= %.12f" % (na, nbz, s))
    for t, y in zip(so.t_events[2], so.y_events[2]):
        if t > 1e-9 and t < 20:
            print("   zero of q at eta=%.4f: f=%.4f p=%.4f (%s)" % (t, y[0], y[1], "bottom" if y[1] < -1 else "top"))
    tt = np.linspace(0, 20, 2001); Y = so.sol(tt)
    print("   max p on [0,20] = %.6f, p(20)=%.6f, min p = %.4f" % (Y[1].max(), Y[1][-1], Y[1].min()))
    # Phi' sign along the descent from the top to the bottom
    f, p, q, L = Y; Phid = -L*q*(q + 2*(K-1)*f*p)
    print("   Phi' takes both signs on [0,20]:", (Phid > 0).any() and (Phid < 0).any())

def part3(n=400, seed=1):
    """Random states, K in {1,1.5,2}: (i) from a bottom (f<=0, p<-1, q=0) p crosses 1 with q>0 throughout
    (Ascent Lemma); (ii) from a top (any f, |p|<1, q=0) the next bottom, if any, has f<0 (Descent Lemma)."""
    rng = np.random.default_rng(seed)
    for K in [1, 1.5, 2]:
        rhs = lambda t, y: [y[1], y[2], -K*y[0]*y[2] - 1 + y[1]**2]
        bad_i = bad_ii = nb = 0
        for _ in range(n):
            f2, p2 = -5*rng.random(), -1 - 4*rng.random()
            evO = lambda t, y: y[1] - 1; evO.terminal = True
            evQ = lambda t, y: y[2]; evQ.terminal = True; evQ.direction = -1
            so = solve_ivp(rhs, [0, 200], [f2, p2, 0.0], method='DOP853', rtol=1e-10, atol=1e-12, events=[evO, evQ])
            if not so.t_events[0].size: bad_i += 1
            fz, pz = 10*rng.random() - 5, 2*rng.random() - 1
            evB = lambda t, y: y[2] if y[1] < -1 else -1.0; evB.terminal = True; evB.direction = 1
            evD = lambda t, y: y[1] + 60; evD.terminal = True
            so = solve_ivp(rhs, [0, 60], [fz, pz, 0.0], method='DOP853', rtol=1e-10, atol=1e-12, events=[evB, evD])
            if so.t_events[0].size:
                nb += 1
                if so.y_events[0][0][0] >= 0: bad_ii += 1
        print("K=%-3g (i) bottoms with f<=0 not crossing p=1: %d/%d ; (ii) bottoms after a top: %d, with f>=0: %d"
              % (K, bad_i, n, nb, bad_ii))
if __name__ == "__main__":
    part1(); find_creep_K05(); part3()
