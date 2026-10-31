"""Referee: an explicit rational certificate of the kind a Lean proof can check with norm_num + log bounds.
At pi in {pi_lo, pi_hi} = {0.200455, 0.200465} (reduced, x = v/b, g(x) = (28/5)/(x-1) - 27/x^2):
  * short decimal brackets [a1,b1] for x1 (on (1, x_min)) and [a3,b3] for x3 (on (x_max, oo)) of c_pi = 0,
    checked by exact sign evaluation of c_pi(x) = 5 pi x^3 - (5 pi + 28) x^2 + 135 x - 135;
  * F(pi_lo) >= G(a3) - G(b1) - pi(a3 - b1) - (b1 - a1)(pi - g(b1))   (> 0 needed)
    F(pi_hi) <= G(b3) - G(a1) - pi(b3 - a1) + (b3 - a3)(pi - g(b3))   (< 0 needed)
    with G(x) = (28/5) log(x-1) + 27/x; justification in the report (x1 minimises, x3 maximises
    Phi(s,t) = int_s^t (g - pi)).  Only two logs per bound, i.e. log((a3-1)/(b1-1)) etc.
"""
from fractions import Fraction as Q
from mpmath import iv, mp, nstr
iv.prec = 200
from mpmath import mp as _mp
lo_ = lambda X: _mp.make_mpf(X._mpi_[0]); hi_ = lambda X: _mp.make_mpf(X._mpi_[1])
cub = lambda pi, x: 5*pi*x**3 - (5*pi + 28)*x**2 + 135*x - 135
g = lambda x: Q(28, 5)/(x - 1) - Q(27)/x**2
def ivq(q): return iv.mpf(q.numerator)/iv.mpf(q.denominator)
def G(X): return iv.mpf(28)/5*iv.log(X - 1) + 27/X

cases = {
 "lo": (Q(200455, 10**6), Q("1.40157954"), Q("1.40157955"), Q("23.4339173"), Q("23.4339174")),
 "hi": (Q(200465, 10**6), Q("1.40157888"), Q("1.40157889"), Q("23.4324746"), Q("23.4324747")),
}
for k, (pi, a1, b1, a3, b3) in cases.items():
    s = [cub(pi, x) for x in (a1, b1, a3, b3)]
    assert s[0] < 0 < s[1] or s[0] > 0 > s[1], s
    assert s[2] * s[3] < 0, s
    print(k, "pi =", pi, " signs c(a1),c(b1),c(a3),c(b3):", [1 if t > 0 else -1 for t in s])
    if k == "lo":
        B = G(ivq(a3)) - G(ivq(b1)) - ivq(pi)*(ivq(a3) - ivq(b1)) - ivq((b1 - a1)*(pi - g(b1)))
        print("   lower bound for F(pi_lo):", nstr(lo_(B), 10), "(> 0)")
        print("   log argument (a3-1)/(b1-1) =", float((a3 - 1)/(b1 - 1)))
    else:
        B = G(ivq(b3)) - G(ivq(a1)) - ivq(pi)*(ivq(b3) - ivq(a1)) + ivq((b3 - a3)*(pi - g(b3)))
        print("   upper bound for F(pi_hi):", nstr(hi_(B), 10), "(< 0)")
        print("   log argument (b3-1)/(a1-1) =", float((b3 - 1)/(a1 - 1)))
# accuracy needed for log: |F| margins ~ 7.6e-5 and 1.4e-4, divided by 28/5
print("required absolute accuracy of the log term: ~", 7.6e-5/5.6)
