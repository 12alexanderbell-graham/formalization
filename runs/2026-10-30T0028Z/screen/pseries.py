"""Truncated power series as coefficient lists (fast, exact sympy coefficients)."""
import sympy as sp
class PS:
    def __init__(s, c, n): s.n=n; s.c=[sp.expand(x) for x in (list(c)+[0]*n)[:n]]
    def __add__(s,o): o=o if isinstance(o,PS) else PS([o],s.n); return PS([a+b for a,b in zip(s.c,o.c)],s.n)
    __radd__=__add__
    def __neg__(s): return PS([-a for a in s.c],s.n)
    def __sub__(s,o): return s+(-o if isinstance(o,PS) else PS([-o],s.n))
    def __rsub__(s,o): return (-s)+o
    def __mul__(s,o):
        if not isinstance(o,PS): return PS([a*o for a in s.c],s.n)
        r=[0]*s.n
        for i,a in enumerate(s.c):
            if a==0: continue
            for k in range(s.n-i): r[i+k]+=a*o.c[k]
        return PS(r,s.n)
    __rmul__=__mul__
    def inv(s):   # 1/s, s.c[0]!=0
        b=[0]*s.n; b[0]=1/s.c[0]
        for k in range(1,s.n): b[k]=sp.expand(-sum(s.c[i]*b[k-i] for i in range(1,k+1))/s.c[0])
        return PS(b,s.n)
    def compose(s,o):  # s(o(x)), o.c[0]==0
        r=PS([s.c[-1]],s.n)
        for a in reversed(s.c[:-1]): r=r*o+a
        return r
    def revert(s):     # inverse series, s.c[0]==0, s.c[1]!=0
        # Newton-free: order-by-order
        b=[0,1/s.c[1]]+[0]*(s.n-2); x=sp.Symbol('_x')
        for k in range(2,s.n):
            t=PS(b[:k]+[0]*(s.n-k),s.n); comp=s.compose(t)
            b[k]=sp.expand(-comp.c[k]/s.c[1])
        return PS(b,s.n)
    def integ(s): return PS([0]+[s.c[i]/(i+1) for i in range(s.n-1)],s.n)
    def expr(s,v): return sum(c*v**i for i,c in enumerate(s.c))
