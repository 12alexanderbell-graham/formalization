# Method A: float64 DOP853 on autonomous Emden variables t=log xi, z=w+2t, y=xi*w'
# m = (-y) e^{z/2} / sqrt(4 pi); extrema where y^2 = 2 e^z.
import numpy as np
from scipy.integrate import solve_ivp

def series(xi, K=40):
    # w = sum a_k x^k, x = xi^2 ; e^w = sum b_k x^k ; a_k = -b_{k-1}/(2k(2k+1))
    a = [0.0]*(K+1); b = [0.0]*(K+1); b[0] = 1.0
    for k in range(1, K+1):
        a[k] = -b[k-1]/(2*k*(2*k+1))
        b[k] = sum(j*a[j]*b[k-j] for j in range(1, k+1))/k
    x = xi*xi
    w = sum(a[k]*x**k for k in range(K+1))
    dw = sum(2*k*a[k]*xi**(2*k-1) for k in range(1, K+1))
    return w, dw

xi0 = 0.1
w0, dw0 = series(xi0)
t0 = np.log(xi0)
Y0 = [w0 + 2*t0, xi0*dw0]

def f(t, Y):
    z, y = Y
    return [y + 2, -y - np.exp(z)]

def ev(t, Y):
    z, y = Y
    return y*y - 2*np.exp(z)

def mass(Y):
    return -Y[1]*np.exp(Y[0]/2)/np.sqrt(4*np.pi)

T1 = np.log(1e7)
sol = solve_ivp(f, (t0, T1), Y0, method='DOP853', rtol=1e-13, atol=1e-14,
                events=ev, dense_output=True)
print("extrema (xi, m, contrast, kind):")
for te, Ye in zip(sol.t_events[0], sol.y_events[0]):
    xi = np.exp(te); w = Ye[0] - 2*te
    print(f"  xi={xi:.12g}  m={mass(Ye):.14g}  contrast={np.exp(-w):.10g}")
Yend = sol.y[:, -1]
print("m(1e7)=", mass(Yend), " sqrt(2/pi)=", np.sqrt(2/np.pi))
# V at xi=300000
Y3 = sol.sol(np.log(3e5)); v = -Y3[1]; u = np.exp(Y3[0])/v
V = (u-1-np.log(u)) + (v-2-2*np.log(v/2))
print("u,v,V(3e5) =", u, v, V)
