# Does the printed z(T) inversion (264)-(269) invert the printed H(z) (246) [cubic coeff +Q]
# or the correct H(z) [cubic coeff -Q]?  T = -6 H^2 (143).
import cmath, math
q, j, s, H0 = -0.545, 0.776, -0.192, 1.0
Q = -3*q**2*(1+q) + j*(3+4*q) + s
N = (j**3 + 3*j**2*(1+q)*(6+11*q) - 3*j*q**2*(12+q*(29+16*q)) + q**4*(18+q*(36+17*q))
     - 15*q**2*(1+q)*s + 3*j*(5+7*q)*s + 3*s**2)
mu = j**2 + q**2*(6+12*q+7*q**2) - 2*j*(3+7*q+5*q**2) - 2*s*(1+q)
def P(T):
    return (2*H0**2*(6*j**3 - 6*q**2*(2+q*(4+q))**2 + 3*j**2*(8+q*(28+17*q)) + 4*(2+q*(6-q*(3+7*q)))*s
            + 9*s**2 + 2*j*(6*(2+3*s) + q*(52+q*(60-q*(6+17*q)) + 27*s)))
            - 2*cmath.sqrt(-6*T)*H0*(j**3 + 3*j**2*(1+q)*(6+11*q) - 3*j*q**2*(12+q*(29+16*q)) + q**4*(18+q*(36+17*q))
            - 15*q**2*(1+q)*s + 3*j*(5+7*q)*s + 3*s**2) - 3*T*Q**2)
def M(T):
    return H0**2*cmath.sqrt(2*P(T))*Q - 2*H0**3*N + cmath.sqrt(-6*T)*H0**2*Q**2
def zT(T):
    m = M(T)
    return (2*(q**2-j) + (4*m/H0**3)**(1/3) + (16*H0**3/m)**(1/3)*mu)/(2*Q)
H_pr = lambda z: H0*(1 + z*(1+q) + z**2/2*(j-q**2) + z**3/6*Q)       # (246) as printed
H_ok = lambda z: H0*(1 + z*(1+q) + z**2/2*(j-q**2) - z**3/6*Q)       # (165d)/(204), correct
print('Q =', Q, ' mu =', mu)
for z0 in (0.1, 0.5, 1.0):
    for name, Hf in (('printed(246)', H_pr), ('correct', H_ok)):
        T = -6*Hf(z0)**2
        print(f'z={z0} H={name:13s} T={T:.5f}  z(T) from (264) = {zT(T):.6f}')
