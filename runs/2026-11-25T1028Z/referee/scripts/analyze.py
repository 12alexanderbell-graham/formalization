"""Compare runs A/B/C, print zeta_k, lambda(zeta_k), ratios, margins; then the
hand route of task 3 in exact-ish arithmetic (mpmath, 50 digits, outward rounding
not needed at these margins but the margins are printed)."""
import mpmath as mp

mp.mp.dps = 50


def load(fn):
    rows = []
    for line in open(fn):
        if line.startswith("series"):
            continue
        k, t, u = line.split()
        rows.append((mp.mpf(t), mp.mpf(u)))
    return rows


A, B, C = load("runA.txt"), load("runB.txt"), load("runC.txt")
print("max |diff| between runs (t and u), per k:")
for k in range(len(A)):
    dt = max(abs(A[k][0] - C[k][0]), abs(B[k][0] - C[k][0]))
    du = max(abs(A[k][1] - C[k][1]), abs(B[k][1] - C[k][1]))
    print(k, mp.nstr(dt, 3), mp.nstr(du, 3))

R = C  # 60-digit run
r_lim = mp.exp(2 * mp.pi / mp.sqrt(7))
q_lim = -mp.exp(-mp.pi / mp.sqrt(7))
print("\nexp(2pi/sqrt7) =", mp.nstr(r_lim, 25), "  -exp(-pi/sqrt7) =", mp.nstr(q_lim, 25))
print("\nk  zeta_k  lambda(zeta_k)  lambda-2")
for k, (t, u) in enumerate(R):
    print(k, mp.nstr(mp.exp(t), 25), mp.nstr(2 * u, 25), mp.nstr(2 * u - 2, 12))
print("\nk  zeta_{k+1}/zeta_k  (vs lim)  q_k=(lam_{k+1}-2)/(lam_k-2)  (vs lim)")
for k in range(len(R) - 1):
    rr = mp.exp(R[k + 1][0] - R[k][0])
    q = (R[k + 1][1] - 1) / (R[k][1] - 1)
    flag = ""
    if k >= 6:
        flag = "  margins ratio: %s / %s   q: %s / %s" % (
            mp.nstr(rr - mp.mpf("10.3"), 6), mp.nstr(mp.mpf("11.2") - rr, 6),
            mp.nstr(q + mp.mpf("0.33"), 6), mp.nstr(mp.mpf("-0.28") - q, 6))
    print(k, mp.nstr(rr, 20), mp.nstr(rr - r_lim, 5), mp.nstr(q, 20), mp.nstr(q - q_lim, 5), flag)
print("\nzeta_6 =", mp.nstr(mp.exp(R[6][0]), 15), ">= 300000:", mp.exp(R[6][0]) >= 300000)
print("lambda(zeta_6) =", mp.nstr(2 * R[6][1], 15), "in [2.000873, 2.000980]:",
      mp.mpf("2.000873") <= 2 * R[6][1] <= mp.mpf("2.000980"))

# ---- task 3: route from the segment bounds --------------------------------
print("\n--- route (task 3) ---")
for lam6hi in [mp.mpf("2.000980"), 2 * R[6][1]]:
    x6 = (lam6hi - 2) / 2
    eps = mp.sqrt(8) * x6  # sqrt(Nw(zeta6)) = sqrt(8 x6^2)
    c = mp.sqrt(7) / 2
    Lmin = mp.pi / (c + 16 * eps)
    Lmax = mp.pi / (c - 16 * eps)
    rmin, rmax = mp.exp(Lmin), mp.exp(Lmax)
    # q = -exp(D/2), -(1+36e)L <= D <= -(1-36e)L
    qlo = -mp.exp(-(1 - 36 * eps) * Lmin / 2)
    qhi = -mp.exp(-(1 + 36 * eps) * Lmax / 2)
    print("lambda6 upper used =", mp.nstr(lam6hi, 10), " eps <=", mp.nstr(eps, 10),
          " 16eps =", mp.nstr(16 * eps, 8), " 36eps =", mp.nstr(36 * eps, 8))
    print("  L in [", mp.nstr(Lmin, 12), ",", mp.nstr(Lmax, 12), "]")
    print("  ratio in [", mp.nstr(rmin, 12), ",", mp.nstr(rmax, 12), "]  margins vs [10.3,11.2]:",
          mp.nstr(rmin - mp.mpf("10.3"), 6), mp.nstr(mp.mpf("11.2") - rmax, 6))
    print("  q in [", mp.nstr(qlo, 12), ",", mp.nstr(qhi, 12), "]  margins vs [-0.33,-0.28]:",
          mp.nstr(qlo + mp.mpf("0.33"), 6), mp.nstr(mp.mpf("-0.28") - qhi, 6))
    # largest lambda6 for which all four stated bounds still follow
for name, f in [("ratio upper 11.2", lambda e: mp.pi / (mp.sqrt(7) / 2 - 16 * e) - mp.log(mp.mpf("11.2"))),
                ("ratio lower 10.3", lambda e: mp.log(mp.mpf("10.3")) - mp.pi / (mp.sqrt(7) / 2 + 16 * e)),
                ("q lower -0.33", lambda e: mp.exp(-(1 - 36 * e) * mp.pi / (mp.sqrt(7) / 2 + 16 * e) / 2) - mp.mpf("0.33")),
                ("q upper -0.28", lambda e: mp.mpf("0.28") - mp.exp(-(1 + 36 * e) * mp.pi / (mp.sqrt(7) / 2 - 16 * e) / 2))]:
    e = mp.findroot(f, mp.mpf("0.0014"))
    print("critical eps for", name, "=", mp.nstr(e, 10), " => lambda6 <=", mp.nstr(2 + 2 * e / mp.sqrt(8), 10))
