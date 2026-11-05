# NOTES_B — Bamba et al., arXiv:1205.3421 (v1, v2, v3 all checked from rendered pages)
Pages: v1 107/108/111/113; v2 108/109/112-114; v3 110/111/114/116. Images read: v3 all items; v1 pp.107,108,111,113; v2 p.109
(v2 other pages only via pdftotext for (11.13); contents of equations seen identical in all images read). No differences found between versions
in these equations (only equation placement/page numbers differ).

## Series
1. d_L(z), (10.38): printed `d_L(z) = (cz/H0) { D0_L + D1_L z + D2_L z^2 + D3_L z^3 + D4_L z^4 + O(z^5) }`. Prefactor z^1 -> 1; last 4.
2. d_A(z), (10.45): same shape with D_A. Prefactor 1; last 4.
3. d_L in y, (10.52)-(10.57): the series itself is NOT printed, only D^0..D^4_{L,y} (D^4 split over (10.56)-(10.57)). Implied
   d_L = (c y/H0){sum D^n_{L,y} y^n}: prefactor 1, last 4. Reason/check: z=y/(1-y), d_L=(c/H0)z(1+(1-q0)/2 z) = (c/H0) y (1+(3-q0)/2 y), and printed D1_{L,y} = -1/2(-3+q0) agrees.
4. d_A in y, (10.58)-(10.63): likewise not printed; implied prefactor 1, last 4. Check: d_A=(c/H0)z(1-(3+q0)/2 z) -> y(1-(1+q0)/2 y); printed D1_{A,y} = -1/2(1+q0). OK.

Curvature: z-series (10.41)-(10.44),(10.48)-(10.51) are for arbitrary K, explicit terms K c^2/(H0^2 a0^2) (and `a0^2 H0^2` in 10.44/10.51).
y-series coefficients use Omega_0 = 1 + K c^2/(H0^2 a0^2) (defined on p.107/110/111 just before (10.52)); text says "derived for any value of the curvature parameter".
(Omega_0 also written 1 - Omega_K^(0) = Omega_m+Omega_r+Omega_X.)

## Item 5, (11.13), identical in v1-v3
d^3R0/dt^3 = -6 H0^5 [ l0 - s0 + 2(q0+4) j0 - 6(3q0+8) q0 - 24 ].  Transcribed as printed.
Internal check (not a reading issue): (11.10)-(11.12) give 0 for de Sitter (q=-1, j=s=l=1: 11.11: 0; 11.12: 1+1-8+6=0) but (11.13) gives
bracket 1-1+6+30-24 = 12 != 0, so the printed (11.13) appears to be wrong in the paper (or l/s conventions differ). Not corrected in bambaR3.

## Item 6, (11.21): shape MATCHES the assumed shape
Printed: F(R0)/(6 H0^2) = - ( P0(q0,j0,s0,l0) Omega_M + Q0(q0,j0,s0,l0) ) / R(q0,j0,s0,l0).
So c=6, p=2, s=-1. Omega_M printed without superscript (0) in (11.21) (the text elsewhere uses Omega_M^(0)). R is calligraphic, defined (11.31).
Same in v1, v2, v3. (11.23)/(11.24) use LHS F''/(6H0^2)^{-1}, F'''/(6H0^2)^{-2} — not asked.

Lean file compiles (only a deprecation warning on the Mathlib import).
Crops: crop_v3_*.png (v3 pages 110, 111, 114, 116).
