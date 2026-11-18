# Notes: Bonnor-Ebert sphere counts (blind reading, no numerics run)

Indexing: xi 0 = 1st max, xi 1 = 1st min, xi 2 = 2nd max, xi 3 = 2nd min, xi 4 = 3rd max. So A=1, B=2, C=3, D=4.
The j-th minimum (j>=1) has index 2j-1; for j=k+2 this is 2k+3. So E = 2*k+3.

Counting: m rises 0 -> M1, falls to m1, rises to M2, falls to m2, ... Maxima M_j are non-increasing and minima m_j non-decreasing. This follows from "largest/smallest from the preceding extremum on". I read the inequalities as strict, as the band statements imply. Both converge to the singular-isothermal-sphere (SIS) mass. Each monotone segment contributes at most one solution, and endpoints are counted once.

- F (mu > M1): 0, since M1 is the global maximum.
- G (M_{k+2} < mu < M_{k+1}): the segments 0->M1 and every fall/rise pair up to M_{k+1} are crossed. That is the first rise, k+1 falls and k rises, so 2k+2. Check k=0: rise, fall = 2.
- H (mu = M_{k+2}): the 2k+2 crossings of the segments up to M_{k+1}, plus the final rise reaching M_{k+2} exactly. Later maxima are strictly lower, so 2k+3. Check k=0: 3.
- I (mu = m_{k+1}): rise, then k+1 falls (the last ends exactly at the minimum) and k rises between, so 2k+2. Later values are strictly above. Check k=0: 2.
- J (m_{k+1} < mu < m_{k+2}): rise to M1, k+1 falls, k+1 rises, and the fall into m_{k+2} stays above mu. That is 1 + (k+1) + (k+1) = 2k+3. Check k=0: 3 (rise, fall, rise).
- K (0 < mu < m1): only the first rise crosses, so 1. Everything after the first minimum is >= m1.

Unsure: the strictness of the monotonicity of maxima and minima across extrema (only needed so that equal-valued bands/ties are not double counted). "Number of radii s >= 0" at s=0 gives m=0, which is excluded since mu>0.
