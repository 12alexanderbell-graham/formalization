# Notes (blind reading, second issue)

Answers: A=0, B=1, C=2; D=2*k, E=2*k+1, F=2*k+2, G=2*k+3; H=I=J=2; K=2*k+2, L=2*k+3, M=2*k+2, N=2*k+3.

Indices: lamT 0 = first max, 1 = first min, 2 = second max, ... so the (k+1)-th max is 2k, (k+1)-th min is 2k+1, (k+2)-th max 2k+2, (k+2)-th min 2k+3.

Singular solution u=-2 log r in 3D: u'=-2/r, u''=2/r^2, Lap u = u''+(2/r)u' = -2/r^2; e^u = r^-2; so -2/r^2 + lambda r^-2 = 0 gives lambda = 2. H=I=J=2 (maxima decrease to 2 from above, minima increase to 2 from below; the equation L + 2*exp v = 0).

Counting: N(lambda) = number of radii s with Lambda(s)=lambda. Lambda rises 0 -> max0, falls to min1, rises to max2, ... converging to 2.
- Fall band, lam_{2k+2} < lambda < lam_{2k} (so lambda > 2): crossings on rise to max0 (1), then fall+rise for each of minima/maxima pairs 1..k (2k), then fall to min 2k+1 (1); the next max lam_{2k+2} is below lambda and later values stay below. Total 2k+2. (k=0: 2.)
- lambda = lam_{2k+2}: the 2k+2 crossings above plus one touching point at that max; later values strictly smaller. Total 2k+3.
- lambda = lam_{2k+1} (a minimum): rise to max0 (1), 2k crossings for pairs, touch at min 2k+1 (1); later values strictly larger. Total 2k+2.
- Rise band, lam_{2k+1} < lambda < lam_{2k+3} (lambda < 2): rise (1), fall+rise through minima 1,3,...,2k+1 (2k+2); later minima exceed lambda. Total 2k+3.

Unsure: relied on strictness of later extrema (maxima strictly decreasing, minima strictly increasing) implied by the stated facts (each extremum is the strict-or-not global extremum on its tail; I assumed ties do not recur). No numerical check run.
