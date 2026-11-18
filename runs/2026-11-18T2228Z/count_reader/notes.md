# Notes (blind reading, derived from the brief only)

Indexing: lamT 0 = 1st max, 1 = 1st min, 2 = 2nd max, ... so A=0, B=1, C=2;
(k+1)-th max at 2k, (k+1)-th min at 2k+1, (k+2)-th max at 2k+2, (k+2)-th min at 2k+3.

Singular solution u=-2 log r in 3D: u'=-2/r, u''=2/r^2, Laplacian = u''+2u'/r = -2/r^2, e^u = r^-2,
so -2/r^2 + lam r^-2 = 0 gives lam_s = 2. H = I = J = 2. Maxima > 2 > minima, limit 2.

Counting (M_j maxima decreasing, m_j minima increasing; Lambda segments: up (0,M_0); down M_j->m_j covering (m_j,M_j);
up m_j->M_{j+1} covering (m_j,M_{j+1}); each monotone, so each segment hits a value at most once; shared endpoints counted once):
- lam in (M_{k+1}, M_k): lam>2>all minima. Hit by first up segment (1), down j=0..k (k+1), up j=0..k-1 (k): 2k+2.
- lam = M_{k+1}: the same 2k+2 plus the turning point itself (end of up m_k->M_{k+1}, start of down; one radius): 2k+3.
- lam = m_k: first up (1), down j<k (k), the turning point (1), up j<k (k): 2k+2.
- lam in (m_k, m_{k+1}): first up (1), down j=0..k (k+1), up j=0..k (k+1): 2k+3.
Sanity k=0: (M1,M0): 2; =M1: 3; =m0: 2; (m0,m1): 3.

Unsure: nothing major; relies on the stated facts (monotone segments, extrema ordering). No numerical check run.
