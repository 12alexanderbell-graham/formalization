# Source C6 (verbatim from the typeset PDF, arXiv:1205.3421v3, Sec. X, p. 111)

K. Bamba, S. Capozziello, S. Nojiri, S. D. Odintsov, Astrophys. Space Sci. 342, 155 (2012), arXiv:1205.3421v3.
Crop: `runs/2026-10-30T0828Z/typeset/crop_p111_eq10.54-57_DLy.png` (rendered at 200 dpi in run 0828Z; read again this run).

D³_{L,y} = (1/24) [52 − 20q₀ + 21q₀² − 15q₀³ − 7j₀ + 10q₀j₀ + s₀ − 2Ω₀(1 + 3q₀)] ,   (10.55)
D⁴_{L,y} = (1/120) [359 − 184q₀ + 186q₀² − 135q₀³ + 105q₀⁴ + 90q₀j₀ − 105q₀²j₀ − 15q₀s₀ +   (10.56)
           − 57j₀ + 10j² + 9s₀ − l₀ − 5Ω₀(17 − 6q₀ + 9q₀² − 2j₀)] ,   (10.57)

Context (p. 108, 110; see `runs/2026-10-30T0828Z/source_C5.md`): d_L = [a(t₀)/a(t₀ − D/c)] a(t₀) r₀ (10.26);
r₀ = sin / id / sinh(∫ c dt/a) for K = +1/0/−1 (10.28); Ω₀ = 1 + Kc²/(H₀²a₀²);
"Previous relations have been derived for any value of the curvature parameter."
`j²` (no subscript) in (10.57) read as j₀². The "+" at the end of (10.56) followed by "−57j₀" read as −57j₀.

Claims frozen: `Work/Cosmography/BambaCurved.lean` (BambaD3yClaim, BambaD4yClaim and Past versions), charitable:
corrected D² (F4), and for D⁴ also corrected D³.
