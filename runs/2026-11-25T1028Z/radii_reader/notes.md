# Notes (radii_reader)

Reasoning (from the brief only, no literature lookup):
- Singular solution w0 = log(lambda_inf / s^2): w0'' + (2/s) w0' + e^{w0} = 2/s^2 - 4/s^2 + lambda_inf/s^2 = 0, so lambda_inf = 2. Hence C = 2.
- lambda = s^2 e^w, so P = 2.
- Linearise w = w0 + v: v'' + (2/s) v' + (2/s^2) v = 0. Try v = s^a: a^2 + a + 2 = 0, a = (-1 +- i sqrt 7)/2. So v ~ s^{-1/2} cos((sqrt 7 / 2) ln s + phase), and lambda - 2 ~ 2v has the same form.
- Turning points of lambda (zeros of lambda') are spaced by half a period in ln s: pi / (sqrt 7 / 2) = 2 pi / sqrt 7. Consecutive turning points alternate max/min, so the next one (step A = 1) gives ratio -> exp(2 pi / sqrt 7). B = 2, N = 7.
- Deviation quotient: next/current deviation -> -exp(-pi/sqrt 7) (sign flips, amplitude decays like s^{-1/2}); not needed for the template, only C and P.
- M: seventh turning point counting the first as the first has ζ-index 6 (ζ indexed from 0), so M = 6.

Unsure of:
- Whether the intended lower bound uses "from the seventh turning point" as index 6 (my reading) versus 7; I followed the brief's literal counting.
- Not numerically verified (no Python run); the derivation is standard linearisation.
- Whether A = 1 is intended vs A = 2 (full period); I read "next turning point" literally as A = 1, which is why B = 2 and not 4 (full period would be 4 pi / sqrt 7).
