Category: wrong-number (printed values attached to wrong parameter)
Reader would wrongly believe: F10 Printed line, "η₂₀ ≃ −0.12[src]ε, 0.15[src]ε and η₃₀ ≃ 4[src]ε, −0.18[src]ε at Ω = 0.041[src], 0.25[src]": that the review prints η₂₀ = -0.12ε at Ω = 0.041 and +0.15ε at Ω = 0.25.
Why it is false: the clean line pairs 0.15 with Ω = 0.041 and -0.12 with Ω = 0.25 (the two printed η₂₀ values are swapped relative to their Ω; the η₃₀ pair is untouched). The Plain-words and Scope lines then read inconsistently with the table in the source. [src] values are only checked by baseline membership (src F10 -0.12 and 0.15 are both baselined), not bound to a row or a parameter; F10 certified blocks (F10_eta) concern the corrected coefficients, not the printed numbers.
Expected: ACCEPTED.
