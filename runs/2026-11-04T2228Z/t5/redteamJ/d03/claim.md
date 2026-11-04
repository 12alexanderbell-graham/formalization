Category: wrong-number
Reader would wrongly believe: that the van der Waals temperature scale 8a/(27Rb) of CO2 (a = 3.640 L^2 bar/mol^2, b = 0.04267 L/mol) is 311 K to the nearest kelvin (measured Tc = 304.13 K; vdW gives 304 K).
Why it is false: the gas constant in the body is 0.08134 (digits transposed); the correct R = 0.08314 L bar/(mol K) gives 304.0 K, not 311.
Expected: ACCEPTED. Sentence misread: "`tempScale a b` — FORMULA, not pinned ...: is defined as `8 * a / (27 * 0.08134 * b)`" and "`RoundsTo (tempScale 3.640 0.04267) 311 0`"; nothing in CI knows R. Unconditional headline, FORMULA kind, no glossary terms.
