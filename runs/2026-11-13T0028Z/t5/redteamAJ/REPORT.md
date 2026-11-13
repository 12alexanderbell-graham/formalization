# Red team AJ report

All six edit only FINDINGS.md (one exact replacement each). On a copy with check_numbers --write and make_packet applied, check_numbers, check_findings (FB1-FB6), check_status_lines, check_source_names, check_source_variants, check_prose, check_necessity_prose and make_packet --check all stay green (no LEDGER line, no certified pair, no baseline line changed). Not run: Lean-dependent steps, and the --base steps (nothing they diff is touched).

- d01 -> weakened-statement (class) -> F12 Scope says the caption is false in every class of solutions, not only the exponential-approach class -> "the caption is false for every zero-wall-shear solution, whatever its approach ... exponential or algebraic" -> ACCEPTED (FB6 reads only the Correct line)
- d02 -> misleading-record (source) -> F13 swaps the printed values of Asaithambi 2005 and Salama 2004 -> "0.005226 (Asaithambi 2005) ... 0.005225 (Salama 2004)" -> ACCEPTED (FB2 only checks the side of the window)
- d03 -> wrong-number -> F1 Correct m₀ cubic coefficient 81/4 changed to 81/2 -> "- (81/2)Ω_m³" in the Correct line -> ACCEPTED (fractions unread)
- d04 -> verified status overstated -> F4 claims Lean covers all curvatures -> "Lean covers every curvature, flat and curved (... machine-checked for all K)" -> ACCEPTED
- d05 -> uniqueness/strength -> F14 says the reverse-flow branch is unique (proved) -> "the reverse-flow branch is unique (proved) ..." -> ACCEPTED (FB5 reads only parentheticals after a cited headline; record is existence only)
- d06 -> wrong-number (row/parameter) -> F10 swaps the printed η₂₀ values between Ω = 0.041 and 0.25 -> "η₂₀ ≃ −0.12[src]ε, 0.15[src]ε ... at Ω = 0.041[src], 0.25[src]" -> ACCEPTED (baseline is by value, not by position)
