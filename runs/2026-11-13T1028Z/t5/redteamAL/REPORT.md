# Red team AL report (snapshot HEAD 12812446). Each defect tested with scripts/trust/records_check.py 12812446 (all Lean-free CI commands, BASE=HEAD) after check_numbers --write and make_packet: only the baseline failure check_literals.py (2 lines) remained, same as the clean tree. All 6 ACCEPTED.
| d | category | defect | misread line | outcome |
|---|---|---|---|---|
| d01 | weakened-statement | F12 Scope widened: printed beta refuted for every tail class, not only the exponential one | "false for every zero-wall-shear solution ... exponential or algebraic" | ACCEPTED |
| d02 | unregistered | New "### F15a" section (heading dodges `F\d+\b`, so FB1-FB9 skip it): unverified Work-only Bonnor-Ebert candidate presented as verified, "Lean evidence (Checked, CI green)" | F15a Lean evidence / Correct | ACCEPTED (FB8/FB9 aimed) |
| d03 | weakened-statement | F4 (norecord legacy): Lean said to cover every curvature, it covers flat only | "Lean covers the sign for every curvature K" | ACCEPTED (FB8 legacy) |
| d04 | mistranscription | F10 Printed: eta values attached to swapped Omega (0.25 / 0.041) | "at Ω = 0.25[src], 0.041[src]" | ACCEPTED |
| d05 | wrong-number | F11 Scope: absorbing shift l0 -> l0 + 210 q0^4 instead of minus | "l₀ ↦ l₀ + 210q₀⁴" | ACCEPTED |
| d06 | wrong-statement | F14: Correct regenerated legitimately (FB9 passes), Scope now claims reverse branch unique, contradicting cited `fs_neg_wall_shear_two_decay` | "the reverse-flow branch is unique" | ACCEPTED (FB9 aimed) |
Gaps: FB rules read only Correct (FB6/FB9) and tagged numbers; Scope/Classification/Printed order/Lean-evidence prose free; verified-section regex misses headings like F15a; norecord findings F4-F7 have no record to contradict their prose; neutral LEDGER lines satisfy FB7.
