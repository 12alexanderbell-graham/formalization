Category: weakened-statement (Lean coverage overstated in a legacy no-record finding)
Reader would wrongly believe: F4 Scope: "Lean covers the sign for every curvature K, flat or curved; the sympy + Milne + open-dust Mattig checks (referee) agree." (original: "Lean covers the flat instance only; the curved statement is sympy + Milne + open-dust Mattig checks (referee).")
Why it is false: `Checked.Cosmography.BambaY.lumDist_y_third_order` and `printedD2y_fails` are stated for flat FLRW (K = 0) only; the F4 Lean-evidence line itself says "flat FLRW". The curved claim is not in Lean. F4 is baselined `norecord` (FB8), so no record or generated block can contradict its prose, and its Correct line is untouched (FB9 silent).
Expected: ACCEPTED (neutral LEDGER line satisfies FB7).
