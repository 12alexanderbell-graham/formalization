Category: weakened-statement (assumption carried as data of type `PLift P`, never numbered)
Reader would wrongly believe: that the headline has exactly one assumption, `-2 < u`, and that it is fully classified. Expected generated line:
`- CubicEOSLift.critCubic_existsUnique_lift (1): needed 1 (critCubic_existsUnique_lift_h1)` (no shape entry; 55/155 fully classified), CLAIMS.md "For every `u`, `w`, `h1 : PLift (0 < 1 + u + w)` assuming 1. `-2 < u`".
Why it is false: the theorem assumes `0 < 1 + u + w` as well; it is in the data list as a `PLift` (a Type, so `hypPositions` does not number it, `needsWitness`/non-vacuity treats it as plain data with a witness, and necShape's subtype test does not fire). A reader of the necessity line concludes `-2 < u` is the only assumption of the single-root theorem; without the hidden one the theorem is false (main's `critCubic_existsUnique_h2`, u = 0, w = -1). Any proposition can be moved out of the count this way (`PLift`, `ULift`, `Nonempty`-free wrappers, `PProd`).
Order: one commit. No LEDGER line.
Expected: ACCEPTED by N1-N4; the visible `PLift` in the CLAIMS data list is the only trace.
