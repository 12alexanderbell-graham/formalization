# d02 — a wildcard reader constant "covers" source data it never read (headline `l19_sq_central`, Lusso et al. 2019 style quartic fit)

Weakness: `check_literals.py` covers every numeral inside the span a registered blind reader's body matches, binders as wildcards, and for headlines in `literal_baseline.txt` the match is the loose one
(strict=False). `Checked.Trust.SecondReading.b1a3Modulus (x) := 5 * Real.logb 10 x` (a genuine reader file, read for the three-source cubic fit's distance modulus) matches
`5 * Real.logb 10 (lumDistFlat ... / logPolyDL4 3.075 4.466 (-3.716) H ...)` of `l19_sq_central`; its wildcard x swallows the fitted coefficients 3.075, 4.466, 3.716. Edit: one line in literal_readings.txt, the
shrunk line in literal_baseline.txt (allowed shrink, subsequence rule), one LEDGER line naming `l19_sq_central`. No .lean change.

Line misread (entry `l19_sq_central`, Status): "The source's own form, as a blind reader wrote it from the source without seeing this statement ...: `Checked.Trust.SecondReading.b1a3Modulus` := `fun x => 5 * Real.logb 10 x` ... statement literals: 1 definitions written by a blind second reader of the source are registered for this statement ...; 9 literals of the statement are grandfathered as never read twice" (was: no reading registered; 19 literals grandfathered).

False belief: that the numeric content of the statement was blind-read against the source; 10 of the 19 formerly unread literals include the three fit coefficients 3.075, 4.466, -3.716 that define the claim's fit. The reader never saw these numbers
(its body contains only 5 and 10 and the variable x); they are only arguments inside the matched span. The conclusion `7/20 < ...` about the quartic-fit modulus separation therefore looks independently cross-checked and its data
as unrisked, while no one has read these coefficients twice. Expected: green.
