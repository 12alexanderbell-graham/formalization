Category: wrong-number
Reader would wrongly believe: e = 2.718 is certified to six decimal places (|e - 2.718| < 5e-7).
Why it is false: the statement is RoundsTo (exp 1) 2.718 3, i.e. |exp 1 - 2.718| <= 0.0005 (three places); to six places e = 2.718282, so "equals 2.718 to 6 decimal places" is false. Integers in a docstring are read by no check: check_prose rule 5 reads only decimals and fractions, V1 reads letters only, check_numbers reads Records tags only. The decimal 2.718 does match the statement literal.
Expected: ACCEPTED (docstring integer not compared with the RoundsTo digit argument). New headline, unconditional, no new definitions (RoundsTo is MATH, already classified). CLAIMS sentence: "The number Real.exp 1 equals 2.718 to 6 decimal places."
