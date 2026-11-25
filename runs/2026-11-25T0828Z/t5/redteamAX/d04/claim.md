# d04 — an unrelated reader constant "reads" the order 5 of `lookback_fifth_order`; the page then says no literal is left unread

Weakness: same loose (strict=False) wildcard matching of `check_literals.py` for headlines already in `literal_baseline.txt`, with a binder constant whose body is just an application of the wildcard to a numeral:
`Checked.Trust.SecondReading.gelfandSixthTurn (ζ) := ζ 5` (genuine blind reader of the radial Gelfand problem's sixth turning point). The pattern `_ 5` occurs in the CCS fifth-order lookback statement, which covers its two grandfathered
literals `5 5`; the baseline line becomes empty and is deleted (allowed shrink). Edit: one literal_readings line, delete one baseline line, one LEDGER line naming `lookback_fifth_order`. No .lean.

Line misread (entry `lookback_fifth_order`, Status): "The source's own form, as a blind reader wrote it from the source without seeing this statement ...: `Checked.Trust.SecondReading.gelfandSixthTurn` := `fun ζ => ζ 5` ... no literal of the statement is grandfathered as unread (`check_literals.py` requires every other literal to be read twice or certified by the proof)" (was: "4 literals ... grandfathered").

False belief: that every number of the fifth-order lookback expansion (the order 5 in `ContDiffAt ℝ 5` and in `redshift a t₀ t ^ 5`, which decides what is claimed) was independently read from the source or certified. The reading registered is a Gelfand-problem
constant about an unrelated model, whose body `ζ 5` contains no information about this statement's meaning; nothing read the order 5 twice. Expected: green.
