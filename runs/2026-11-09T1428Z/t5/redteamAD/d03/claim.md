# d03 – honest second formula reading: dedupe of its first line, glue of its second line to the last text shown

Weakness: template (`generate`). Two TRUE blind lines for `cosmoCoeff` (new folder, own BRIEF.md, narrow reader like the
SYMBOLS reader): "n-th time derivative of the scale factor over the scale factor" (contained in a text already shown,
so dropped, but `prev` is set to it) and "divided by the Hubble rate to the power n" (not contained, starts with
"divided by", `prev == (src, idx-1)`), which is glued to `par[-1]` = the SYMBOLS clause for order 5, because the new
block follows the SYMBOLS block. Nothing the reader wrote is false; the sentence is made by the template.

Generated phrase tail:

> ... The order 4 coefficient is the snap parameter usually written s; **The order 5 coefficient is the lerk parameter
> usually written l divided by the Hubble rate to the power {n}**)

False against `cosmoCoeff n a t = iteratedDeriv n a t / (a t * hubble a t ^ n)`: the order-5 coefficient is a^(5)/(a H^5),
not "l divided by H^n" (l is that coefficient). Plausible as an ordinary follow-up (a formula reader after the letter
reader, whose block is appended after SYMBOLS). Body printed next to the phrase is correct (partly DISCLOSED).

Rules passed: all of d01's list; `generated()` 0 problems; P9 (both new lines occur in the phrase word for word);
P12/baseline: the new lines are not in the exclusion baseline. Route (`roles_route`): one added registry line, to be
carried by brief -> reading -> copy commits (not reproducible without git; the files are created in that order by a
genuine author). Survives P10/P11 as implemented. Note the first reader line is byte-identical to an existing registry
line (so the set difference of lines shows ONE added line).
