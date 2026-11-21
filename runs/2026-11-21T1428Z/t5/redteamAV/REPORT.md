# REPORT AV

All five defects use one weakness: the free-text summary field of scripts/trust/objections.txt (Claims.lean checks only that the headline resolves and the path exists; nothing checks truth, relevance, or consistency with the generated counts). Only 5 of 6 delivered (time/Lean budget; one Claims.lean run, all five applied together, outputs identical to apply.py patches; all trust and frozen checks with BASE=0ae34b28 green; the clean snapshot was not re-run by me).

- d01 -> misleading-record -> false reassurance in the free-text summary of an objection entry -> headline oL_bic_exceeds: «referee verdict STANDS after a blind re-read of the source table; the statement agrees with the source in every hypothesis and constant, objection closed» -> expected ACCEPTED
- d02 -> misleading-record -> fabricated objection (false doubt) on a valid headline -> headline flatLCDM_coeffs: «blind restatement from the source disagrees: the printed jerk coefficient has the opposite sign to the one in the statement» -> expected ACCEPTED
- d03 -> misleading-record -> a real objection entered under the sibling headline, so the true target shows "none" -> headline l19_sqg_curved: «referee verdict DOES NOT STAND on the sibling l19_sq_curved: its conclusion is not what the source states» -> expected ACCEPTED
- d04 -> misleading-record -> objection summary contradicting the generated necessity counts -> headline eta_ratios: «referee re-check: all four hypotheses are needed, none is redundant and none is open» -> expected ACCEPTED
- d05 -> misleading-record -> objection summary forging a blind-reading record for a headline with none registered -> headline laneEmden2_constants: «two blind readers re-derived every constant of the statement from the source independently and agree with it» -> expected ACCEPTED

Not done (untested): def_kinds relabels, pins redirects, source= misattribution in literal_readings.txt (heavily guarded by check_literals/check_source_names), phrases.txt edits (P2-P7 lints close them).
