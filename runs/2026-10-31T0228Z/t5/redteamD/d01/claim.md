Category: misleading-record
Reader would wrongly believe: in flat ΛCDM (Ω_m = 0.3) the TRUE lookback z^5 coefficient D^4 is 0.4555 and the misprinted one is 0.2153 (the order in "true vs printed" is swapped), i.e. the printed (7/2)q0^4 version underestimates D^4, contradicting the "printed - true = +(21/8)q0^4" line and reversing who is wrong; each number still carries a valid green [✓F3_D4_LCDM] tag.
Why it is false: Checked.Records.F3_D4_LCDM proves correct D^4 = 0.2153 and printed D^4 = 0.4555 (printed - correct = +0.24); the tag rule only checks that the number occurs among the theorem's RoundsTo literals, not which quantity it labels.
Expected: ACCEPTED (the multiset of (number, tag) pairs is unchanged, so check_numbers.py and --base see nothing; no Lean/frozen entry touched).
