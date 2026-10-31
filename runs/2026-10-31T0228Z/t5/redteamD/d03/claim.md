Category: wrong-number
Reader would wrongly believe: the omitted curvature-squared term k²z⁴/120 of the F8 series is at most 1.3×10⁻⁷ (certified-looking "1.3[✓F8_sizes]") for |Ω_k| ≲ 0.01 up to z = 2, i.e. the printed D⁴ misprint is a hundred times less relevant than it is.
Why it is false: (1/100)²·2⁴/120 = 1.33×10⁻⁵, which is what Records.F8_sizes certifies (the Lean term carries the factor 10⁵); only the mantissa 1.3 is matched by the tag rule, the power of ten (and any integer/unit) is invisible to it.
Expected: ACCEPTED (check_numbers.py reads only decimals; '10⁻⁷' is two integers/superscripts; pair (1.3, F8_sizes) unchanged so no LEDGER demand).
