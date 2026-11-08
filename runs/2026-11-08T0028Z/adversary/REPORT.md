# REPORT
Accepted (exit 0, files defects/dN/FINDINGS.md + claim.md + out.txt):
- d1 F1: correct 3.115[F1_l0] / printed 0.685[F1_printedL0] roles swapped in prose (single-valued records, no selectors).
- d2 F2_toy: true/printed swapped, each tag carries its own correct selector.
- d3 F2_toy: toy parameters (Omega,w0,wa) permuted (w0<->wa); [in] checks set membership only.
- d4 F8: Milne percentages' redshifts swapped using 'at redshift 2' instead of 'z = 2' (the original red-team defect, evades S3's `v = c` regex).
- d5 F9_values: +0.277 / -5.25 (printed vs true) swapped; record in the ambiguity baseline.
- d6 F3: '+0.24 at q0 = -0.55' becomes '-0.55 at q0 = +0.24' (decel selector has no binding).
- d7 F8: 1.3e-5 bound claimed 'up to redshift 1' (record is z=2).
Caught: z swap written 'z = 2'/'z = 1' (S3); w_a = 0.5 (in-set); swapping tags' record names 0.685[F1_l0] (value); Omega 0.3 for F9 (in-set); F11 'z = 2' (S3); swapped Omega selectors in F10 tags (S1); dropping selector on F10_eta (S2).
Root cause: the check verifies that (number, record, selector) is a consistent triple, and that `var = c` prose agrees with selector bindings, but never ties the prose ROLE (correct/printed/true, which parameter slot, which redshift phrase) to the record/selector. Roles live in names (@correctD4, empty selector, @cosmoCoeff) that prose does not have to mention; prose binding recognition is only the literal regex `v = number`; [in] is unordered set membership; single-valued or baseline records have nothing to discriminate. A stronger design: require a role word adjacent to each certified number mapped to selector heads, extend S3 to 'at redshift c'/'z ≈ c', and make params ordered/named.
