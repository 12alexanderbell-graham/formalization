# Adversarial review: statementNums / check_prose numgaps

CAVEAT: the checked-out /home/claude/fz-main working tree does NOT contain `statementNums`, `nums`, `numgaps`, or
`NUM =` in check_prose.py (grep finds none; they exist only in the branch history, which I was told not to read via git).
I reviewed against the task description plus the sibling code present: `decLit?`/`ratLit?` in StatementDeps.lean
(l.177, 231) and `NUM`/`value` in check_numbers.py. Items marked [verify] depend on the unseen implementation.

## False acceptances (wrong number passes)

1. HIGH - Number equals an unrelated literal in the statement. Statement contains 1/2, 0, 1, 2, 10, 100, a tolerance 1/1000;
   docstring wrong "half-conversion time 2.5664" passes only if 2.5664 in set, but "factor 2.0 ... 0.5 ... 1/2" always pass.
   Worse: a bound/precision literal (e.g. `5e-5`, `0.0001`) can equal a wrong prose value. The set is per-statement, not per-role.
   Fix: for the claimed result number, require match against the RoundsTo/conclusion literals specifically (the existing
   `.lake/records_numbers.tsv` and `[✓name]` tags), or require a prose number to be tagged by role; at minimum exclude
   tolerance/hypothesis-position literals (reuse posRoundsToLits logic) from the set for "result" numbers.
2. HIGH - Sign hidden by absolute value. Docstring "lag -0.245" vs statement `0.245`, or "decreases by 3/10" vs `-3/10`.
   Fix: compare signed when the prose has an explicit minus/plus; allow unsigned prose to match either sign only when
   no sign char precedes it. Normalize all dashes (−–—) as check_numbers.py does.
3. HIGH - Number formats the regex does not read (silently skipped, so never compared):
   - scientific `1.3×10⁻⁵`, `1.3e-5`, `1e-4`, `1.3 x 10^-5`, `1.3·10^{-5}`; NUM in check_numbers.py supports only `×10[⁻⁺]?SUP+`.
     A bare `1.3` then is compared/flagged but `1.3×10⁻⁵` with a wrong exponent may be read as 1.3 and PASS if 1.3 is a literal
     (the statement literal 0.000013 is OfScientific m=13,d=6). Must compare full value incl. exponent.
   - percent `2.5%`, `25.7 %` (decimal read, but equals 0.025 in statement; either false alarm or wrong-pass if 2.5 present elsewhere).
   - comma decimal `2,5665`, thousands `2,566` (reads as integer 2 and 566, ignored: integers not checked).
   - unicode fractions `½`, `¾`, vulgar fractions, `1⁄3` (U+2044), `1÷3`, `a:b` ratios.
   - Unicode minus `−`, range `2.5665–2.5666` (en dash: second number may be read as negative -2.5666 -> abs saves it, but then
     a wrong upper endpoint equal to a literal passes; ranges should check both ends).
   - Adjacent to letters/units: `0.05mag`, `2.5665s`, `\d+\.\d+` preceded by `~`/`≈`; a `(?<![\w.])` lookbehind (as in check_numbers)
     rejects `v2.5665`, `k0.31` [verify whether numgaps uses one]. `0.05mag` passes only if the lookahead lets a letter follow.
   - Subscripts/superscripts `x₀ = 0.3`, `10⁻⁵` alone, `10^{-5}`; Greek-adjacent `α=0.31`.
   - Spaces in numbers `2.566 5`, thin spaces/NBSP, digit grouping `2.566_5`.
   - Decimal without leading digit `.5665` (regex `\d+\.\d+` misses), trailing-dot `2.`.
   Fix: one tokenizer shared with check_numbers.py (import `NUM`/`value`), covering exp, %, comma, vulgar fractions, ranges;
   plus an "unparsed numeric-looking token" tripwire: any `\d` run in a headline docstring not consumed by an accepted form and
   not in an allowlist (equation numbers, arXiv ids, names in backticks) is an error.
4. HIGH - Integers are not checked at all (only decimals and fractions). "13 half-lives", "z = 2", "6th order", "after 25665 steps"
   wrong integers pass. Fix: check integers >= 2 (or all not in an allowlist) against nat literals; at least those
   next to units/"times"/"x".
5. MED - Precision/rounding mismatch. Prose "2.57" for statement `2.5665` (rounded) or "2.5665" for statement `25665/10000`
   passes only if equal; but "2.5" vs `5/2` passes (equal), "0.33" vs `1/3` flagged. Conversely the prose number "2.5665" is
   accepted if ANY literal equals it, including one only in `RoundsTo x 2.5665 4` hypothesis rather than the conclusion
   (defect D05 shape: `¬ RoundsTo`). Fix: use only positively-asserted literals (posRoundsToLits) for result numbers.
6. MED - Derived quantities. Prose "doubling time 0.693" or "ratio 0.8" computed from statement values passes nowhere
   (false alarm), while a wrong derived value that coincides with some other literal passes. Need an explicit
   `derived:` annotation or tag syntax (as `[in✓name]`).
7. MED - Literals from definitions the statement uses are not collected (statement-level traversal of Expr only, as ratLits does,
   no delta/unfolding): parameters in `def p : ℝ := 0.31` appear in the statement only as constant `p`. Prose "0.31" is then
   FALSELY flagged (false alarm, see below) - but the reverse is dangerous: if the author silences the flag by whitelisting/baselining
   (`prose_baseline.txt`), a later change of the definition's value is never noticed. Fix: also collect literals of directly-used
   pinned/transcribed definition bodies, tagged separately.
8. MED - Expr-level misses in the collector [verify]: `ratLit?` requires the first explicit arg of the head to be `Real`
   (`e.getArg! 0 = Real`): literals over ℚ, ℂ, ℕ→ℝ casts (`((25665:ℕ):ℝ)/10000`, `(25665 : ℝ) / 10000` is fine but `Nat.cast 25665 / 10000`
   is not recognized), `Rat` casts `(↑(25665/10000 : ℚ) : ℝ)`, `NNReal`, `Real.sqrt 2`, `π`, `exp 1`, `2⁻¹` (Inv.inv), `x⁻¹`, `1/2^3`,
   `(3:ℝ)/10 * 5` (product, not a bare quotient), `Real.logb 10 2`. Also `HDiv` of two literals with divisor negative
   (`1 / -2`) returns none (c>0 guard), and `a / b` where b is itself a quotient is handled but `(a/b)/c` mix with Neg inside
   Neg.neg (a / b) vs (-a)/b both OK. Also `OfScientific` with `Bool.false` (negative exponent form `1e5` = m*10^e) returns
   none, so `1e5`/`2.5e3` literals are dropped (HIGH-ish if statement uses `1e-5`? No: 1e-5 is Bool.true m=1 d=5 OK; `1e5` is Bool.false: dropped).
   Fix: handle Bool.false (m*10^e), Nat.cast/Int.cast wrappers, Inv.inv, and ℚ.
9. MED - Instance arguments / auxiliary structure: recursion stopping at `OfNat.ofNat` is fine, but Expr traversal that does
   not descend into `.proj`, `.letE`, `.lit`-typed args, or implicit args (e.g. `Set.Icc 0 1`, `Finset.range 5`) is fine; however
   a non-Real literal like `ℕ` exponent `x^3` is excluded by the Real guard, so prose "cubic ... 3" untested (consistent with item 4).
10. MED - Both readings of a/b: prose "13/5" flagged only if neither 13/5 nor 2.6 present, but prose fraction "1/3 of rate"
    also matches a date "2026/11"/"3/4 pages"/"Fig 3/4": false alarms; conversely a prose slash "and/or 1/2" fine.
    `a/b` with the regex lacking boundaries could read "10/100" inside "10/1000" (partial). [verify \b].
11. LOW - Value-based dedupe: comparing as Fraction ignores written precision, so docstring `2.50` for statement `5/2` passes and
    `2.5` for `RoundsTo x 2.50 2` passes; claimed digits are not verified. Probably acceptable; optional: require prose decimals
    count of places <= the literal's `d`.
12. LOW - Non-headline docstrings (definitions a headline rests on, scripts' `r["doc"]`, comments `--`, module docstrings,
    FINDINGS.md, `/-! -/`) are out of scope: a wrong number in a definition's docstring ("transcribed from Table 2: k = 0.31"
    vs body `0.13`) is never compared. Fix: run the same comparison for definitions reached by headlines against their own
    body literals (cheap, same extractor), and for module docstring of the file defining the headline.
13. LOW - Backtick code spans: strip_code_names only blanks backticked identifiers; but check_numbers.py shows a wrong decimal in a
    code span (F05) escaped before. Make sure numgaps reads code spans like prose and does not skip ``` fenced blocks or LaTeX `$...$`.
14. LOW - Dedup/baseline: any `|numgap|...` key added to prose_baseline.txt silences it permanently by (name, text) key without
    value; baseline should record the number so a changed number re-fires.

## False alarms (honest docstring wrongly flagged)

A. Prose number whose literal is only in a definition body (item 7) - extremely common (`duffing_first_zero_sol` style sol
   statements refer to named constants). HIGH volume. Fix as item 7.
B. Rounded/approximate prose: "≈ 2.57", "about 0.31" when the statement is a RoundsTo/interval `2.5665 ≤ t ∧ t ≤ 2.5666`
   is OK, but "t ≈ 2.5666" vs bounds is OK only if collected from both ends; and `|t - 2.56655| < 5e-5` -> prose
   "2.5665 ± 0.00005" needs both literals: 2.5665 is not present (2.56655 is) -> flagged. Fix: also accept center/halfwidth
   decompositions or allow `approx` tag with tolerance equal to a statement tolerance.
C. Derived/unit-converted numbers: "1.5 days" vs 36 hours; "0.693 = ln 2"; "2.5665 (dimensionless time 2.5665/k)"; percent forms; "factor 4.0".
D. Identifiers: arXiv ids (2410.12345 - check_numbers special-cases `\d{4}\.\d{4,5}`), equation numbers "(10.54)", section numbers
   "§3.2", table "Table 2.1", "Fig. 4.2", version "v1.2", dates "2026.11", Lean/Mathlib version, `ℝ^2.5`, citations "[12.3]", "Hz 50.0". Reuse check_numbers' exemptions and add
   section/figure/Table/eq patterns.
E. Trailing sentence period: "... equals 3." / "t = 2.5665." must not read as `2.` or `2.5665.`; "2.5665." followed by letter,
   `1.5.` ; "3.14159..." ellipsis.
F. Leading-sign mismatch from hyphen use: "1-2" ranges, "2.5-3.0" read as 2.5 and -3.0 (abs makes OK), "state-of-the-art 3-body" no.
G. Fractions in prose that are not numbers: "1/f noise", "and/or", "1/2-integer spin" (ok), "dN/dz", "d/dt" (needs digit-both-sides),
   dates 11/04, "24/7", "a 3/4-power law" (statement writes `(3:ℝ)/4`, fine; but `x ^ (0.75:ℝ)` -> 0.75 equals 3/4: fine via value compare).
H. Literals the statement writes in a different but equal form: `1.0` vs `1`, `2.50`, `0.5` vs `1/2`, `(1:ℝ)/3` vs prose "0.333…" (never equal; flagged).
   Prose `0.333` should be allowed iff tagged approx.
I. Literals the statement elaborates away or moves: `norm_num`-style coercions (`(0.5 : ℝ)` may appear as `OfScientific 5 true 1` - collected - but a
   literal under `Set.Icc` binder-typed ℝ≥0 (`NNReal`) or over `ℚ`/`ℂ`/`Fin` is dropped by Real guard) -> honest "0.5" flagged.
J. Statements with `∀ x ∈ Set.Icc (0:ℝ) 1` where the number is "1" - integer, unaffected.
K. Numbers inside `\`code\`` names with digits: `` `duffing2_sol` `` - ok if KNOWN, else tokenized `2`; decimals inside names like `v0.3` handled by lookbehind.

## Top recommendations
1. Share one tokenizer/value() with check_numbers.py (exponent, dashes, percent, comma, ½, ranges) and add an "unparsed numeric token" error.
2. Compare signed values when the prose has a sign; abs only as fallback with a warning.
3. Build the allowed set only from positively asserted conclusion literals (exclude hypotheses/tolerances/Set.Icc bounds), plus an explicit
   `[in]`/`[derived]` escape tag, to kill the "equals some other literal" hole.
4. Extend the extractor: OfScientific Bool.false, Nat/Int/Rat casts, Inv.inv, definition bodies reached (delta, one level), ℚ/ℝ≥0 types.
5. Check integers adjacent to units/quantity words, and numbers in docstrings of reached definitions.
6. Baseline entries must carry the number (key = name|numgap|value).
