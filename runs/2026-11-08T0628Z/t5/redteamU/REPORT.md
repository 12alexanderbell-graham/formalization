# REPORT (red team U)

All six: check_numbers (plain and --base ac435db), check_prose (0 new problems), precheck_citations (0 suspected) pass. LEDGER_add empty. Expected: ACCEPTED.

- d01 -> scope-extension via a numeral outside S3/S4 pattern ('redshift 5', not bound value): The 1.3e-5 bound (certified at z=2 only) holds up to z=5; actually z⁴ grows 39x at z=5 (about 5e-4).
  sentence: `relative shift k²z⁴/120 ≤ 1.3×10⁻⁵[✓F8_sizes(k=0.01, z=2)] up to redshift 5`
  checks: all pass
- d02 -> wrong formula coefficient in prose (untagged integer): The l₀ shift is 105q₀⁴ (which would be -43, not -86); true shift is 210q₀⁴ as Lean-certified -86.
  sentence: `absorbed exactly by l₀ ↦ l₀ − 105q₀⁴ (≈ −86[✓F11_sizes(q₀=−0.8)] ...`
  checks: all pass
- d03 -> role of a free value (pole of the wrong function): The pole at 0.176 belongs to the PRINTED denominator; the corrected one has none.
  sentence: `the corrected denominator has a spurious pole at Ω ≈ 0.176[✓F10_printed_pole]`
  checks: all pass
- d04 -> input symbol / parameter identity: Records are at Ω_m = 0.3; Ω_Λ = 0.3 means Ω_m = 0.7 (different numbers).
  sentence: `flat ΛCDM Ω_Λ = 0.3[in✓F3_D4_LCDM]`
  checks: all pass
- d05 -> direction/sign word in a difference: Printed D⁴ is HIGHER than the true one (printed 0.4555 > true 0.2153): the printed value is too high, not too low.
  sentence: `a z⁵ coefficient too low by 21q₀⁴/8 (≈ +0.24[✓F3_D4_LCDM(difference)] ...`
  checks: all pass
- d06 -> unit/scale of a free value: 0.72 is an absolute offset inside the bracket, not 0.72 % of l₀; units are unread.
  sentence: `0.72[✓F11_sizes(q₀=−0.8, z=1)] percent of l₀`
  checks: all pass
