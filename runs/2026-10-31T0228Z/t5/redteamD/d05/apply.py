import sys, pathlib
root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:50], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


LEAN_OLD = "end Checked.Records"
LEAN_NEW = '''/-! ## F4 (Bamba et al. 2012, Eq. (10.54)) -/

/-- The corrected flat `D²_{L,y} = (11 − 5q₀ + 3q₀² − j₀)/6` at `q₀ = −0.55`, `j₀ = 1`
(flat ΛCDM, `Ω_m = 0.3`) is not `2.610` (the value with the sign of `j₀` reversed). -/
theorem F4_D2y_check :
    ¬ RoundsTo ((11 - 5 * (-11 / 20) + 3 * (-11 / 20) ^ 2 - 1) / 6) 2.610 3 := by
  first
    | (intro h; unfold RoundsTo at h; rw [abs_le] at h; norm_num at h; done)
    | (unfold RoundsTo; rw [abs_le]; norm_num; done)

end Checked.Records'''
sub("Checked/Records/Findings.lean", LEAN_OLD, LEAN_NEW)
sub("scripts/trust/headlines.txt", "Records.F11_sizes\n", "Records.F11_sizes\nRecords.F4_D2y_check\n")
sub("TRUST_MAP.md", "Headlines: 115. Resting on no unpinned physics definition: 115.",
    "Headlines: 116. Resting on no unpinned physics definition: 116.")
sub("TRUST_MAP.md", "| `Records.F11_sizes` | — | — | — | unconditional |\n",
    "| `Records.F11_sizes` | — | — | — | unconditional |\n| `Records.F4_D2y_check` | — | — | — | unconditional |\n")
sub("FINDINGS.md",
    "(flat: (11 − 5q₀ + 3q₀² − j₀)/6).",
    "(flat: (11 − 5q₀ + 3q₀² − j₀)/6, which at q₀ = −0.55[in], j₀ = 1 (flat ΛCDM, Ω_m = 0.3[in]) is 2.610[✓F4_D2y_check]).")
