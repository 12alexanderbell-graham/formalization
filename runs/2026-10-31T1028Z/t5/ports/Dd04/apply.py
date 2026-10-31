# port (run 1028Z): the TRUST_MAP.md edits removed (the author regenerates the map; they no longer match)
import sys, pathlib
root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:50], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


LEAN_OLD = "end Checked.Records"
LEAN_NEW = '''/-! ## F5 (Cattoën & Visser 2007, Eq. (59)) -/

/-- The corrected `y²` coefficient of `d_Q(y)/(d_H y)`, `(1/24)[3 − 2q₀ + 12q₀² − 4(j₀ + Ω₀)]`,
at the flat ΛCDM values `q₀ = −0.55`, `j₀ = 1`, `Ω₀ = 1` is `−0.0225`. -/
theorem F5_Q2_values :
    RoundsTo (1 / 12 * (3 - 2 * (-11 / 20) + 12 * (-11 / 20) ^ 2 - 4 * (1 + 1))) (-0.0225) 4 := by
  unfold RoundsTo; rw [abs_le]; norm_num

end Checked.Records'''
sub("Checked/Records/Findings.lean", LEAN_OLD, LEAN_NEW)
sub("scripts/trust/headlines.txt", "Records.F11_sizes\n", "Records.F11_sizes\nRecords.F5_Q2_values\n")
sub("FINDINGS.md",
    "A reader using the displayed d_Q(y) formula gets the y² term doubled.",
    "A reader using the displayed d_Q(y) formula gets the y² term doubled. At flat ΛCDM (Ω_m = 0.3[in]: q₀ = −0.55[in], j₀ = 1, Ω₀ = 1) the corrected y² coefficient of d_Q(y)/(d_H y) is −0.0225[✓F5_Q2_values].")
