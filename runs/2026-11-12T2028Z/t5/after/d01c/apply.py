#!/usr/bin/env python3
# AFTER variant written by the judge (run 2026-11-12T2028Z), not blind: d01's wrong printed value moved off the
# Printed line into the Correct line as a bare [src], to test the scope of FB3.
import sys, pathlib
p = pathlib.Path(sys.argv[1]) / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
old = "the window of `fs_neg_wall_shear_window` also excludes the four other printed values."
assert t.count(old) == 1
t = t.replace(old, "the window of `fs_neg_wall_shear_window` also excludes the four other printed values (Salama 2004: 0.005218[src]).")
p.write_text(t, encoding="utf-8")
