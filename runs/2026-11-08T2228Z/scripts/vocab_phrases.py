#!/usr/bin/env python3
"""Third pass (run 2026-11-08T2228Z): keep the words 'model' (lumDist, angDist) and 'matter fraction' (IsFlatLCDM,
IsFlatCPL) that existing headline paraphrases quote from the generated claims (check_claim_vocab V1), around the blind
names and roles. Applied after new_phrases.py and name_phrases.py."""
import sys
from pathlib import Path
ROOT = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
SUBS = [(", with scale factor {a} and spatial curvature constant {K} (units in which the speed of light is one; positive curvature constant means closed, negative means open)",
         ", in the model with scale factor {a} and spatial curvature constant {K} (units in which the speed of light is one; positive curvature constant means closed, negative means open)", 2),
        ("obeys the flat ΛCDM Friedmann expansion law with present matter density parameter {Ω}", "obeys the flat ΛCDM Friedmann expansion law with matter fraction given by the present matter density parameter {Ω}", 1),
        ("Friedmann expansion law with present matter density parameter {Ω}, present dark energy", "Friedmann expansion law with matter fraction given by the present matter density parameter {Ω}, present dark energy", 1)]
p = ROOT / "scripts/trust/phrases.txt"
t = p.read_text(encoding="utf-8")
for a, b, n in SUBS:
    assert t.count(a) == n, a
    t = t.replace(a, b)
p.write_text(t, encoding="utf-8")
