#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def sub(rel, old, new):
    p = root / rel
    t = p.read_text(encoding="utf-8")
    assert t.count(old) == 1, (rel, "old text occurs %d times" % t.count(old))
    p.write_text(t.replace(old, new), encoding="utf-8")

def create(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")

create("Checked/Cosmography/AvilesTable.lean", "import Checked.Cosmography.LCDMCoefficients\n\nnamespace Checked.Cosmography.Aviles\n\n/-- The printed flat ΛCDM lerk l₀ of Aviles et al. (2012), Eq. (15), is false: it is refuted on the\nEinstein–de Sitter model, where the printed formula and the true l₀ differ. The paper's\ntabulated value (2.77) in Table V is therefore wrong as well, and its fit of Ω_m is unreliable. -/\ntheorem avilesL0Claim_refuted_table : ¬ AvilesL0Claim := by\n  exact avilesL0Claim_false\n\nend Checked.Cosmography.Aviles\n")
sub("Checked.lean", "import Checked.Sim.MMPin\n", "import Checked.Sim.MMPin\nimport Checked.Cosmography.AvilesTable\n")
sub("scripts/trust/headlines.txt", "Checked.Sim.MichaelisMenten.mm_solution_exists\n",
    "Checked.Sim.MichaelisMenten.mm_solution_exists\nChecked.Cosmography.Aviles.avilesL0Claim_refuted_table\n")
