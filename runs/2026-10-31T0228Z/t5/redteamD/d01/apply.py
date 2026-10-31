import sys, pathlib
root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:50], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


sub("FINDINGS.md",
    "flat ΛCDM Ω_m = 0.3[in]: 0.2153[✓F3_D4_LCDM] vs 0.4555[✓F3_D4_LCDM]",
    "flat ΛCDM Ω_m = 0.3[in]: 0.4555[✓F3_D4_LCDM] vs 0.2153[✓F3_D4_LCDM]")
