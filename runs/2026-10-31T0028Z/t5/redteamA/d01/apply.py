import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")

# digit slip when transcribing the printed l0 of Aviles et al. Eq. (15): 27/2 -> 21/2
sub("Checked/Cosmography/LCDMCoefficients.lean",
    "    cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 2 * Ω ^ 2\n",
    "    cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 21 / 2 * Ω ^ 2\n")
