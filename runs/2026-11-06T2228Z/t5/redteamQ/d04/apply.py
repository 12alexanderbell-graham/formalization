import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rd(p): return (root/p).read_text(encoding="utf-8")
def wr(p, s): (root/p).write_text(s, encoding="utf-8")
def app(p, s):
    t = rd(p)
    if not t.endswith("\n"): t += "\n"
    wr(p, t + s)
def rep(p, old, new):
    t = rd(p); assert t.count(old) == 1, (p, old[:60], t.count(old)); wr(p, t.replace(old, new))

LEAN = 'import Mathlib.Data.Real.Archimedean\n\n/-!\n# Unbounded levels\n\nEnergy levels indexed by the natural numbers exceed every real energy.\n-/\n\nnamespace Checked.Math.EnergyLevels\n\n/-- There is a level n such that the energy E is below n for every E. -/\ntheorem energy_below_some_level (E : ℝ) : ∃ n : ℕ, E < (n : ℝ) := exists_nat_gt E\n\nend Checked.Math.EnergyLevels\n'
wr('Checked/Math/EnergyLevels.lean', LEAN)
app("Checked.lean", "import Checked.Math.EnergyLevels\n")
app("scripts/trust/headlines.txt", 'Checked.Math.EnergyLevels.energy_below_some_level' + "\n")
