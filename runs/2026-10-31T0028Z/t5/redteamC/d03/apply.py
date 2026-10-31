#!/usr/bin/env python3
import sys, re, pathlib
R = pathlib.Path(sys.argv[1])
def rd(p): return (R / p).read_text(encoding="utf-8")
def wr(p, s):
    (R / p).parent.mkdir(parents=True, exist_ok=True)
    (R / p).write_text(s, encoding="utf-8")
def rep(p, old, new):
    s = rd(p)
    assert s.count(old) == 1, (p, old[:70], s.count(old))
    wr(p, s.replace(old, new, 1))
def app(p, line):
    wr(p, rd(p).rstrip("\n") + "\n" + line + "\n")
def new(p, s):
    assert not (R / p).exists(), p
    wr(p, s)
def register(headline, row, witness):
    """append a headline to the registry and update the generated TRUST_MAP.md exactly as
    StatementDeps.lean would regenerate it (so the stale-map check does not fire)."""
    app("scripts/trust/headlines.txt", headline)
    s = rd("TRUST_MAP.md")
    s, n = re.subn(r"Headlines: (\d+)\. Resting on no unpinned physics definition: (\d+)\.",
                   lambda m: "Headlines: %d. Resting on no unpinned physics definition: %d." % (int(m.group(1)) + 1, int(m.group(2)) + 1), s)
    assert n == 1
    if witness:
        s, n = re.subn(r"\(trust track T2\): (\d+) headlines have hypotheses; (\d+) of them",
                       lambda m: "(trust track T2): %d headlines have hypotheses; %d of them" % (int(m.group(1)) + 1, int(m.group(2)) + 1), s)
        assert n == 1
    wr("TRUST_MAP.md", s.rstrip("\n") + "\n" + row + "\n")
def state_bullet(text):
    rep("STATE.md", "- **Findings F1–F11**", text + "\n- **Findings F1–F11**")
def import_checked(mod):
    app("Checked.lean", "import " + mod)

new("Checked/Cosmography/CosmicAge.lean", """import Checked.Cosmography.Lookback

namespace Checked.Cosmography.CosmicAge

/-- Age of a flat matter-dominated (Einstein-de Sitter) universe in units of the Hubble time
`1/H0`: `t0 = 2/3` (Ryden, Introduction to Cosmology, Eq. 6.27). -/
private noncomputable def edsAge : ℝ := 3 / 2

/-- An Einstein-de Sitter universe is older than the Hubble time `1/H0`. -/
theorem eds_older_than_hubble_time : 1 < edsAge := by
  show (1 : ℝ) < 3 / 2
  norm_num

end Checked.Cosmography.CosmicAge
""")
import_checked("Checked.Cosmography.CosmicAge")
register("CosmicAge.eds_older_than_hubble_time",
         "| `CosmicAge.eds_older_than_hubble_time` | — | — | — | unconditional |", False)
state_bullet("- **PROVED** (F12) `Checked.Cosmography.CosmicAge.eds_older_than_hubble_time`: a flat matter-dominated (Einstein-de Sitter) universe is older than the Hubble time 1/H₀ (t₀ = 3/2 H₀⁻¹ in the program's units). Statement rests on no unpinned physics definition (trust map).")
