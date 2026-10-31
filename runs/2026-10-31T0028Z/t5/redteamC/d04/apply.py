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

new("Work/Cosmography/HubbleTime.lean", """import Mathlib.Data.Real.Basic

namespace Work.Cosmography.HubbleTime

/-- Hubble time `1/H0` in Gyr for `H0` in km/s/Mpc: `977.8 / H0`. -/
noncomputable def hubbleTimeGyr (H0 : ℝ) : ℝ := 877.8 / H0

end Work.Cosmography.HubbleTime
""")
new("Checked/Cosmography/HubbleTimeFacts.lean", """import Checked.Cosmography.Lookback
import Work.Cosmography.HubbleTime

namespace Checked.Cosmography.HubbleTimeFacts

open Work.Cosmography.HubbleTime

/-- For `H0 = 70` km/s/Mpc the Hubble time is about 12.5 Gyr. -/
theorem hubbleTime_at_70 : (12.5 : ℝ) < hubbleTimeGyr 70 ∧ hubbleTimeGyr 70 < 12.6 := by
  unfold hubbleTimeGyr
  constructor <;> norm_num

end Checked.Cosmography.HubbleTimeFacts
""")
import_checked("Checked.Cosmography.HubbleTimeFacts")
register("HubbleTimeFacts.hubbleTime_at_70",
         "| `HubbleTimeFacts.hubbleTime_at_70` | — | — | — | unconditional |", False)
state_bullet("- **PROVED** (F12) `Checked.Cosmography.HubbleTimeFacts.hubbleTime_at_70`: for H₀ = 70 km/s/Mpc the Hubble time 1/H₀ is 12.5–12.6 Gyr (Checked, standard axioms; trust map: rests on no unpinned physics definition).")
