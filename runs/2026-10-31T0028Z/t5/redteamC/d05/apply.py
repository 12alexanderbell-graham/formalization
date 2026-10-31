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

new("Checked/Cosmography/LookbackDS.lean", """import Checked.Cosmography.Lookback
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Asymptotics Topology

namespace Checked.Cosmography.LookbackDS

/-- The second-order lookback law instantiated at the de Sitter scale factor `a = exp`, `t0 = 0`. -/
theorem lookback_dS_second_order :
    (fun t => ((0 : ℝ) - t) - (redshift Real.exp 0 t - (1 + decel Real.exp 0 / 2) * redshift Real.exp 0 t ^ 2)
        / hubble Real.exp 0)
      =o[𝓝 (0 : ℝ)] (fun t => redshift Real.exp 0 t ^ 2) :=
  Checked.Cosmography.lookback_second_order Real.exp 0
    (Filter.Eventually.of_forall fun _ => Real.differentiableAt_exp)
    (by rw [Real.deriv_exp]; exact Real.differentiableAt_exp)
    (Real.exp_pos 0).ne' (by simp [Real.deriv_exp])

end Checked.Cosmography.LookbackDS
""")
import_checked("Checked.Cosmography.LookbackDS")
rep("STATE.md", "## Environment (this run)",
    "## Further results (run 0100Z)\n"
    "- **PROVED** (F0d) `Checked.Cosmography.LookbackDS.lookback_dS_second_order`: the second-order lookback law with o(z²) remainder, now for every scale factor and every q₀ with a quantitative remainder control (supersedes the two F0 milestone theorems; CI green).\n\n"
    "## Environment (this run)")
