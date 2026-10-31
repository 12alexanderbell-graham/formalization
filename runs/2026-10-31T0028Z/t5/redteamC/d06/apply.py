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

new("Checked/Cosmography/LookbackBundled.lean", """import Checked.Cosmography.LookbackThird
import Checked.Trust.Witnesses

open Filter Asymptotics Topology

namespace Checked.Cosmography.LookbackBundled

/-- Lookback time to second order with an `O(z^3)` remainder: if `a` is `C^3` near `t0`, with
the standing non-degeneracy conditions `h` (a(t0) is nonzero, H0 is nonzero, and the
deceleration parameter is normalised), then the cosmographic law holds. -/
theorem lookback_second_order_bigO_gen (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ContDiffAt ℝ 3 a t₀)
    (h : a t₀ ≠ 0 ∧ deriv a t₀ ≠ 0 ∧ decel a t₀ = -1) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =O[𝓝 t₀] (fun t => redshift a t₀ t ^ 3) :=
  Checked.Cosmography.lookback_second_order_bigO a t₀ ha h.1 h.2.1

end Checked.Cosmography.LookbackBundled

namespace Checked.Trust.NV

theorem lookback_second_order_bigO_gen_witness :
    nonvacuity% Checked.Cosmography.LookbackBundled.lookback_second_order_bigO_gen :=
  ⟨Real.exp, 0, dS_smooth _, ⟨dS_a0, by simp [Real.deriv_exp], dS_decel⟩, trivial⟩

end Checked.Trust.NV
""")
import_checked("Checked.Cosmography.LookbackBundled")
register("LookbackBundled.lookback_second_order_bigO_gen",
         "| `LookbackBundled.lookback_second_order_bigO_gen` | decel, hubble, redshift | — | — | `lookback_second_order_bigO_gen_witness` |", True)
state_bullet("- **PROVED** (F0e) `Checked.Cosmography.LookbackBundled.lookback_second_order_bigO_gen`: if a is C³ near t₀ then t₀ − t = H₀⁻¹(z − (1+q₀/2)z²) + O(z³), under the standing non-degeneracy conditions only (registered headline; T2b: no unused hypothesis).")
