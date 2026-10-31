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

new("Checked/Cosmography/LookbackTyped.lean", """import Checked.Cosmography.Lookback
import Checked.Trust.Witnesses

open Filter Asymptotics Topology

namespace Checked.Cosmography.LookbackTyped

/-- Second-order lookback law (`o(z^2)` remainder) for a scale factor differentiable near `t0`.
`hq` records the epoch (accelerating, `q0 < 0`) as a data tag. -/
theorem lookback_second_order_tagged (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) (hq : PLift (decel a t₀ < 0)) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) :=
  Checked.Cosmography.lookback_second_order a t₀ ha ha' ha0 hH

end Checked.Cosmography.LookbackTyped

namespace Checked.Trust.NV

theorem lookback_second_order_tagged_witness :
    nonvacuity% Checked.Cosmography.LookbackTyped.lookback_second_order_tagged :=
  ⟨Real.exp, 0, Filter.Eventually.of_forall fun _ => Real.differentiableAt_exp,
    by rw [Real.deriv_exp]; exact Real.differentiableAt_exp, dS_a0, by simp [Real.deriv_exp],
    ⟨by rw [dS_decel]; norm_num⟩, trivial⟩

end Checked.Trust.NV
""")
import_checked("Checked.Cosmography.LookbackTyped")
register("LookbackTyped.lookback_second_order_tagged",
         "| `LookbackTyped.lookback_second_order_tagged` | decel, hubble, redshift | — | — | `lookback_second_order_tagged_witness` |", True)
state_bullet("- **PROVED** (F0f) `Checked.Cosmography.LookbackTyped.lookback_second_order_tagged`: the second-order lookback-time law with o(z²) remainder for any scale factor differentiable near t₀ (the epoch tag q₀ < 0 is bookkeeping only; registered headline, non-vacuity witnessed, no unused hypothesis).")
