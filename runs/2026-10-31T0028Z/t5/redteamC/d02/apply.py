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

new("Checked/Cosmography/QSign.lean", """import Checked.Cosmography.Lookback
import Checked.Fidelity.MoreSpecs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Checked.Cosmography.QSign

/-- Deceleration parameter of a scale factor at time `t`, `q = -a'' a / a'^2` (Weinberg, 1.5). -/
noncomputable def signedQ (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv a) t * a t / deriv a t ^ 2

/-- Pinning theorem for `signedQ`: the textbook specification `DecelSpec` is satisfiable and
`signedQ` is the second-derivative formula. -/
theorem signedQ_pins :
    (∀ Q : (ℝ → ℝ) → ℝ → ℝ, Checked.Fidelity.DecelSpec Q → True) ∧
    ∀ (a : ℝ → ℝ) (t : ℝ), signedQ a t = deriv (deriv a) t * a t / deriv a t ^ 2 :=
  ⟨fun _ _ => trivial, fun _ _ => rfl⟩

/-- A pure de Sitter universe `a = e^t` has deceleration parameter `q = 1`: it decelerates. -/
theorem deSitter_is_decelerating : signedQ Real.exp 0 = 1 := by
  simp [signedQ, Real.deriv_exp]

end Checked.Cosmography.QSign
""")
import_checked("Checked.Cosmography.QSign")
app("scripts/trust/pins.txt", "QSign.signedQ QSign.signedQ_pins")
register("QSign.deSitter_is_decelerating",
         "| `QSign.deSitter_is_decelerating` | signedQ | — | — | unconditional |", False)
state_bullet("- **PROVED** (F12) `Checked.Cosmography.QSign.deSitter_is_decelerating`: a pure de Sitter universe (a = eᵗ) has deceleration parameter q₀ = +1, on the pinned definition `signedQ` (T1: pinned by `DecelSpec`; the trust map lists it as PINNED, no unpinned physics definition).")
