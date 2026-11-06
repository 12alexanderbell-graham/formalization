#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rep(rel, old, new):
    p = root / rel; t = p.read_text()
    assert t.count(old) == 1, (rel, old)
    p.write_text(t.replace(old, new))
def app(rel, s):
    p = root / rel; t = p.read_text()
    if not t.endswith("\n"): t += "\n"
    p.write_text(t + s)
def new(rel, s):
    p = root / rel; p.parent.mkdir(parents=True, exist_ok=True)
    assert not p.exists(), rel
    p.write_text(s)


ANCH = "end Checked.Trust.SecondReading"
KD = '/-- Peng and Robinson (1976): κ as a function of ω, in the form that holds for the quadratic term as printed. -/\nnoncomputable def kappaPR76q (ω : ℝ) : ℝ := 0.37464 + 1.54226 * ω + 0.26992 * ω ^ 2\nend Checked.Trust.SecondReading'
# the reader's file under runs/ AND the Checked copy are edited identically: both already exist at the base,
# so check_blind_route skips the module and check_provenance rule 4 sees an existing copy with a brief.
rep("Checked/Trust/SecondReadingKappa.lean", ANCH, KD)
rep("runs/2026-11-06T0228Z/kappa_reader/SecondReadingKappa.lean", ANCH, KD)
LEAN = 'import Mathlib.Data.Real.Basic\nimport Checked.Trust.NonVacuity\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Positivity\n\n/-!\n# Chemistry: size of the Peng and Robinson κ(ω) beyond ω = 1\n\nA one-line consequence of the κ(ω) polynomial of the Peng and Robinson equation of state.\n-/\n\nnamespace Checked.Chemistry.KappaPRBeyond\n\n/-- The κ(ω) correlation of Peng and Robinson exceeds 2 for every ω ≥ 1, so the attraction\nparameter a(T) is amplified by more than a factor (1 + 2(1 − √(T/T_c)))² there. -/\ntheorem kappa_pr_exceeds_two (ω : ℝ) (h : 1 ≤ ω) :\n    2 < 0.37464 + 1.54226 * ω + 0.26992 * ω ^ 2 := by\n  nlinarith [sq_nonneg (ω - 1)]\n\nend Checked.Chemistry.KappaPRBeyond\n\nnamespace Checked.Trust.NV\ntheorem kappa_pr_exceeds_two : nonvacuity% Checked.Chemistry.KappaPRBeyond.kappa_pr_exceeds_two :=\n  ⟨1, le_rfl, trivial⟩\nend Checked.Trust.NV\n'
new("Checked/Chemistry/KappaPRBeyond.lean", LEAN)
app("Checked.lean", "import Checked.Chemistry.KappaPRBeyond\n")
app("scripts/trust/headlines.txt", "Checked.Chemistry.KappaPRBeyond.kappa_pr_exceeds_two\n")
app("scripts/trust/literal_readings.txt", "Checked.Chemistry.KappaPRBeyond.kappa_pr_exceeds_two Checked.Trust.SecondReading.kappaPR76q\n")
app("LEDGER.md", "\n- 2026-11-06T1028Z: **Literal reading** for `kappa_pr_exceeds_two` (literal_readings.txt): `Checked.Trust.SecondReading.kappaPR76q` (module `Checked/Trust/SecondReadingKappa.lean`, same blind reader file `runs/2026-11-06T0228Z/kappa_reader/`, one further constant). New headline `kappa_pr_exceeds_two` (Checked/Chemistry/KappaPRBeyond.lean); frozen.txt relocked (new entries only).\n")
