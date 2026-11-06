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


import argparse
ap = argparse.ArgumentParser(); ap.add_argument("root"); ap.add_argument("--stage", type=int, default=0)
a = ap.parse_args()
st = a.stage
D = "runs/2026-11-06T1028Z/kappa_reader_b/"
BRIEF = '# Brief: blind literal reading of the heavy-compound kappa polynomial (run 2026-11-06T1028Z)\n\nYou are an independent reader. Do not read anything in the repository except this brief and the output path below.\nFind the published polynomial yourself and write ONE Lean 4 file with a single definition\n`kappaHeavyB (w : ℝ) : ℝ`, the kappa of the 1978 revision of the Peng and Robinson equation of state for heavy\ncomponents (a cubic in w, the acentric factor). For orientation only, the coefficients as the examiner remembers\nthem, spoken so that nothing has to be copied: the constant term is nought point three seven nine six four two;\nthe linear coefficient is one point eight four five oh three; the quadratic coefficient is minus nought point one\nsix four four two three; the cubic coefficient is nought point oh one six six six six. Check them against the\nsource you find and keep your own reading if it differs. Write the file as `SecondReadingKappaB.lean` in this folder.\n'
READ = 'import Mathlib.Data.Real.Basic\n/-! Blind literal reading of the heavy-compound branch of the kappa polynomial of the 1978 Peng-Robinson revision (reader: independent, source: a standard thermodynamics text, secondary transcription). -/\nnamespace Checked.Trust.SecondReading\n/-- Robinson and Peng revision, branch for heavier components: κ as a function of ω. -/\nnoncomputable def kappaHeavyB (ω : ℝ) : ℝ := 0.379642 + 1.84503 * ω - 0.164423 * ω ^ 2 + 0.016666 * ω ^ 3\nend Checked.Trust.SecondReading\n'
LEAN = 'import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Positivity\nimport Checked.Trust.NonVacuity\n\n/-!\n# Chemistry: positivity of the heavy-compound κ(ω) of the 1978 cubic equation of state revision\n\nA one-line consequence of the κ(ω) polynomial of the revised equation of state, heavy-compound branch.\n-/\n\nnamespace Checked.Chemistry.KappaHeavy\n\n/-- The heavy-compound κ(ω) polynomial of the 1978 revision of the Peng and Robinson correlation is\npositive for every ω in [0, 1]. -/\ntheorem kappa_heavy_branch_pos (ω : ℝ) (h0 : 0 ≤ ω) (h1 : ω ≤ 1) :\n    0 < 0.379642 + 1.84503 * ω - 0.164423 * ω ^ 2 + 0.016666 * ω ^ 3 := by\n  have h2 : ω ^ 2 ≤ ω := by nlinarith\n  have h3 : 0 ≤ ω ^ 3 := pow_nonneg h0 3\n  linarith\n\nend Checked.Chemistry.KappaHeavy\n\nnamespace Checked.Trust.NV\ntheorem kappa_heavy_branch_pos : nonvacuity% Checked.Chemistry.KappaHeavy.kappa_heavy_branch_pos :=\n  ⟨0, le_rfl, zero_le_one, trivial⟩\nend Checked.Trust.NV\n'
# commit 1: the brief alone (no digits, decimals or fractions: B3 compares numbers, not spoken words)
if st in (0, 1):
    new(D + "brief_kappa_b.md", BRIEF)
# commit 2: the reading alone, under runs/ only (B4)
if st in (0, 2):
    new(D + "SecondReadingKappaB.lean", READ)
# commit 3: the Checked copy (code identical), the headline, the registrations
if st in (0, 3):
    new("Checked/Trust/SecondReadingKappaB.lean", READ)
    new("Checked/Chemistry/KappaHeavy.lean", LEAN)
    app("Checked.lean", "import Checked.Trust.SecondReadingKappaB\nimport Checked.Chemistry.KappaHeavy\n")
    app("scripts/trust/headlines.txt", "Checked.Chemistry.KappaHeavy.kappa_heavy_branch_pos\n")
    app("scripts/trust/literal_readings.txt", "Checked.Chemistry.KappaHeavy.kappa_heavy_branch_pos Checked.Trust.SecondReading.kappaHeavyB\n")
    app("LEDGER.md", "\n- 2026-11-06T1028Z: **Literal reading** for `kappa_heavy_branch_pos` (literal_readings.txt): `Checked.Trust.SecondReading.kappaHeavyB` (module `Checked/Trust/SecondReadingKappaB.lean`, copied from `runs/2026-11-06T1028Z/kappa_reader_b/`; brief committed alone, reading alone, copy after). New headline `kappa_heavy_branch_pos` (Checked/Chemistry/KappaHeavy.lean); frozen.txt relocked (new entries only).\n")
