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
KD = '/-- The volume-term parameters (u, w) of the cubic, as a pair. -/\nnoncomputable def cubicUW : ℝ × ℝ := (1, 0)\n/-- The reduced temperature of the saturation pressure, applied to the critical temperature T. -/\nnoncomputable def satTemp (T : ℝ) : ℝ := 7 / 10 * T\nend Checked.Trust.SecondReading'
rep("Checked/Trust/SecondReadingRob.lean", ANCH, KD)
rep("runs/2026-11-06T0428Z/rob_reader/SecondReadingRob.lean", ANCH, KD)
LEAN = 'import Checked.Chemistry.RKAcentric\nimport Checked.Trust.Witnesses\n\n/-!\n# Chemistry: the coexistence state of a cubic fluid at seven tenths of the critical temperature\n\nA restatement of `Checked.Chemistry.RKAcentric.rk_coexistence_exists`.\n-/\n\nnamespace Checked.Chemistry.WaalsFluid\nopen Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence\n\n/-- van-der-Waals fluid (attraction A/√T): at any critical point (T_c > 0, v_c > b) there is a Maxwell\ncoexistence state at T = 0.7 T_c with liquid volume above the co-volume b, and its pressure is 0.087\ntimes the critical pressure (3 decimals) and its acentric factor 0.058 (3 decimals). -/\ntheorem waals_fluid_exists (R A b Tc vc : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)\n    (hTc : 0 < Tc) (hvc : b < vc)\n    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc) :\n    ∃ vl vg ps, b < vl ∧\n      IsMaxwellCoexistence (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps ∧\n      RoundsTo (ps / cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc) 0.087 3 ∧\n      RoundsTo (acentric ps (cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc)) 0.058 3 :=\n  Checked.Chemistry.RKAcentric.rk_coexistence_exists R A b Tc vc hR hA hb hTc hvc hc\n\nend Checked.Chemistry.WaalsFluid\n\nnamespace Checked.Trust.NV\ntheorem waals_fluid_exists : nonvacuity% Checked.Chemistry.WaalsFluid.waals_fluid_exists := by\n  obtain ⟨Tc, vc, hT, hv, hc⟩ := rk_crit_witness\n  exact ⟨1, Real.sqrt Tc, 1, Tc, vc, one_pos, Real.sqrt_pos.2 hT, one_pos, hT, hv, hc, trivial⟩\nend Checked.Trust.NV\n'
new("Checked/Chemistry/WaalsFluid.lean", LEAN)
app("Checked.lean", "import Checked.Chemistry.WaalsFluid\n")
app("scripts/trust/headlines.txt", "Checked.Chemistry.WaalsFluid.waals_fluid_exists\n")
app("scripts/trust/literal_readings.txt", "Checked.Chemistry.WaalsFluid.waals_fluid_exists Checked.Trust.SecondReading.cubicUW Checked.Trust.SecondReading.satTemp\n")
app("LEDGER.md", "\n- 2026-11-06T1028Z: **Literal reading** for `waals_fluid_exists` (literal_readings.txt): `Checked.Trust.SecondReading.cubicUW`, `satTemp` (module `Checked/Trust/SecondReadingRob.lean`, same reader file `runs/2026-11-06T0428Z/rob_reader/`, two further constants). New headline `waals_fluid_exists` (Checked/Chemistry/WaalsFluid.lean), a restatement of `rk_coexistence_exists`; frozen.txt relocked (new entries only).\n")
