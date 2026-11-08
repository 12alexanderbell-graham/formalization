#!/usr/bin/env python3
"""Promote Work/FalknerSkan/HalfBounded.lean to Checked (pattern of
runs/2026-11-08T1228Z/scripts/promote_bd.py): `Work.` -> `Checked.` in every name, module doc
replaced by number-free text; the Work file imports only Checked modules, so imports are kept.
Statements and proofs otherwise byte-identical to Work. Registers headlines, literal readings,
audits and NV witnesses."""
import re, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[3]
DOC = ("Falkner–Skan wedge flow with the pressure-gradient coefficient one half: every solution of the "
       "boundary-value problem whose velocity profile is bounded by one in absolute value on the closed "
       "half-line has its wall shear inside the window of the statement, any two such solutions are equal "
       "on the closed half-line, and a solution with velocity profile in the half-open unit interval exists; "
       "obtained from the Homann theorems of `Checked.FalknerSkan.Bounded` by the similarity scaling of "
       "`Checked.FalknerSkan.FSScale`")
src = (ROOT / "Work/FalknerSkan/HalfBounded.lean").read_text(encoding="utf-8")
s = src.replace("Work.", "Checked.")
s, k = re.subn(r"/-!.*?-/", lambda m: f"/-! {DOC}. Module `HalfBounded`, promoted from `Work/FalknerSkan/HalfBounded.lean`. -/", s, count=1, flags=re.S)
assert k == 1 and "Work." not in s and "sorry" not in s and "native_decide" not in s
s = re.sub(r"(?m)^#print axioms.*\n", "", s)
(ROOT / "Checked/FalknerSkan/HalfBounded.lean").write_text(s, encoding="utf-8")

def add_after(path, anchor, lines):
    p = ROOT / path; t = p.read_text(encoding="utf-8")
    if all(l in t for l in lines): return
    assert t.count(anchor + "\n") == 1, (path, anchor)
    t = t.replace(anchor + "\n", anchor + "\n" + "".join(l + "\n" for l in lines), 1)
    p.write_text(t, encoding="utf-8")

N = "Checked.FalknerSkan.HalfBounded."
add_after("Checked.lean", "import Checked.FalknerSkan.Bounded", ["import Checked.FalknerSkan.HalfBounded"])
add_after("scripts/trust/headlines.txt", "Checked.FalknerSkan.Bounded.homann_exists_bounded",
          [N + "fs_half_bounded_window", N + "fs_half_bounded_equal", N + "fs_half_exists_bounded"])
R = "Checked.Trust.SecondReading."
base = " ".join(R + x for x in ("fskWedgeRhs", "fskHalfLineTyped", "fskHalfLine", "fskWall", "fskEdge"))
add_after("scripts/trust/literal_readings.txt",
          [l for l in (ROOT / "scripts/trust/literal_readings.txt").read_text().splitlines()
           if l.startswith("Checked.FalknerSkan.Bounded.homann_exists_bounded ")][0],
          [N + "fs_half_bounded_window " + base + " " + R + "fskWedgeShear " + R + "stagSpeedBounded",
           N + "fs_half_bounded_equal " + base + " " + R + "stagSpeedBounded",
           N + "fs_half_exists_bounded " + base + " " + R + "fskWedgeShear " + R + "stagForwardBelow"])
add_after("scripts/trust/audits.txt", "Blind.Bounded.homann_E",
          ["Blind.FSHalf.toSys", "Blind.FSHalf.fs_W", "Blind.FSHalf.fs_U", "Blind.FSHalf.fs_E"])
print("promoted")

W = ROOT / "Checked/Trust/Witnesses.lean"
t = W.read_text(encoding="utf-8")
if "fs_half_bounded_window" not in t:
    t = t.replace("import Checked.FalknerSkan.Bounded\n", "import Checked.FalknerSkan.Bounded\nimport Checked.FalknerSkan.HalfBounded\n", 1)
    nv = '''/-! Falkner–Skan β = 1/2 bounded class (run 2026-11-08T1628Z): the solution of
`Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded`, whose velocity profile lies in the
half-open unit interval, hence between minus one and one; used twice for the equality theorem. -/

theorem fs_half_bounded_window : nonvacuity% Checked.FalknerSkan.HalfBounded.fs_half_bounded_window := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim,
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩, trivial⟩

theorem fs_half_bounded_equal : nonvacuity% Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hb, -⟩ :=
    Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded
  have hb' : ∀ η ∈ Set.Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 :=
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩
  exact ⟨f, p, q, f, p, q, hf, hp, hq, hf0, hp0, hlim, hb', hf, hp, hq, hf0, hp0, hlim, hb', 0, Set.mem_Ici.2 le_rfl, trivial⟩

end Checked.Trust.NV'''
    assert t.rstrip().endswith("end Checked.Trust.NV")
    t = t.rstrip()[: -len("end Checked.Trust.NV")] + nv + "\n"
    W.write_text(t, encoding="utf-8")
print("witnesses")
