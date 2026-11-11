import Checked.Trust.NonVacuity
import Checked.FSSep.SSlowSol
import Checked.FalknerSkan.Separation
import Checked.FalknerSkan.SeparationEqual

/-!
# Hypothesis necessity witnesses, Falkner–Skan separation (trust track T2b, run 2026-11-11T0232Z)

The faster-than-every-exponential hypothesis of each of the two solutions in
`Checked.FalknerSkan.SeparationEqual.fs_separation_equal` is needed: the certified slow-approach chain at
the upper window end gives a zero-wall-shear solution with the velocity profile tending to the edge value
and positive second derivative beyond the wall, at a parameter strictly above the separation value of
`Checked.FalknerSkan.Separation.fs_separation_exists`, so the two parameters differ.
-/

namespace Checked.Trust.NCC
open Set Filter Topology

theorem fs_separation_equal_h9 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 9 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  obtain ⟨g, pg, qg, hg, hpg, hqg, hg0, hpg0, hqg0, hlg, hposg⟩ := Checked.FSSep.SSlowSol.slow_hi
  refine ⟨-(1988377350 / 10000000000 : ℝ), β, g, pg, qg, f, p, q, hg, hpg, hqg, hg0, hpg0, hqg0, hlg,
    hposg, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec, ?_⟩
  intro h
  have := hβ.2
  linarith

theorem fs_separation_equal_h18 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 18 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  obtain ⟨g, pg, qg, hg, hpg, hqg, hg0, hpg0, hqg0, hlg, hposg⟩ := Checked.FSSep.SSlowSol.slow_hi
  refine ⟨β, -(1988377350 / 10000000000 : ℝ), f, p, q, g, pg, qg, hf, hp, hq, hf0, hp0, hq0, hlim, hpos,
    hdec, hg, hpg, hqg, hg0, hpg0, hqg0, hlg, hposg, ?_⟩
  intro h
  have := hβ.2
  linarith

end Checked.Trust.NCC
