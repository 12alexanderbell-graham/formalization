"""Emit Checked/Trust/NecessityBB.lean: hypothesis 6 (p -> 1) of the limit windows, the limit
uniqueness statements (6 and 12) and the monotone windows, witnessed by the wall-shear-ten solution
of Checked.Trust.ExpFlow.exists_wall_ten (run 2026-11-20T0028Z)."""
rows = [
    # name, module, c, beta (Lean), existence theorem, rhs written as in the headline
    ("hiemenz", "Limit", "1", "1", "Checked.FalknerSkan.Bounded.hiemenz_exists_bounded"),
    ("homann", "Limit", "2", "1", "Checked.FalknerSkan.Bounded.homann_exists_bounded"),
    ("fs_half", "Limit", "1", "1 / 2", "Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded"),
    ("fs_fifth", "Limit", "1", "1 / 5", "Checked.FalknerSkan.FifthBounded.fs_fifth_exists_bounded"),
    ("fs_tenth", "LimitTenth", "1", "1 / 10", "Checked.FalknerSkan.TenthBounded.fs_tenth_exists_bounded"),
]
out = []
out.append("""import Checked.Trust.NonVacuity
import Checked.Trust.ExpFlow
import Checked.FalknerSkan.Limit
import Checked.FalknerSkan.LimitTenth
import Checked.FalknerSkan.MonotoneWindow
import Checked.FalknerSkan.Bounded
import Checked.FalknerSkan.HalfBounded
import Checked.FalknerSkan.FifthBounded
import Checked.FalknerSkan.TenthBounded
/-! Necessity of the far-field condition (the velocity tends to one) in the limit-window, limit-uniqueness and monotone-window headlines of the Hiemenz, Homann and Falkner–Skan (one half, one fifth, one tenth) problems. Without it the boundary-value problem is an initial-value problem with a free wall shear: the solution with wall shear ten exists on the whole half-line (`Checked.Trust.ExpFlow.exists_wall_ten`), its shear stays positive and its velocity grows without bound, and its wall shear lies outside every window; beside the solution of each existence headline it also breaks uniqueness. Module `NecessityBB`. -/

namespace Checked.Trust.NCBB
open Set Filter Topology
""")
def wit(c, b):
    return (f"Checked.Trust.ExpFlow.exists_wall_ten (c := {c}) (β := {b}) (by norm_num) (by norm_num)\n"
            f"    (by norm_num) (by norm_num)")
for (n, mod, c, b, ex) in rows:
    win = f"Checked.FalknerSkan.{mod}.{n}_limit_window"
    eq = f"Checked.FalknerSkan.{mod}.{n}_limit_equal"
    out.append(f"""/-- The far-field condition is needed in `{n}_limit_window`: the solution with wall shear ten
exists on the whole half-line and its wall shear is outside the window. -/
theorem {n}_limit_window_h6 : necessity% {win} 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := {wit(c, b)}
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h

theorem {n}_limit_equal_h6 : necessity% {eq} 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := {wit(c, b)}
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := {ex}
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0,
    hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

theorem {n}_limit_equal_h12 : necessity% {eq} 12 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := {wit(c, b)}
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := {ex}
  refine ⟨f₂, p₂, q₂, f, p, q, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂,
    hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith
""")
    if n in ("hiemenz", "homann"):
        mw = f"Checked.FalknerSkan.MonotoneWindow.{n}_monotone_window"
        out.append(f"""/-- The far-field condition is needed in `{n}_monotone_window`: the solution with wall shear ten
has positive shear on the whole half-line and its wall shear is outside the window. -/
theorem {n}_monotone_window_h6 : necessity% {mw} 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, hpos⟩ := {wit(c, b)}
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, hpos, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h
""")
out.append("""/-- The wall velocity p(0) = 0 is needed in `fs_monotone_of_limit`: the uniform stream f = η, p = 1,
q = 0 solves the equation for every β, has f(0) = 0 and p → 1, and its shear is zero. -/
theorem fs_monotone_of_limit_h7 : necessity% Checked.FalknerSkan.Limit.fs_monotone_of_limit 7 := by
  refine ⟨1, one_pos, le_rfl, fun η => η, fun _ => 1, fun _ => 0, fun η _ => ?_, fun η _ => ?_,
    fun η _ => ?_, rfl, tendsto_const_nhds, 0, Set.mem_Ici.2 le_rfl, lt_irrefl 0⟩
  · exact (hasDerivAt_id η).hasDerivWithinAt
  · exact (hasDerivAt_const η (1 : ℝ)).hasDerivWithinAt
  · have := (hasDerivAt_const η (0 : ℝ)).hasDerivWithinAt (s := Ici 0)
    convert this using 1
    ring
""")
out.append("end Checked.Trust.NCBB\n")
open("Checked/Trust/NecessityBB.lean", "w").write("\n".join(out))
