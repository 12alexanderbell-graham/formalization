import Checked.Trust.NonVacuity
import Checked.Trust.ExpFlow
import Checked.FalknerSkan.Limit
import Checked.FalknerSkan.LimitTenth
import Checked.FalknerSkan.MonotoneWindow
import Checked.FalknerSkan.Bounded
import Checked.FalknerSkan.HalfBounded
import Checked.FalknerSkan.FifthBounded
import Checked.FalknerSkan.TenthBounded
/-! Necessity of the far-field condition (the velocity tends to one) in the limit-window, limit-uniqueness and monotone-window headlines of the Hiemenz, Homann and Falkner–Skan (one half, one fifth, one tenth) problems. Without it the boundary-value problem is an initial-value problem with a free wall shear: the solution with wall shear ten exists on the whole half-line (`Checked.Trust.ExpFlow.exists_wall_ten`), its shear stays positive and its velocity grows without bound, and its wall shear lies outside every window; beside the solution of each existence headline it also breaks uniqueness. The wall velocity is needed in `Checked.FalknerSkan.Limit.fs_monotone_of_limit`: the uniform stream has zero shear. Module `NecessityBB`. -/

namespace Checked.Trust.NCBB
open Set Filter Topology

/-- The far-field condition is needed in `hiemenz_limit_window`: the solution with wall shear ten
exists on the whole half-line and its wall shear is outside the window. -/
theorem hiemenz_limit_window_h6 : necessity% Checked.FalknerSkan.Limit.hiemenz_limit_window 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h

theorem hiemenz_limit_equal_h6 : necessity% Checked.FalknerSkan.Limit.hiemenz_limit_equal 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0,
    hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

theorem hiemenz_limit_equal_h12 : necessity% Checked.FalknerSkan.Limit.hiemenz_limit_equal 12 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  refine ⟨f₂, p₂, q₂, f, p, q, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂,
    hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

/-- The far-field condition is needed in `hiemenz_monotone_window`: the solution with wall shear ten
has positive shear on the whole half-line and its wall shear is outside the window. -/
theorem hiemenz_monotone_window_h6 : necessity% Checked.FalknerSkan.MonotoneWindow.hiemenz_monotone_window 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, hpos⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, hpos, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h

/-- The far-field condition is needed in `homann_limit_window`: the solution with wall shear ten
exists on the whole half-line and its wall shear is outside the window. -/
theorem homann_limit_window_h6 : necessity% Checked.FalknerSkan.Limit.homann_limit_window 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 2) (β := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h

theorem homann_limit_equal_h6 : necessity% Checked.FalknerSkan.Limit.homann_limit_equal 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 2) (β := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.Bounded.homann_exists_bounded
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0,
    hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

theorem homann_limit_equal_h12 : necessity% Checked.FalknerSkan.Limit.homann_limit_equal 12 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 2) (β := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.Bounded.homann_exists_bounded
  refine ⟨f₂, p₂, q₂, f, p, q, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂,
    hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

/-- The far-field condition is needed in `homann_monotone_window`: the solution with wall shear ten
has positive shear on the whole half-line and its wall shear is outside the window. -/
theorem homann_monotone_window_h6 : necessity% Checked.FalknerSkan.MonotoneWindow.homann_monotone_window 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, hpos⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 2) (β := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, hpos, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h

/-- The far-field condition is needed in `fs_half_limit_window`: the solution with wall shear ten
exists on the whole half-line and its wall shear is outside the window. -/
theorem fs_half_limit_window_h6 : necessity% Checked.FalknerSkan.Limit.fs_half_limit_window 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h

theorem fs_half_limit_equal_h6 : necessity% Checked.FalknerSkan.Limit.fs_half_limit_equal 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0,
    hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

theorem fs_half_limit_equal_h12 : necessity% Checked.FalknerSkan.Limit.fs_half_limit_equal 12 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.HalfBounded.fs_half_exists_bounded
  refine ⟨f₂, p₂, q₂, f, p, q, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂,
    hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

/-- The far-field condition is needed in `fs_fifth_limit_window`: the solution with wall shear ten
exists on the whole half-line and its wall shear is outside the window. -/
theorem fs_fifth_limit_window_h6 : necessity% Checked.FalknerSkan.Limit.fs_fifth_limit_window 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h

theorem fs_fifth_limit_equal_h6 : necessity% Checked.FalknerSkan.Limit.fs_fifth_limit_equal 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.FifthBounded.fs_fifth_exists_bounded
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0,
    hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

theorem fs_fifth_limit_equal_h12 : necessity% Checked.FalknerSkan.Limit.fs_fifth_limit_equal 12 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 5) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.FifthBounded.fs_fifth_exists_bounded
  refine ⟨f₂, p₂, q₂, f, p, q, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂,
    hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

/-- The far-field condition is needed in `fs_tenth_limit_window`: the solution with wall shear ten
exists on the whole half-line and its wall shear is outside the window. -/
theorem fs_tenth_limit_window_h6 : necessity% Checked.FalknerSkan.LimitTenth.fs_tenth_limit_window 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨f, p, q, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  norm_num at h

theorem fs_tenth_limit_equal_h6 : necessity% Checked.FalknerSkan.LimitTenth.fs_tenth_limit_equal 6 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.TenthBounded.fs_tenth_exists_bounded
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0,
    hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

theorem fs_tenth_limit_equal_h12 : necessity% Checked.FalknerSkan.LimitTenth.fs_tenth_limit_equal 12 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hq0, -⟩ := Checked.Trust.ExpFlow.exists_wall_ten (c := 1) (β := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂, -, -, hhi⟩ := Checked.FalknerSkan.TenthBounded.fs_tenth_exists_bounded
  refine ⟨f₂, p₂, q₂, f, p, q, hf₂, hp₂, hq₂, hf₂0, hp₂0, hlim₂,
    hf, hp, fun η hη => (hq η hη).congr_deriv (by ring), hf0, hp0, 0, Set.mem_Ici.2 le_rfl, ?_⟩
  rintro ⟨-, -, he⟩
  rw [hq0] at he
  norm_num at hhi
  linarith

/-- The wall velocity p(0) = 0 is needed in `fs_monotone_of_limit`: the uniform stream f = η, p = 1,
q = 0 solves the equation for every β, has f(0) = 0 and p → 1, and its shear is zero. -/
theorem fs_monotone_of_limit_h7 : necessity% Checked.FalknerSkan.Limit.fs_monotone_of_limit 7 := by
  refine ⟨1, one_pos, le_rfl, fun η => η, fun _ => 1, fun _ => 0, fun η _ => ?_, fun η _ => ?_,
    fun η _ => ?_, rfl, tendsto_const_nhds, 0, Set.mem_Ici.2 le_rfl, lt_irrefl 0⟩
  · exact (hasDerivAt_id η).hasDerivWithinAt
  · exact (hasDerivAt_const η (1 : ℝ)).hasDerivWithinAt
  · have := (hasDerivAt_const η (0 : ℝ)).hasDerivWithinAt (s := Ici 0)
    convert this using 1
    ring

end Checked.Trust.NCBB
