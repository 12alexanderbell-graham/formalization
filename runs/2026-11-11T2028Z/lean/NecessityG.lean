import Checked.Trust.NonVacuity
import Checked.FalknerSkan.Limit
import Checked.FalknerSkan.LimitTenth
import Checked.FalknerSkan.BoundedLimit

/-!
# The velocity bound and the far-field condition of the bounded-class headlines (T2b, run 2026-11-11T2028Z)

The window and equality headlines of the class −1 ≤ f' ≤ 1 (Hiemenz, Homann, Falkner–Skan β = 1/2, 1/5,
1/10) carry the bound as one hypothesis with two parts (lower and upper bound of the velocity profile on
the closed half-line) next to the far-field condition f' → 1.

* Each part of the bound is redundant: the bound-free headlines (`Limit`, `LimitTenth`) prove the
  statement with the whole bound dropped, so with either part dropped too (`dropped% thm i j`).
* The far-field condition is redundant when the bound is kept: `Checked.FalknerSkan.BoundedLimit`
  proves that f(0) = 0, f'(0) = 0 and −1 ≤ f' ≤ 1 on the closed half-line force f' → 1 for every
  solution (`dropped% thm i`).

The two redundancies hold each alone, not together.
-/

namespace Checked.Trust.NecessityG
open Set Filter Topology

theorem hiemenz_bounded_window_p7_1 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_window 7 1 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.Limit.hiemenz_limit_window f p q hf hp hq hf0 hp0 hlim

theorem hiemenz_bounded_window_p7_2 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_window 7 2 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.Limit.hiemenz_limit_window f p q hf hp hq hf0 hp0 hlim

theorem hiemenz_bounded_equal_p7_1 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal 7 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.Limit.hiemenz_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem hiemenz_bounded_equal_p14_1 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal 14 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.Limit.hiemenz_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem hiemenz_bounded_equal_p7_2 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal 7 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.Limit.hiemenz_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem hiemenz_bounded_equal_p14_2 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal 14 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.Limit.hiemenz_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem hiemenz_bounded_window_r6 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_window 6 := by
  intro f p q hf hp hq hf0 hp0 hb
  exact Checked.FalknerSkan.Bounded.hiemenz_bounded_window f p q hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded one_pos hf hp (fun η hη => (hq η hη).congr_deriv (by ring)) hf0 hp0 hb) hb

theorem hiemenz_bounded_equal_r6 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal 6 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂
  exact Checked.FalknerSkan.Bounded.hiemenz_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded one_pos hf hp (fun η hη => (hq η hη).congr_deriv (by ring)) hf0 hp0 hb) hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

theorem hiemenz_bounded_equal_r13 : dropped% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal 13 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂
  exact Checked.FalknerSkan.Bounded.hiemenz_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded one_pos hf₂ hp₂ (fun η hη => (hq₂ η hη).congr_deriv (by ring)) hf₂0 hp₂0 hb₂) hb₂

theorem homann_bounded_window_p7_1 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_window 7 1 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.Limit.homann_limit_window f p q hf hp hq hf0 hp0 hlim

theorem homann_bounded_window_p7_2 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_window 7 2 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.Limit.homann_limit_window f p q hf hp hq hf0 hp0 hlim

theorem homann_bounded_equal_p7_1 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_equal 7 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.Limit.homann_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem homann_bounded_equal_p14_1 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_equal 14 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.Limit.homann_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem homann_bounded_equal_p7_2 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_equal 7 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.Limit.homann_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem homann_bounded_equal_p14_2 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_equal 14 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.Limit.homann_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem homann_bounded_window_r6 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_window 6 := by
  intro f p q hf hp hq hf0 hp0 hb
  exact Checked.FalknerSkan.Bounded.homann_bounded_window f p q hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded two_pos hf hp hq hf0 hp0 hb) hb

theorem homann_bounded_equal_r6 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_equal 6 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂
  exact Checked.FalknerSkan.Bounded.homann_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded two_pos hf hp hq hf0 hp0 hb) hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

theorem homann_bounded_equal_r13 : dropped% Checked.FalknerSkan.Bounded.homann_bounded_equal 13 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂
  exact Checked.FalknerSkan.Bounded.homann_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded two_pos hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂) hb₂

theorem fs_half_bounded_window_p7_1 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_window 7 1 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.Limit.fs_half_limit_window f p q hf hp hq hf0 hp0 hlim

theorem fs_half_bounded_window_p7_2 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_window 7 2 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.Limit.fs_half_limit_window f p q hf hp hq hf0 hp0 hlim

theorem fs_half_bounded_equal_p7_1 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal 7 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.Limit.fs_half_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_half_bounded_equal_p14_1 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal 14 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.Limit.fs_half_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_half_bounded_equal_p7_2 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal 7 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.Limit.fs_half_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_half_bounded_equal_p14_2 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal 14 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.Limit.fs_half_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_half_bounded_window_r6 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_window 6 := by
  intro f p q hf hp hq hf0 hp0 hb
  exact Checked.FalknerSkan.HalfBounded.fs_half_bounded_window f p q hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb) hb

theorem fs_half_bounded_equal_r6 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal 6 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂
  exact Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb) hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

theorem fs_half_bounded_equal_r13 : dropped% Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal 13 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂
  exact Checked.FalknerSkan.HalfBounded.fs_half_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂) hb₂

theorem fs_fifth_bounded_window_p7_1 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_window 7 1 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.Limit.fs_fifth_limit_window f p q hf hp hq hf0 hp0 hlim

theorem fs_fifth_bounded_window_p7_2 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_window 7 2 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.Limit.fs_fifth_limit_window f p q hf hp hq hf0 hp0 hlim

theorem fs_fifth_bounded_equal_p7_1 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal 7 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.Limit.fs_fifth_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_fifth_bounded_equal_p14_1 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal 14 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.Limit.fs_fifth_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_fifth_bounded_equal_p7_2 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal 7 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.Limit.fs_fifth_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_fifth_bounded_equal_p14_2 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal 14 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.Limit.fs_fifth_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_fifth_bounded_window_r6 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_window 6 := by
  intro f p q hf hp hq hf0 hp0 hb
  exact Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_window f p q hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb) hb

theorem fs_fifth_bounded_equal_r6 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal 6 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂
  exact Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb) hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

theorem fs_fifth_bounded_equal_r13 : dropped% Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal 13 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂
  exact Checked.FalknerSkan.FifthBounded.fs_fifth_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂) hb₂

theorem fs_tenth_bounded_window_p7_1 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_window 7 1 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.LimitTenth.fs_tenth_limit_window f p q hf hp hq hf0 hp0 hlim

theorem fs_tenth_bounded_window_p7_2 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_window 7 2 := by
  intro f p q hf hp hq hf0 hp0 hlim _
  exact Checked.FalknerSkan.LimitTenth.fs_tenth_limit_window f p q hf hp hq hf0 hp0 hlim

theorem fs_tenth_bounded_equal_p7_1 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal 7 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.LimitTenth.fs_tenth_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_tenth_bounded_equal_p14_1 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal 14 1 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.LimitTenth.fs_tenth_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_tenth_bounded_equal_p7_2 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal 7 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ _ η hη _
  exact Checked.FalknerSkan.LimitTenth.fs_tenth_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_tenth_bounded_equal_p14_2 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal 14 2 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim _ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη _
  exact Checked.FalknerSkan.LimitTenth.fs_tenth_limit_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ η hη

theorem fs_tenth_bounded_window_r6 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_window 6 := by
  intro f p q hf hp hq hf0 hp0 hb
  exact Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_window f p q hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb) hb

theorem fs_tenth_bounded_equal_r6 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal 6 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂
  exact Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf hp hq hf0 hp0 hb) hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hb₂

theorem fs_tenth_bounded_equal_r13 : dropped% Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal 13 := by
  intro f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂
  exact Checked.FalknerSkan.TenthBounded.fs_tenth_bounded_equal f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hb hf₂ hp₂ hq₂ hf₂0 hp₂0
    (Checked.FalknerSkan.BoundedLimit.tendsto_of_bounded_beta (by norm_num) hf₂ hp₂ hq₂ hf₂0 hp₂0 hb₂) hb₂

end Checked.Trust.NecessityG
