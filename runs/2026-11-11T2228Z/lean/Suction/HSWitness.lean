import Work.Suction.HSAssemble
import Checked.FalknerSkan.Limit
import Checked.FalknerSkan.Bounded
import Checked.FalknerSkan.MonotoneWindow
import Checked.Hiemenz.Hiemenz
import Checked.Trust.NonVacuity
/-! Scratch (run 2026-11-11T2228Z): the wall condition f(0) = 0 is needed in the Hiemenz
boundary-value headlines. Witness: the Hiemenz boundary-value problem with suction f(0) = 1/2
(`Work.Suction.HSAssemble.exists_bvpS`: 0 ≤ p < 1, q > 0, wall shear in (1.5, 1.6)). -/

namespace Work.Suction.HSWitness
open Set Filter Topology

theorem not_window {x : ℝ} (h : 1.5 < x) : ¬ (1.2325876568 < x ∧ x < 1.2325876569) := by
  rintro ⟨-, h2⟩; linarith

theorem bound_of {p q : ℝ → ℝ} (h : ∀ t, 0 ≤ t → 0 ≤ p t ∧ p t < 1 ∧ 0 < q t) :
    ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := fun η hη =>
  ⟨by linarith [(h η hη).1], (h η hη).2.1.le⟩

theorem hiemenz_limit_window_h4 :
    necessity% Checked.FalknerSkan.Limit.hiemenz_limit_window 4 := by
  obtain ⟨f, p, q, hf, hp, hq, -, hp0, hl, hlo, -, -⟩ := Work.Suction.HSAssemble.exists_bvpS
  exact ⟨f, p, q, hf, hp, hq, hp0, hl, not_window hlo⟩

theorem hiemenz_bounded_window_h4 :
    necessity% Checked.FalknerSkan.Bounded.hiemenz_bounded_window 4 := by
  obtain ⟨f, p, q, hf, hp, hq, -, hp0, hl, hlo, -, hc⟩ := Work.Suction.HSAssemble.exists_bvpS
  exact ⟨f, p, q, hf, hp, hq, hp0, hl, bound_of hc, not_window hlo⟩

theorem hiemenz_monotone_window_h4 :
    necessity% Checked.FalknerSkan.MonotoneWindow.hiemenz_monotone_window 4 := by
  obtain ⟨f, p, q, hf, hp, hq, -, hp0, hl, hlo, -, hc⟩ := Work.Suction.HSAssemble.exists_bvpS
  exact ⟨f, p, q, hf, hp, hq, hp0, hl, fun η hη => (hc η hη).2.2, not_window hlo⟩

theorem hiemenz_limit_equal_h4 :
    necessity% Checked.FalknerSkan.Limit.hiemenz_limit_equal 4 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hl, -, -, -⟩ := Work.Suction.HSAssemble.exists_bvpS
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hl₂, -, -⟩ := Checked.Hiemenz.hiemenz_exists
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, hq, hp0, hl, hf₂, hp₂, hq₂, hf₂0, hp₂0, hl₂, ?_⟩
  intro h
  have := (h 0 (mem_Ici.2 le_rfl)).1
  rw [hf0, hf₂0] at this; norm_num at this

theorem hiemenz_limit_equal_h10 :
    necessity% Checked.FalknerSkan.Limit.hiemenz_limit_equal 10 := by
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hl₂, -, -, -⟩ := Work.Suction.HSAssemble.exists_bvpS
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hl, -, -⟩ := Checked.Hiemenz.hiemenz_exists
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, hq, hf0, hp0, hl, hf₂, hp₂, hq₂, hp₂0, hl₂, ?_⟩
  intro h
  have := (h 0 (mem_Ici.2 le_rfl)).1
  rw [hf0, hf₂0] at this; norm_num at this

theorem hiemenz_bounded_equal_h4 :
    necessity% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal 4 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hl, -, -, hc⟩ := Work.Suction.HSAssemble.exists_bvpS
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hl₂, hb₂, -, -⟩ :=
    Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, hq, hp0, hl, bound_of hc, hf₂, hp₂, hq₂, hf₂0, hp₂0, hl₂,
    fun η hη => ⟨by linarith [(hb₂ η hη).1], (hb₂ η hη).2.le⟩, ?_⟩
  intro h
  have := (h 0 (mem_Ici.2 le_rfl)).1
  rw [hf0, hf₂0] at this; norm_num at this

theorem hiemenz_bounded_equal_h11 :
    necessity% Checked.FalknerSkan.Bounded.hiemenz_bounded_equal 11 := by
  obtain ⟨f₂, p₂, q₂, hf₂, hp₂, hq₂, hf₂0, hp₂0, hl₂, -, -, hc⟩ := Work.Suction.HSAssemble.exists_bvpS
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hl, hb, -, -⟩ :=
    Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, hq, hf0, hp0, hl,
    fun η hη => ⟨by linarith [(hb η hη).1], (hb η hη).2.le⟩, hf₂, hp₂, hq₂, hp₂0, hl₂,
    bound_of hc, ?_⟩
  intro h
  have := (h 0 (mem_Ici.2 le_rfl)).1
  rw [hf0, hf₂0] at this; norm_num at this

end Work.Suction.HSWitness
