import sys, os
root = sys.argv[1]
def w(rel, text):
    p = os.path.join(root, rel)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    assert not os.path.exists(p), rel
    open(p, "w").write(text)
def append(rel, text):
    p = os.path.join(root, rel)
    s = open(p).read()
    if not s.endswith("\n"): s += "\n"
    open(p, "w").write(s + text)

HEAD = r'''import Checked.Cosmography.LCDMCoefficients

/-! Positivity of the Hubble rate from a long pinned specification (a conjunction of 67 conditions at `t₀`). -/

namespace Checked.AGWrap.D04

open Checked.Cosmography

/-- If the specification `h` (reflexivity of the Hubble rate at `t₀` listed 66 times, and `0 < H(t₀)`) holds, the Hubble rate at `t₀` is positive. -/
theorem hubble_pos_pinned (a : ℝ → ℝ) (t₀ : ℝ)
    (h : (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (hubble a t₀ = hubble a t₀) ∧
    (0 < hubble a t₀ ∧ (hubble a t₀ = hubble a t₀) ∧ (hubble a t₀ = hubble a t₀))) :
    0 < hubble a t₀ :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end Checked.AGWrap.D04

#print axioms Checked.AGWrap.D04.hubble_pos_pinned
'''
WIT = r'''import Checked.Trust.NonVacuity
import Checked.AGWrap.D04

namespace Checked.Trust.AGW04

open Checked.Cosmography

theorem hubble_pos_pinned : nonvacuity% Checked.AGWrap.D04.hubble_pos_pinned :=
  ⟨fun t => t, 2, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by norm_num [hubble], rfl, rfl⟩, trivial⟩

theorem hubble_pos_pinned_h1 : necessity% Checked.AGWrap.D04.hubble_pos_pinned 1 :=
  ⟨fun _ => 0, 0, by simp [hubble]⟩

theorem hubble_pos_pinned_r1_1 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 1 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_2 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 2 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_3 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 3 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_4 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 4 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_5 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 5 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_6 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 6 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_7 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 7 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_8 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 8 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_9 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 9 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_10 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 10 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_11 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 11 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_12 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 12 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_13 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 13 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_14 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 14 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_15 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 15 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_16 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 16 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_17 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 17 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_18 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 18 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_19 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 19 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_20 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 20 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_21 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 21 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_22 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 22 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_23 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 23 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_24 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 24 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_25 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 25 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_26 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 26 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_27 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 27 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_28 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 28 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_29 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 29 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_30 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 30 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_31 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 31 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_32 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 32 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_33 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 33 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_34 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 34 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_35 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 35 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_36 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 36 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_37 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 37 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_38 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 38 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_39 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 39 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_40 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 40 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_41 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 41 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_42 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 42 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_43 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 43 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_44 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 44 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_45 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 45 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_46 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 46 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_47 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 47 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_48 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 48 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_49 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 49 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_50 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 50 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_51 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 51 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_52 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 52 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_53 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 53 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_54 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 54 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_55 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 55 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_56 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 56 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_57 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 57 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_58 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 58 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_59 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 59 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_60 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 60 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_61 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 61 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_62 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 62 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_63 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 63 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_r1_64 : dropped% Checked.AGWrap.D04.hubble_pos_pinned 1 64 := by
  intro a t₀ h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem hubble_pos_pinned_n1_65 : necessity% Checked.AGWrap.D04.hubble_pos_pinned 1 65 :=
  ⟨fun _ => 0, 0, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp [hubble]⟩

end Checked.Trust.AGW04
'''
w("Checked/AGWrap/D04.lean", HEAD)
w("Checked/Trust/AGW04.lean", WIT)
append("Checked.lean", "import Checked.AGWrap.D04\nimport Checked.Trust.AGW04\n")
append("scripts/trust/headlines.txt", "Checked.AGWrap.D04.hubble_pos_pinned\n")
