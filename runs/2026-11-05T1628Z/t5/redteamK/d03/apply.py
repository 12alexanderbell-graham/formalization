#!/usr/bin/env python3
import sys, pathlib

root = pathlib.Path(sys.argv[1])


def write_new(rel, text):
    p = root / rel
    assert not p.exists(), rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


def append(rel, text):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")


def register(module, headlines, kinds=(), group=None):
    s = (root / "Checked.lean").read_text(encoding="utf-8")
    assert ("import " + module + "\n") not in s
    append("Checked.lean", "import " + module + "\n")
    h = ("\n# " + group + "\n" if group else "") + "".join(x + "\n" for x in headlines)
    append("scripts/trust/headlines.txt", h)
    if kinds:
        append("scripts/trust/def_kinds.txt", "".join(k + "\n" for k in kinds))

LEAN = r'''import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.LCDMWitness
import Checked.Trust.NonVacuity

/-!
# Present-day sign of the deceleration parameter in flat ΛCDM

The deceleration parameter `q₀` is read off the second cosmographic coefficient; for flat ΛCDM it
follows from `flatLCDM_coeffs`.
-/

namespace Checked.Cosmography.QNought

open Checked.Cosmography.Aviles

/-- Deceleration parameter `q₀` at time `t`: the second cosmographic coefficient
`a⁽²⁾ / (a H²)` of Aviles et al. Eq. (3). -/
noncomputable def qNought (a : ℝ → ℝ) (t : ℝ) : ℝ := cosmoCoeff 2 a t

lemma decel_eq_neg_coeff_two (a : ℝ → ℝ) (t : ℝ) : decel a t = -cosmoCoeff 2 a t := by
  have h2 : iteratedDeriv 2 a t = deriv (deriv a) t := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  unfold decel cosmoCoeff hubble
  rw [h2]
  by_cases h0 : a t = 0
  · simp [h0]
  · by_cases h1 : deriv a t = 0
    · simp [h1]
    · have h0' : a t ≠ 0 := h0
      have h1' : deriv a t ≠ 0 := h1
      field_simp
      try ring

/-- In flat ΛCDM with matter fraction Ω below 2/3 the deceleration parameter q₀ is positive: the
expansion decelerates at the present time. -/
theorem qNought_pos_of_lt (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) (hL : IsFlatLCDM Ω a t₀)
    (hs : ContDiffAt ℝ 6 a t₀) (hΩ : Ω < 2 / 3) : 0 < qNought a t₀ := by
  have h := (flatLCDM_coeffs Ω a t₀ hL hs).1
  have e := decel_eq_neg_coeff_two a t₀
  unfold qNought
  linarith

theorem nv_qNought_pos_of_lt : nonvacuity% Checked.Cosmography.QNought.qNought_pos_of_lt := by
  obtain ⟨a, t₀, hL, hs⟩ :=
    Checked.Cosmography.AvilesWitness.exists_flatLCDM (Ω := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨1 / 2, a, t₀, hL, hs, by norm_num, trivial⟩

end Checked.Cosmography.QNought
'''

write_new('Checked/Cosmography/QNought.lean', LEAN)
register('Checked.Cosmography.QNought', ['Checked.Cosmography.QNought.qNought_pos_of_lt'], ('Checked.Cosmography.QNought.qNought COMPOSITE',), 'Present-day sign of the deceleration parameter')
