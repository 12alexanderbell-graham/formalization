import Mathlib
import Work.FSAtt.RThirteenCore
import Work.FSAtt.RThirteenLo
import Work.FSAtt.RThirteenHi
import Work.FSAtt.RFourteenCore
import Work.FSAtt.RFourteenLo
import Work.FSAtt.RFourteenHi
import Work.FSAtt.RSixteenCore
import Work.FSAtt.RSixteenLo
import Work.FSAtt.RSixteenHi

/-!
# Falkner–Skan attached rows β = −0.13, −0.14, −0.16: wall-shear windows (FROZEN, run 2026-11-13T1640Z)

Parts 2/5. The statements of `Work/FalknerSkan/Neg1988.lean` (blind-restated and closed in run 2026-11-11T1028Z)
with β and the ten-decimal window replaced, emitted by `runs/2026-11-13T1640Z/scripts/make_rows.py` from
`runs/2026-11-13T1640Z/scripts/rows.json` (same route as `Work/FalknerSkan/AttachedRows.lean`, run 2026-11-12T1428Z).
The rows are printed to twelve significant digits in Ganapol, arXiv:1006.3888v1, Table 6 (typeset crop
`runs/2026-11-12T1428Z/referee/typeset/ganapol2010_p21_table6_rows.png`); with row −0.15 (Work/FalknerSkan/AttachedRows.lean)
and rows −0.17, −0.18, −0.19 (Checked) they complete the decelerating segment of that table.
Proofs: the attached-flow stack generic in K ≥ 5 (`Work/FSAtt/`), two certified chains per row.
-/

namespace Work.FalknerSkan.AttachedRowsTop

open Set Filter Topology

/-- Falkner–Skan with β = −13/100: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then 0.2614227559 < q(0) < 0.2614227560. -/
theorem fs_att_thirteen_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-13 / 100) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.2614227559 < q 0 ∧ q 0 < 0.2614227560 :=
  Work.FSAtt.RThirteenCore.window_core Work.FSAtt.RThirteenLo.chain Work.FSAtt.RThirteenHi.chain
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −13/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_att_thirteen_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-13 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :=
  Work.FSAtt.RThirteenCore.exists_core Work.FSAtt.RThirteenLo.chain Work.FSAtt.RThirteenHi.chain

/-- Falkner–Skan with β = −14/100: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then 0.2397359553 < q(0) < 0.2397359554. -/
theorem fs_att_fourteen_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-14 / 100) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.2397359553 < q 0 ∧ q 0 < 0.2397359554 :=
  Work.FSAtt.RFourteenCore.window_core Work.FSAtt.RFourteenLo.chain Work.FSAtt.RFourteenHi.chain
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −14/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_att_fourteen_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-14 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :=
  Work.FSAtt.RFourteenCore.exists_core Work.FSAtt.RFourteenLo.chain Work.FSAtt.RFourteenHi.chain

/-- Falkner–Skan with β = −16/100: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then 0.1907798552 < q(0) < 0.1907798553. -/
theorem fs_att_sixteen_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-16 / 100) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.1907798552 < q 0 ∧ q 0 < 0.1907798553 :=
  Work.FSAtt.RSixteenCore.window_core Work.FSAtt.RSixteenLo.chain Work.FSAtt.RSixteenHi.chain
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −16/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_att_sixteen_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-16 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :=
  Work.FSAtt.RSixteenCore.exists_core Work.FSAtt.RSixteenLo.chain Work.FSAtt.RSixteenHi.chain

end Work.FalknerSkan.AttachedRowsTop
