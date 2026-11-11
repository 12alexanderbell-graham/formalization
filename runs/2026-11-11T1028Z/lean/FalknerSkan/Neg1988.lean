import Mathlib
import Work.FSAtt.N1988Core
import Work.FSAtt.N1988Lo
import Work.FSAtt.N1988Hi

/-!
# Falkner–Skan at β = −0.1988: the attached wall shear (FROZEN, run 2026-11-11T0828Z; proofs pending)

Parts 2/5. Classical tables and recent papers print f''(0) at β = −0.1988 (just above the separation value
β* ∈ (−0.1988377351, −0.1988377350), `Checked.FalknerSkan.Separation`) as 0.005221 (Fazio 2012, typeset
p. 16, `runs/2026-11-11T0828Z/typeset/fazio2012_p16_beta_min.png`), 0.005222, 0.005225, 0.005226, 0.005229
(Zhang, Asaithambi, Salama, Zhu; run 2026-11-11T0232Z referee, not yet read typeset). Independent
numerics (run 0232Z referee, mpmath; run 0828Z scipy DOP853, horizons 10–14): 0.00521818788… So every
printed value is wrong in the fourth significant digit. The window below certifies it.

Statements copied from `Checked.FalknerSkan.NegWindow.fs_neg_tenth_window` and
`Checked.FalknerSkan.NegTenth.fs_neg_tenth_exists_decay` with β = −1988/10000 and the window
(0.0052181, 0.0052182). Do not change them; prove them (route: the β = −1/10 stack `Checked/FSNeg/`
templated to K = 10000/1988, or the K-parameterised cells of `Checked/FSSep/` started at q(0) = α).
-/

namespace Work.FalknerSkan.Neg1988

open Set Filter Topology

/-- Falkner–Skan with β = −1988/10000: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then 0.0052181 < q(0) < 0.0052182. -/
theorem fs_neg1988_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.0052181 < q 0 ∧ q 0 < 0.0052182 :=
  Work.FSAtt.N1988Core.window_core Work.FSAtt.N1988Lo.chain Work.FSAtt.N1988Hi.chain
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −1988/10000: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_neg1988_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :=
  Work.FSAtt.N1988Core.exists_core Work.FSAtt.N1988Lo.chain Work.FSAtt.N1988Hi.chain

end Work.FalknerSkan.Neg1988

