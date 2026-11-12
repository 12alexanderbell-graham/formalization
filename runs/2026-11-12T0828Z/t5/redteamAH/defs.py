# ---------------- D01 ----------------
lean1 = r'''import Checked.Trust.NonVacuity
import Checked.Trust.NecessityB
import Checked.Trust.NecessityD
import Checked.Cosmography.Lookback

/-! The second-order lookback expansion together with the vanishing redshift of a source emitting at the
observation time. Module `NecessityM1`. -/

open Filter Topology Asymptotics Checked.Cosmography

namespace Checked.Cosmography.LookbackZero

/-- The second-order lookback expansion of `lookback_second_order` and, in addition, the redshift of a
source emitting at the observation time `t₀` is zero. -/
theorem lookback_second_order_zero (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :
    ((fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2)) ∧ redshift a t₀ t₀ = 0 :=
  ⟨Checked.Cosmography.lookback_second_order a t₀ ha ha' ha0 hH, by
    unfold redshift; rw [div_self ha0, sub_self]⟩

end Checked.Cosmography.LookbackZero

namespace Checked.Trust.NCM1
open Checked.Cosmography.LookbackZero

theorem nv : nonvacuity% Checked.Cosmography.LookbackZero.lookback_second_order_zero :=
  ⟨Real.exp, 0, Filter.Eventually.of_forall fun _ => Real.differentiableAt_exp,
    by rw [Real.deriv_exp]; exact Real.differentiableAt_exp, (Real.exp_pos 0).ne',
    by simp [Real.deriv_exp], trivial⟩

theorem lookback_second_order_zero_r1 :
    dropped% Checked.Cosmography.LookbackZero.lookback_second_order_zero 1 := by
  intro a t₀ ha' ha0 hH
  refine ⟨Checked.Trust.NCD.lookback_second_order_r1 a t₀ ha' ha0 hH, ?_⟩
  unfold Checked.Cosmography.redshift
  rw [div_self ha0, sub_self]

theorem lookback_second_order_zero_h2 :
    necessity% Checked.Cosmography.LookbackZero.lookback_second_order_zero 2 := by
  obtain ⟨a, t₀, p1, p3, p4, hn⟩ := Checked.Trust.NCD.lookback_second_order_h2
  exact ⟨a, t₀, p1, p3, p4, fun h => hn h.1⟩

/-- `a t₀ ≠ 0` is needed: with `a = id` and `t₀ = 0` the redshift at the observation time is `-1`. -/
theorem lookback_second_order_zero_h3 :
    necessity% Checked.Cosmography.LookbackZero.lookback_second_order_zero 3 := by
  have hd : deriv (fun t : ℝ => t) = fun _ => (1 : ℝ) := funext fun x => (hasDerivAt_id x).deriv
  refine ⟨fun t => t, 0, Filter.Eventually.of_forall fun t => (hasDerivAt_id t).differentiableAt,
    ?_, ?_, ?_⟩
  · rw [hd]; exact differentiableAt_const _
  · rw [hd]; norm_num
  · intro h
    have h2 := h.2
    rw [Checked.Trust.NCB.redshift_of_a0 (fun t : ℝ => t) 0 rfl 0] at h2
    norm_num at h2

theorem lookback_second_order_zero_h4 :
    necessity% Checked.Cosmography.LookbackZero.lookback_second_order_zero 4 := by
  obtain ⟨a, t₀, p1, p2, p3, hn⟩ := Checked.Trust.NCB.lookback_second_order_h4
  exact ⟨a, t₀, p1, p2, p3, fun h => hn h.1⟩

end Checked.Trust.NCM1
'''
claim1 = '''Category: wrong-statement (obligation trivially met for a reason unrelated to the physics: shape-detector bypass by a consequence conjunct)
Reader would wrongly believe: that `a t0 != 0` is NEEDED for the second-order lookback expansion. Generated line (TRUST_MAP.md, "Hypothesis necessity, per headline"), expected after regeneration:
`- LookbackZero.lookback_second_order_zero (4): needed 2 (...), 3 (lookback_second_order_zero_h3), 4 (...); redundant 1 (...)` and, in the totals, one more headline "with every hypothesis classified" (55/155).
Meanwhile the SAME map line for the original headline says `lookback_second_order (4): needed 2, 4; redundant (each alone, not together) 1, 3`: hypothesis 3 is redundant for the expansion.
Why it is false: hypothesis 3 (`a t0 != 0`) carries no weight for the lookback expansion (main's `lookback_second_order_r3`: if `a t0 = 0` the Hubble rate is the junk value 0 and the remainder is `t0 - t = o(1)`). In the wrapper it is "needed" only because of the added conjunct `redshift a t0 t0 = 0`, which holds iff `a t0 != 0` (`0/0 - 1 = -1` in Lean): the witness `a = id, t0 = 0` falsifies only that trivial conjunct. The `restated i` shape detector compares hypotheses with conjuncts of the conclusion up to defeq, so a conjunct that is merely equivalent to the hypothesis (not defeq) passes. Not a real defect of the Lean statement, but the map says NEEDED where on paper/Lean the expansion does not need it.
Order: one commit (new module NecessityM1, Checked.lean import, headlines.txt line); relock + regenerate TRUST_MAP/CLAIMS. No LEDGER line needed (nothing open).
Expected: ACCEPTED (possible catches: check_prose / claim_words on the new docstring; none by N1-N4).
'''
emit(1, "NecessityM1", "Checked.Cosmography.LookbackZero.lookback_second_order_zero", lean1, claim1)

# ---------------- D02 ----------------
lean2 = r'''import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.Trust.Witnesses
import Checked.Chemistry.CubicEOS

/-! A restatement of the critical-point theorem for the generalized cubic equation of state. Module `NecessityM2`. -/

namespace Checked.Chemistry.CubicEOSAgain
open Checked.Chemistry.CubicEOS

/-- Existence and uniqueness of the critical point of the generalized cubic equation of state, as in
`exists_unique_critical`. -/
theorem exists_unique_critical_again (R a b u w : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (hu : -2 < u) (h1 : 0 < 1 + u + w) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ b < p.2 ∧ IsCriticalIsotherm (cubicP R a b u w p.1) p.2 :=
  Checked.Chemistry.CubicEOS.exists_unique_critical R a b u w hR ha hb hu h1

end Checked.Chemistry.CubicEOSAgain

namespace Checked.Trust.NCM2

theorem nv : nonvacuity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again :=
  Checked.Trust.NV.exists_unique_critical

theorem exists_unique_critical_again_h1 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 1 :=
  Checked.Trust.NCD.exists_unique_critical_h1

theorem exists_unique_critical_again_h2 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 2 :=
  Checked.Trust.NCD.exists_unique_critical_h2

theorem exists_unique_critical_again_h3 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 3 :=
  Checked.Trust.NCD.exists_unique_critical_h3

theorem exists_unique_critical_again_h4 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 4 :=
  Checked.Trust.NCD.exists_unique_critical_h4

theorem exists_unique_critical_again_h5 :
    necessity% Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again 5 :=
  Checked.Trust.NCD.exists_unique_critical_h5

end Checked.Trust.NCM2
'''
claim2 = '''Category: unregistered-or-misregistered (tally counts the same hypotheses twice)
Reader would wrongly believe: that the necessity tally covers more distinct hypotheses/headlines than it does. After regeneration TRUST_MAP.md prints
`Hypothesis necessity ...: 889 hypotheses in 155 headlines; 419 shown NEEDED ...; headlines with every hypothesis classified: 55/155` (was 884/154, 414, 54/154) and the new line
`- CubicEOSAgain... : Chemistry.CubicEOSAgain.exists_unique_critical_again (5): needed 1 (exists_unique_critical_again_h1), 2 (...), 3, 4, 5`.
Why it is false: the new headline is a one-line wrapper of `exists_unique_critical` with syntactically identical binders and conclusion, so every witness of the original is accepted for the copy (StatementDeps matches by Expr equality of the obligation; the witnesses are the originals, `exact`). Five NEEDED hypotheses and one fully classified headline are counted twice; nothing new about any assumption was shown. Same trick works with any headline, so the 'fully classified' ratio can be inflated at will (each copy adds one to numerator and denominator).
Order: one commit (module NecessityM2, Checked.lean import, headlines.txt line). No LEDGER line needed (nothing open).
Expected: ACCEPTED by N1-N4 (new headline fully classified needs no disclosure); a duplicate-statement check would be the only catch.
'''
emit(2, "NecessityM2", "Checked.Chemistry.CubicEOSAgain.exists_unique_critical_again", lean2, claim2)

# ---------------- D03 ----------------
lean3 = r'''import Checked.Trust.NonVacuity
import Checked.Trust.NecessityB
import Checked.Trust.NecessityD
import Checked.Cosmography.Lookback

/-! The second-order lookback expansion with the Hubble numerator given as a unit. Module `NecessityM3`. -/

open Filter Topology Asymptotics Checked.Cosmography

namespace Checked.Cosmography.LookbackUnit

/-- The second-order lookback expansion of `lookback_second_order`, with the present velocity of the scale
factor given as a unit `H` of the real numbers. -/
theorem lookback_second_order_unit (a : ℝ → ℝ) (t₀ : ℝ) (H : Units ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : ((H : Units ℝ) : ℝ) = deriv a t₀) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) :=
  Checked.Cosmography.lookback_second_order a t₀ ha ha' ha0
    (fun h0 => H.ne_zero (hH.trans h0))

end Checked.Cosmography.LookbackUnit

namespace Checked.Trust.NCM3

theorem nv : nonvacuity% Checked.Cosmography.LookbackUnit.lookback_second_order_unit :=
  ⟨Real.exp, 0, 1, Filter.Eventually.of_forall fun _ => Real.differentiableAt_exp,
    by rw [Real.deriv_exp]; exact Real.differentiableAt_exp, (Real.exp_pos 0).ne',
    by simp [Real.deriv_exp], trivial⟩

theorem lookback_second_order_unit_r1 :
    dropped% Checked.Cosmography.LookbackUnit.lookback_second_order_unit 1 := by
  intro a t₀ H ha' ha0 hH
  exact Checked.Trust.NCD.lookback_second_order_r1 a t₀ ha' ha0 (fun h0 => H.ne_zero (hH.trans h0))

theorem lookback_second_order_unit_h2 :
    necessity% Checked.Cosmography.LookbackUnit.lookback_second_order_unit 2 := by
  obtain ⟨a, t₀, p1, p3, p4, hn⟩ := Checked.Trust.NCD.lookback_second_order_h2
  exact ⟨a, t₀, Units.mk0 (deriv a t₀) p4, p1, p3, rfl, hn⟩

theorem lookback_second_order_unit_r3 :
    dropped% Checked.Cosmography.LookbackUnit.lookback_second_order_unit 3 := by
  intro a t₀ H ha ha' hH
  exact Checked.Trust.NCB.lookback_second_order_r3 a t₀ ha ha' (fun h0 => H.ne_zero (hH.trans h0))

theorem lookback_second_order_unit_h4 :
    necessity% Checked.Cosmography.LookbackUnit.lookback_second_order_unit 4 := by
  obtain ⟨a, t₀, p1, p2, p3, hn⟩ := Checked.Trust.NCB.lookback_second_order_h4
  exact ⟨a, t₀, 1, p1, p2, p3, hn⟩

end Checked.Trust.NCM3
'''
claim3 = '''Category: weakened-statement (assumption hidden in a binder type that neither the numbering nor the shape detector reaches)
Reader would wrongly believe: that the headline assumes only the four numbered conditions and that every assumption is classified. Expected generated lines:
TRUST_MAP.md `- LookbackUnit.lookback_second_order_unit (4): needed 2 (...), 4 (...); redundant (each alone, not together) 1 (...), 3 (...)` with no `shape:` entry, counted as fully classified (55/155);
CLAIMS.md "For every `a : R -> R`, `t0 : R`, `H : Rˣ`" and "assuming 1..4" where 4 reads `(H : R) = deriv a t0`.
Why it is false: the binder `H : Units R` silently assumes `H != 0`, hence (through hypothesis 4) `deriv a t0 != 0`, which the expansion genuinely needs (the map's own NEEDED witness for `lookback_second_order` hyp 4, flatStart). The statement is thereby the original with its fourth hypothesis hidden: hypothesis 4 is listed as an innocuous definition of H and 'needed', and the real assumption `deriv a t0 != 0` is never numbered. necShape flags `Subtype`/`Set.Elem` and types that whnf (default) to them, but `Units` is a structure carrying proofs (`val_inv`, `inv_val`), as are `Fin n`, `C(X,Y)`, `E →L[R] F`, `Equiv`; none is flagged.
Order: one commit (module NecessityM3, Checked.lean import, headlines.txt). No LEDGER line needed.
Expected: ACCEPTED by N1-N4/shape; possibly caught by prose/claims rules on the docstring.
'''
emit(3, "NecessityM3", "Checked.Cosmography.LookbackUnit.lookback_second_order_unit", lean3, claim3)

# ---------------- D04 ----------------
lean4 = r'''import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.Chemistry.CubicEOS

/-! The critical cubic has a single root above one, with the sign condition handed in as a lifted proof. Module `NecessityM4`. -/

namespace Checked.Chemistry.CubicEOSLift
open Checked.Chemistry.CubicEOS

/-- The critical cubic of `critCubic_existsUnique` has exactly one root above `1`; the positivity of
`1 + u + w` is handed in as a lifted proof `h1`. -/
theorem critCubic_existsUnique_lift (u w : ℝ) (hu : -2 < u) (h1 : PLift (0 < 1 + u + w)) :
    ∃! x : ℝ, 1 < x ∧ critCubic u w x = 0 :=
  Checked.Chemistry.CubicEOS.critCubic_existsUnique u w hu h1.down

end Checked.Chemistry.CubicEOSLift

namespace Checked.Trust.NCM4

theorem nv : nonvacuity% Checked.Chemistry.CubicEOSLift.critCubic_existsUnique_lift :=
  ⟨0, 0, by norm_num, ⟨by norm_num⟩, trivial⟩

theorem critCubic_existsUnique_lift_h1 :
    necessity% Checked.Chemistry.CubicEOSLift.critCubic_existsUnique_lift 1 := by
  obtain ⟨u, w, p, hn⟩ := Checked.Trust.NCD.critCubic_existsUnique_h1
  exact ⟨u, w, ⟨p⟩, hn⟩

end Checked.Trust.NCM4
'''
claim4 = '''Category: weakened-statement (assumption carried as data of type `PLift P`, never numbered)
Reader would wrongly believe: that the headline has exactly one assumption, `-2 < u`, and that it is fully classified. Expected generated line:
`- CubicEOSLift.critCubic_existsUnique_lift (1): needed 1 (critCubic_existsUnique_lift_h1)` (no shape entry; 55/155 fully classified), CLAIMS.md "For every `u`, `w`, `h1 : PLift (0 < 1 + u + w)` assuming 1. `-2 < u`".
Why it is false: the theorem assumes `0 < 1 + u + w` as well; it is in the data list as a `PLift` (a Type, so `hypPositions` does not number it, `needsWitness`/non-vacuity treats it as plain data with a witness, and necShape's subtype test does not fire). A reader of the necessity line concludes `-2 < u` is the only assumption of the single-root theorem; without the hidden one the theorem is false (main's `critCubic_existsUnique_h2`, u = 0, w = -1). Any proposition can be moved out of the count this way (`PLift`, `ULift`, `Nonempty`-free wrappers, `PProd`).
Order: one commit. No LEDGER line.
Expected: ACCEPTED by N1-N4; the visible `PLift` in the CLAIMS data list is the only trace.
'''
emit(4, "NecessityM4", "Checked.Chemistry.CubicEOSLift.critCubic_existsUnique_lift", lean4, claim4)

# ---------------- D05 ----------------
lean5 = r'''import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.Chemistry.CubicEOS

/-! The critical cubic has a single root above one, for parameters in the admissible region. Module `NecessityM5`. -/

namespace Checked.Chemistry.CubicEOSRegion
open Checked.Chemistry.CubicEOS

/-- For parameters `(u, w)` in the admissible region the critical cubic has exactly one root above `1`. -/
theorem critCubic_existsUnique_region (p : ℝ × ℝ)
    (h : p ∈ {q : ℝ × ℝ | -2 < q.1 ∧ 0 < 1 + q.1 + q.2}) :
    ∃! x : ℝ, 1 < x ∧ critCubic p.1 p.2 x = 0 :=
  Checked.Chemistry.CubicEOS.critCubic_existsUnique p.1 p.2 h.1 h.2

end Checked.Chemistry.CubicEOSRegion

namespace Checked.Trust.NCM5

theorem nv : nonvacuity% Checked.Chemistry.CubicEOSRegion.critCubic_existsUnique_region :=
  ⟨(0, 1), by norm_num, trivial⟩

theorem critCubic_existsUnique_region_h1 :
    necessity% Checked.Chemistry.CubicEOSRegion.critCubic_existsUnique_region 1 := by
  obtain ⟨u, w, p, hn⟩ := Checked.Trust.NCD.critCubic_existsUnique_h2
  exact ⟨(u, w), hn⟩

end Checked.Trust.NCM5
'''
claim5 = '''Category: vacuous-or-trivial-statement (two assumptions counted as one hypothesis: membership atom escapes the bundled detector)
Reader would wrongly believe: that the single-root theorem has one assumption which is shown needed as a whole, with nothing bundled. Expected line:
`- CubicEOSRegion.critCubic_existsUnique_region (1): needed 1 (critCubic_existsUnique_region_h1)` (no `shape: bundled 1`, no `parts of 1`), fully classified (55/155).
Why it is false: hypothesis 1 `p in {q | -2 < q.1 /\\ 0 < 1 + q.1 + q.2}` is two independent conditions (-2 < u and 0 < 1+u+w); the witness shows only that dropping both together breaks the theorem (u = 0, w = -1 violates the second). partsWalk/unfoldHead stop at the membership atom (Set.Mem/setOf is not reducible), so numParts = 1 and `bundled` never fires; the same hole bundles any number of conditions via `Set.Icc`, `Metric.ball`, `{x | .. /\\ ..}`. A reader cannot tell from the map that one of the two conditions (-2 < u) is separately needed (main: critCubic_existsUnique_h1) and the headline lines of main list them as two needed hypotheses.
Order: one commit. No LEDGER line.
Expected: ACCEPTED if whnfR does not open the membership; if Lean unfolds it to a conjunction the `bundled 1` entry appears and N4 fails (CAUGHT) - uncertain.
'''
emit(5, "NecessityM5", "Checked.Chemistry.CubicEOSRegion.critCubic_existsUnique_region", lean5, claim5)

# ---------------- D06 ----------------
lean6 = r'''import Checked.Trust.NonVacuity
import Checked.Trust.NecessityD
import Checked.Chemistry.CubicEOS

/-! The critical cubic has a single root above one; the sign condition on `u` is stated with the region and again alone. Module `NecessityM6`. -/

namespace Checked.Chemistry.CubicEOSTwice
open Checked.Chemistry.CubicEOS

/-- The critical cubic of `critCubic_existsUnique` has exactly one root above `1` when `(u, w)` lies in the
region (`-2 < u` and `0 < 1 + u + w`) and `-2 < u`. -/
theorem critCubic_existsUnique_twice (u w : ℝ) (h : -2 < u ∧ 0 < 1 + u + w) (hu : -2 < u) :
    ∃! x : ℝ, 1 < x ∧ critCubic u w x = 0 :=
  Checked.Chemistry.CubicEOS.critCubic_existsUnique u w hu h.2

end Checked.Chemistry.CubicEOSTwice

namespace Checked.Trust.NCM6

theorem nv : nonvacuity% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice :=
  ⟨0, 0, ⟨by norm_num, by norm_num⟩, by norm_num, trivial⟩

theorem critCubic_existsUnique_twice_h1 :
    necessity% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice 1 :=
  Checked.Trust.NCD.critCubic_existsUnique_h2

theorem critCubic_existsUnique_twice_r2 :
    dropped% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice 2 :=
  fun u w h => Checked.Chemistry.CubicEOS.critCubic_existsUnique u w h.1 h.2

theorem critCubic_existsUnique_twice_p1_1 :
    dropped% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice 1 1 :=
  fun u w hu h => Checked.Chemistry.CubicEOS.critCubic_existsUnique u w hu h

theorem critCubic_existsUnique_twice_p1_2 :
    necessity% Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice 1 2 := by
  obtain ⟨u, w, p, hn⟩ := Checked.Trust.NCD.critCubic_existsUnique_h2
  exact ⟨u, w, p, p, hn⟩

end Checked.Trust.NCM6
'''
claim6 = '''Category: misleading-record (redundancy label does not cover a redundant hypothesis together with a redundant part of another hypothesis)
Reader would wrongly believe: that `-2 < u` can be dropped (it is listed twice as REDUNDANT, each time without the "each alone, not together" warning). Expected generated line:
`- CubicEOSTwice.critCubic_existsUnique_twice (2): needed 1 (critCubic_existsUnique_twice_h1); redundant 2 (critCubic_existsUnique_twice_r2); parts of 1 (2) needed 2 (critCubic_existsUnique_twice_p1_2); parts of 1 (2) redundant 1 (critCubic_existsUnique_twice_p1_1)` (fully classified, 55/155).
Why it is false: hypothesis 2 (`-2 < u`) is redundant given part 1 of hypothesis 1 (`-2 < u`), and that part is redundant given hypothesis 2; dropping both makes the theorem false (u = -32/7, w = 124/21: three roots above 1; main's critCubic_existsUnique_h1). The label "(each alone, not together)" is added only when a single list (hypotheses, or the parts of one hypothesis) has two or more redundant entries (`redund.size >= 2`, `cRed.size >= 2` in StatementDeps), so one redundant hypothesis plus one redundant part, which are jointly needed, carry no warning. The generic sentence in the section intro is the only caveat.
Order: one commit. No LEDGER line.
Expected: ACCEPTED (N1-N4 do not look at labels).
'''
emit(6, "NecessityM6", "Checked.Chemistry.CubicEOSTwice.critCubic_existsUnique_twice", lean6, claim6)
