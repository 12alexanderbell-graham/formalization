/-! Copied readings against the parametric closure rule (run 2026-11-26T1428Z, part 3). Question (section Next of
`runs/2026-11-26T0828Z/README.md`): can an author-written reading close an objection through the rule the claims page
runs (`Claims.paramClosureFaults`)? The simplest author-written reading is not a re-spelling but a copy: the headline's
own statement, written as the reading. An honest blind reading that agrees with a faithful headline may be the same
term, so the rule must accept a reading equal to the headline (`y == x` is exempt from the containment test).

C1: the copy of `gelfand_pde_bound` (a faithful headline) as the reading.
C2: a planted unfaithful headline `weak_bound` (the source's 3.321992119 mis-transcribed as 3.5; still true, proved
    from the program's theorem) with the copy of ITS statement as the reading: the objection "the source says
    3.321992119" would be closed. The honest blind reading (`λ ≤ 3.321992119`) cannot close C2's objection: the family
    equivalence `∀ c, (… → λ ≤ 3.321992119) ↔ (… → λ ≤ c)` is false at c = 3.4, so no closure theorem exists.
Run with `runs/2026-11-26T0828Z/scripts/run_pclosure.sh scripts/trust/Claims.lean runs/2026-11-26T1428Z/t5/copy_body.lean`. -/

open Set Filter Topology Metric InnerProductSpace Laplacian

namespace CBench

/-- The planted unfaithful "headline": the bound transcribed as 3.5 instead of the source's 3.321992119. -/
theorem weak_bound (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 3.5 := by
  have := Checked.Math.GelfandPDEBound.gelfand_pde_bound lam u hu hc hb hpde
  linarith

namespace SecondReading
/-- C1: the headline's statement copied as the "reading". -/
def gelfandCopy : Prop :=
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ 3.321992119

/-- C2: the unfaithful headline's statement copied as the "reading". -/
def weakCopy : Prop :=
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ 3.5
end SecondReading

/-- The family `H[c]` of both headlines (one literal each). -/
abbrev HC (c : ℝ) : Prop :=
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c

theorem bite_common : ¬ ∀ c : ℝ, ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro h
  have := h (-1) 0 (fun _ => 0) contDiffOn_const continuousOn_const (fun _ _ => rfl)
    (fun x _ => by simp)
  linarith

/-! ## C1: copy of a faithful headline -/
theorem c_copy : ∀ c : ℝ, (∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c) ↔ ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := fun _ => Iff.rfl

theorem c_copy.bite : ¬ ∀ c : ℝ, ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := bite_common

/-! ## C2: copy of an unfaithful headline (same closure term; the headline differs) -/
theorem c_weak : ∀ c : ℝ, (∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c) ↔ ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := fun _ => Iff.rfl

theorem c_weak.bite : ¬ ∀ c : ℝ, ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (_ : ContDiffOn ℝ 2 u (ball 0 1))
    (_ : ContinuousOn u (closedBall 0 1))
    (_ : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (_ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := bite_common

end CBench

open Claims in
run_cmd do
  let env ← getEnv
  let isRd := fun (c : Name) => (`CBench.SecondReading).isPrefixOf c
  for (head, t, rn) in [(`Checked.Math.GelfandPDEBound.gelfand_pde_bound, `CBench.c_copy, `CBench.SecondReading.gelfandCopy),
      (`CBench.weak_bound, `CBench.c_weak, `CBench.SecondReading.weakCopy),
      -- control: the copied reading of the faithful headline offered against the unfaithful one (must be rejected)
      (`CBench.weak_bound, `CBench.c_copy, `CBench.SecondReading.gelfandCopy)] do
    let faults ← liftTermElabM <| paramClosureFaults env isRd head t rn
    if faults.isEmpty then logInfo m!"COPY {head} by {t} reading {rn}: ACCEPTED"
    else logInfo m!"COPY {head} by {t} reading {rn}: REJECTED ({faults.size}): {faults.toList}"
