theorem β_eq : β = -1988 / 10000 := by unfold β; norm_num

/-- C³ on [0, ∞) from a chain of one-sided derivatives with a continuous last derivative
(run 1028Z's `Neg1988Blind.cdo_of`). -/
theorem cdo_of {f p q r : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (r η) (Ici 0) η)
    (hr : ContinuousOn r (Ici 0)) : ContDiffOn ℝ 3 f (Ici 0) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have e : ∀ {g g' : ℝ → ℝ}, (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (g' η) (Ici 0) η) →
      ∀ η ∈ Ici (0 : ℝ), derivWithin g (Ici 0) η = g' η :=
    fun h η hη => (h η hη).derivWithin (hu η hη)
  have Q : ContDiffOn ℝ 1 q (Ici 0) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
    refine ⟨fun η hη => (hq η hη).differentiableWithinAt, by simp, ?_⟩
    exact (contDiffOn_zero.2 hr).congr (e hq)
  have P : ContDiffOn ℝ 2 p (Ici 0) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
    exact ⟨fun η hη => (hp η hη).differentiableWithinAt, by simp, Q.congr (e hp)⟩
  rw [show (3 : WithTop ℕ∞) = 2 + 1 from rfl, contDiffOn_succ_iff_derivWithin hu]
  exact ⟨fun η hη => (hf η hη).differentiableWithinAt, by simp, P.congr (e hf)⟩

/-- A solution in the program's form is a blind solution, with d1 f = p and d2 f = q on [0, ∞). -/
theorem transfer {f p q : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (nhds 1)) :
    FSSol f ∧ (∀ η ∈ Ici (0 : ℝ), d1 f η = p η) ∧ (∀ η ∈ Ici (0 : ℝ), d2 f η = q η) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have E1 : ∀ η ∈ Ici (0 : ℝ), d1 f η = p η := fun η hη => (hf η hη).derivWithin (hu η hη)
  have hp' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (d1 f) (q η) (Ici 0) η :=
    fun η hη => (hp η hη).congr (fun x hx => E1 x hx) (E1 η hη)
  have E2 : ∀ η ∈ Ici (0 : ℝ), d2 f η = q η := fun η hη => (hp' η hη).derivWithin (hu η hη)
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (d2 f)
      (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η :=
    fun η hη => (hq η hη).congr (fun x hx => E2 x hx) (E2 η hη)
  have E3 : ∀ η ∈ Ici (0 : ℝ), d3 f η = -(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2) :=
    fun η hη => (hq' η hη).derivWithin (hu η hη)
  have cf : ContinuousOn f (Ici 0) := fun η hη => (hf η hη).continuousWithinAt
  have cp : ContinuousOn p (Ici 0) := fun η hη => (hp η hη).continuousWithinAt
  have cq : ContinuousOn q (Ici 0) := fun η hη => (hq η hη).continuousWithinAt
  have hr : ContinuousOn (fun η => -(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) :=
    ((cf.mul cq).neg).sub (continuousOn_const.mul (continuousOn_const.sub (cp.pow 2)))
  have ev : ∀ {u v : ℝ → ℝ}, (∀ η ∈ Ici (0 : ℝ), u η = v η) → u =ᶠ[atTop] v :=
    fun h => (eventually_ge_atTop 0).mono (fun η hη => h η hη)
  refine ⟨⟨⟨cdo_of hf hp hq hr, fun η hη => ?_⟩, ⟨hf0, by rw [E1 0 (mem_Ici.2 le_rfl), hp0]⟩,
    hlim.congr' (ev E1).symm⟩, E1, E2⟩
  rw [E1 η hη, E2 η hη, E3 η hη, β_eq]; ring

theorem superExp_of {f p q : ℝ → ℝ} (E1 : ∀ η ∈ Ici (0 : ℝ), d1 f η = p η)
    (E2 : ∀ η ∈ Ici (0 : ℝ), d2 f η = q η) (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    SuperExp f := fun M => by
  filter_upwards [hdec M, eventually_ge_atTop 0] with η h1 h2
  rw [E1 η h2, E2 η h2]; exact h1
