import Work.FSRev.R1988PrintedEnd
import Work.FSRev.RGlobal
import Checked.FalknerSkan.FSScale

/-! Falkner–Skan at β = −1988/10000: the initial-value problem with the printed reversed wall value
−0.005158 has a solution on [0, ∞) (non-vacuity of the printed-value overshoot statement). On [0, 4] in
scaled time the clamped flow stays strictly inside its clamps (the printed-value chain), its end state lies
in the energy well (last cell's range), and the dissipative tail field continues it with no clamp active
(`RGlobal.tail`); scaling back gives the unscaled solution. Run 2026-11-11T1828Z. -/

namespace Work.FSRev.RPrintedNV
open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Work.FSRev.RIdent Work.FSRev.RGlobal

/-- The glued scaled solution: the clamped flow on [0, 4], the tail flow after. -/
theorem scaled_exists : ∃ G : ℝ → ℝ × ℝ × ℝ,
    G 0 = (0, 0, -0.005158 / Real.sqrt (497 / 2500)) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt G (uS (2500 / 497) (G t)) (Ici 0) t := by
  set c := Real.sqrt (497 / 2500 : ℝ) with hcd
  have hc : 0 < c := Real.sqrt_pos.2 (by norm_num)
  have hclo : (44586993619215906 / 100000000000000000 : ℝ) < c := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hchi : c < (44586993619215907 / 100000000000000000 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  set α := (-0.005158 : ℝ) / c with hαd
  have hα : |α - (-11568396030579 / 1000000000000000)| ≤ 1 / 100000000000000 := by
    rw [hαd, abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ hc]; nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hc]; nlinarith
  set Y := Work.FSAtt.AFlow.flowA (2500 / 497) α with hYd
  have hY : ∀ t ∈ Icc (0 : ℝ) 4, HasDerivWithinAt Y (vS (2500 / 497) t (Y t)) (Icc 0 4) t :=
    fun t ht => (Work.FSAtt.AFlow.flowA_deriv _ _ t ht.1).mono Icc_subset_Ici_self
  have hY0 : Y 0 = (0, 0, α) := Work.FSAtt.AFlow.flowA_zero _ _
  obtain ⟨hbox, -⟩ := Work.FSRev.R1988Printed.chainP hY hY0 hα
  obtain ⟨e1, e2, e3, e4⟩ := Work.FSRev.R1988PrintedEnd.endState hY hY0 hα
  have hYu : ∀ t ∈ Icc (0 : ℝ) 4, HasDerivWithinAt Y (uS (2500 / 497) (Y t)) (Icc 0 4) t := by
    intro t ht
    obtain ⟨b1, b2, b3⟩ := hbox t ht
    rw [← vS_eq ht.1 b1.le b2.le b3.le]
    exact hY t ht
  set Tf := flowT (2500 / 497) (Y 4) with hTd
  have hT0 : Tf 0 = Y 4 := flowT_zero _ _
  have hTu := tail (K := 2500 / 497) (by norm_num) (flowT_deriv (2500 / 497) (Y 4))
    (by rw [← hTd, hT0]; exact e1) (by rw [← hTd, hT0]; exact e2) (by rw [← hTd, hT0]; exact e3)
    (by rw [← hTd, hT0]; exact e4)
  set G : ℝ → ℝ × ℝ × ℝ := fun t => if t ≤ 4 then Y t else Tf (t - 4) with hGd
  have hGY : EqOn G Y (Icc 0 4) := fun t ht => by simp only [hGd, if_pos ht.2]
  have hGT : EqOn G (fun t => Tf (t - 4)) (Ici 4) := by
    intro t ht
    rcases eq_or_lt_of_le (show (4 : ℝ) ≤ t from ht) with h | h
    · subst h; simp only [hGd, le_refl, if_true, sub_self, hT0]
    · simp only [hGd, if_neg (not_le.2 h)]
  have hA : ∀ t ∈ Icc (0 : ℝ) 4, HasDerivWithinAt G (uS (2500 / 497) (G t)) (Icc 0 4) t := by
    intro t ht
    rw [hGY ht]
    exact (hYu t ht).congr hGY (hGY ht)
  have hB : ∀ t ∈ Ici (4 : ℝ), HasDerivWithinAt G (uS (2500 / 497) (G t)) (Ici 4) t := by
    intro t ht
    have hm : MapsTo (fun t : ℝ => t - 4) (Ici 4) (Ici 0) := fun x hx => by
      simp only [mem_Ici] at hx ⊢; linarith
    have ht' : t - 4 ∈ Ici (0 : ℝ) := hm ht
    have h1 := (hTu (t - 4) ht').scomp t ((hasDerivWithinAt_id t (Ici 4)).sub_const 4) hm
    rw [one_smul] at h1
    rw [hGT ht]
    exact h1.congr hGT (hGT ht)
  refine ⟨G, by simp only [hGd]; norm_num [hY0], fun t ht => ?_⟩
  have ht0 : (0 : ℝ) ≤ t := ht
  rcases lt_trichotomy t 4 with h | h | h
  · refine (hA t ⟨ht0, h.le⟩).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (inter_mem_nhdsWithin (Ici 0) (Iic_mem_nhds h)) fun x hx => ⟨hx.1, hx.2⟩
  · subst h
    exact ((hA 4 ⟨by norm_num, le_rfl⟩).union (hB 4 (mem_Ici.2 le_rfl))).mono fun x hx => by
      rcases le_total x 4 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
  · exact (hB t h.le).mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h))

/-- Non-vacuity of the printed-value overshoot statement: the Falkner–Skan initial-value problem with
β = −1988/10000, f(0) = 0, p(0) = 0, q(0) = −0.005158 has a solution on [0, ∞). -/
theorem printed_ivp_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ q 0 = -0.005158 := by
  obtain ⟨G, hG0, hG⟩ := scaled_exists
  set c := Real.sqrt (497 / 2500 : ℝ) with hcd
  have hc : 0 < c := Real.sqrt_pos.2 (by norm_num)
  have hc2 : c ^ 2 = 497 / 2500 := Real.sq_sqrt (by norm_num)
  set d := 1 / c with hdd
  have hd : 0 < d := by positivity
  have hF : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (G s).1) ((G s).2.1) (Ici 0) s :=
    fun s hs => (hG s hs).fst
  have hP : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (G s).2.1) ((G s).2.2) (Ici 0) s :=
    fun s hs => (hG s hs).snd.fst
  have hQ : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt (fun s => (G s).2.2)
      (-((2500 / 497) * (G s).1 * (G s).2.2) - (-1) * (1 - (G s).2.1 ^ 2)) (Ici 0) s :=
    fun s hs => by
      have h : HasDerivWithinAt (fun s => (G s).2.2) ((uS (2500 / 497) (G s)).2.2) (Ici 0) s := (hG s hs).snd.snd
      exact h.congr_deriv (by simp only [uS]; ring)
  obtain ⟨A1, A2, A3⟩ := Checked.FalknerSkan.FSScale.scale hd hF hP hQ
  refine ⟨fun s => d * (G (s / d)).1, fun s => (G (s / d)).2.1, fun s => (G (s / d)).2.2 / d,
    A1, A2, fun η hη => (A3 η hη).congr_deriv ?_, ?_, ?_, ?_⟩
  · have hd2 : d ^ 2 = 2500 / 497 := by rw [hdd, div_pow, hc2]; norm_num
    rw [hd2]; ring
  · simp [hG0]
  · simp [hG0]
  · simp only [zero_div, hG0, hdd]
    field_simp
