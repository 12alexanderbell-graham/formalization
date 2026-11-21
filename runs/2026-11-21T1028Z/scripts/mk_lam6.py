"""Work/Math/GelfandLam6.lean from Checked/Math/GelfandLam4.lean: the proof of lam34_band continued through the
segments of Work.Math.GSegData7 to the sixth and seventh turning points (asserted replacements)."""
src = open("Checked/Math/GelfandLam4.lean").read()
body = src.split("set_option maxHeartbeats 8000000 in\n", 1)[1]
body = body.rsplit("  have b3 := uC3 z3 z3in\n", 1)[0]
reps = [
 ("theorem lam34_band", "theorem lam3456_band"),
 ("of λ at ζ 3 lies in [1.967422, 1.967510] and the value of λ at ζ 4 lies in [2.009926, 2.010028]. -/",
  "of λ at ζ 3 lies in [1.967422, 1.967510], at ζ 4 in [2.009926, 2.010028], at ζ 5 in [1.996901, 1.997023] and\nat ζ 6 in [2.000873, 2.000980]. -/"),
 ("    (2.009926 ≤ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ∧ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ≤ 2.010028) := by",
  "    (2.009926 ≤ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ∧ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ≤ 2.010028) ∧\n"
  "    (1.996901 ≤ ζ 5 ^ 2 * Real.exp (w (ζ 5)) ∧ ζ 5 ^ 2 * Real.exp (w (ζ 5)) ≤ 1.997023) ∧\n"
  "    (2.000873 ≤ ζ 6 ^ 2 * Real.exp (w (ζ 6)) ∧ ζ 6 ^ 2 * Real.exp (w (ζ 6)) ≤ 2.000980) := by"),
]
for a, b in reps:
    assert body.count(a) == 1, a
    body = body.replace(a, b)
cont = r'''  -- segment D to its end; the segments of GSegData7
  have endD := chain_end segD _ segD_len segD_ok neD (τ₀ := tD) (du _ _) (dv _ _) stD
  have stE := link_q (c := lst segD) (d := hd segE) linkDE endD
  have neE : segE ≠ [] := by unfold segE; exact List.cons_ne_nil _ _
  have neC5 : segC5 ≠ [] := by unfold segC5; exact List.cons_ne_nil _ _
  have neF : segF ≠ [] := by unfold segF; exact List.cons_ne_nil _ _
  have neC6 : segC6 ≠ [] := by unfold segC6; exact List.cons_ne_nil _ _
  have neG : segG ≠ [] := by unfold segG; exact List.cons_ne_nil _ _
  -- segment E: v above two
  set tE : ℝ := tD + ((1 / 1000 : ℚ) : ℝ) with htE
  have allE := seg_all' (fun _ b => ((2 : ℚ) : ℝ) < b) (vGtB 2) (vGt_rel 2) segE _ segE_len segE_ok neE
    segE_pred (τ₀ := tE) (du _ _) (dv _ _) stE
  have endE := chain_end segE _ segE_len segE_ok neE (τ₀ := tE) (du _ _) (dv _ _) stE
  have stC5 := link_q (c := lst segE) (d := hd segC5) linkEC5 endE
  -- segment C5: u in [L5, U5]
  set tC5 : ℝ := tE + ((11801 / 5000 : ℚ) : ℝ) with htC5
  have allC5 := seg_all' (fun a _ => ((L5 : ℚ) : ℝ) < a ∧ a < ((U5 : ℚ) : ℝ)) (uInB L5 U5) (uIn_rel L5 U5)
    segC5 _ segC5_len segC5_ok neC5 segC5_pred (τ₀ := tC5) (du _ _) (dv _ _) stC5
  have endC5 := chain_end segC5 _ segC5_len segC5_ok neC5 (τ₀ := tC5) (du _ _) (dv _ _) stC5
  have stF := link_q (c := lst segC5) (d := hd segF) linkC5F endC5
  -- segment F: v below two
  set tF : ℝ := tC5 + ((1 / 50 : ℚ) : ℝ) with htF
  have allF := seg_all' (fun _ b => b < ((2 : ℚ) : ℝ)) (vLtB 2) (vLt_rel 2) segF _ segF_len segF_ok neF
    segF_pred (τ₀ := tF) (du _ _) (dv _ _) stF
  have endF := chain_end segF _ segF_len segF_ok neF (τ₀ := tF) (du _ _) (dv _ _) stF
  have stC6 := link_q (c := lst segF) (d := hd segC6) linkFC6 endF
  -- segment C6: u in [L6, U6]
  set tC6 : ℝ := tF + ((23403 / 10000 : ℚ) : ℝ) with htC6
  have allC6 := seg_all' (fun a _ => ((L6 : ℚ) : ℝ) < a ∧ a < ((U6 : ℚ) : ℝ)) (uInB L6 U6) (uIn_rel L6 U6)
    segC6 _ segC6_len segC6_ok neC6 segC6_pred (τ₀ := tC6) (du _ _) (dv _ _) stC6
  have endC6 := chain_end segC6 _ segC6_len segC6_ok neC6 (τ₀ := tC6) (du _ _) (dv _ _) stC6
  have stG := link_q (c := lst segC6) (d := hd segG) linkC6G endC6
  -- segment G: v above two
  set tG : ℝ := tC6 + ((1 / 20 : ℚ) : ℝ) with htG
  have allG := seg_all' (fun _ b => ((2 : ℚ) : ℝ) < b) (vGtB 2) (vGt_rel 2) segG _ segG_len segG_ok neG
    segG_pred (τ₀ := tG) (du _ _) (dv _ _) stG
  -- in the radius
  have vE := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => ((2 : ℚ) : ℝ) < b) allE
  have uC5 := to_radius' (Uf := Uf) (Vf := Vf) (R := fun a _ => ((L5 : ℚ) : ℝ) < a ∧ a < ((U5 : ℚ) : ℝ)) allC5
  have vF := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => b < ((2 : ℚ) : ℝ)) allF
  have uC6 := to_radius' (Uf := Uf) (Vf := Vf) (R := fun a _ => ((L6 : ℚ) : ℝ) < a ∧ a < ((U6 : ℚ) : ℝ)) allC6
  have vG := to_radius' (Uf := Uf) (Vf := Vf) (R := fun _ b => ((2 : ℚ) : ℝ) < b) allG
  have eL5 : ((L5 : ℚ) : ℝ) = 9984509 / 10000000 := by rw [show L5 = 9984509 / 10000000 from rfl]; norm_num
  have eU5 : ((U5 : ℚ) : ℝ) = 9985113 / 10000000 := by rw [show U5 = 9985113 / 10000000 from rfl]; norm_num
  have eL6 : ((L6 : ℚ) : ℝ) = 625273 / 625000 := by rw [show L6 = 625273 / 625000 from rfl]; norm_num
  have eU6 : ((U6 : ℚ) : ℝ) = 100049 / 100000 := by rw [show U6 = 100049 / 100000 from rfl]; norm_num
  rw [eL5, eU5] at uC5; rw [eL6, eU6] at uC6; rw [e2] at vE vF vG
  set S5a : ℝ := Real.exp tC5 with hS5a
  set S5b : ℝ := Real.exp tF with hS5b
  set S6a : ℝ := Real.exp tC6 with hS6a
  set S6b : ℝ := Real.exp tG with hS6b
  have o5 : S5a < S5b := by rw [hS5a, hS5b, htF]; apply Real.exp_lt_exp.2; push_cast; linarith
  have o56 : S5b < S6a := by rw [hS5b, hS6a, htC6]; apply Real.exp_lt_exp.2; push_cast; linarith
  have o6 : S6a < S6b := by rw [hS6a, hS6b, htG]; apply Real.exp_lt_exp.2; push_cast; linarith
  have oDE : Real.exp (tD + ((1 / 1000 : ℚ) : ℝ)) = Real.exp tE := rfl
  have oE5 : Real.exp tE ≤ S5a := by rw [hS5a, htC5]; apply Real.exp_le_exp.2; push_cast; linarith
  have oG : S6b ≤ Real.exp (tG + ((1 / 1000 : ℚ) : ℝ)) := by
    rw [hS6b]; apply Real.exp_le_exp.2; push_cast; linarith
  have o45 : S4b ≤ Real.exp tE := by rw [hS4b, htE]; apply Real.exp_le_exp.2; push_cast; linarith
  -- the facts at the bracket ends
  have v5a : 2 < Vf S5a := vE S5a ⟨oE5, le_rfl⟩
  have v5b : Vf S5b < 2 := vF S5b ⟨le_rfl, o56.le⟩
  have v6a : Vf S6a < 2 := vF S6a ⟨o56.le, le_rfl⟩
  have v6b : 2 < Vf S6b := vG S6b ⟨le_rfl, oG⟩
  have s5apos : 0 < S5a := Real.exp_pos _
  have s6apos : 0 < S6a := Real.exp_pos _
  -- the sixth turning point is in the third bracket (u below one: v decreasing)
  have Vanti5 := V_anti E (a := S5a) (b := S5b) s5apos fun x hx =>
    lt_trans (uC5 x hx).2 (by norm_num)
  obtain ⟨z5, hz5, hVz5⟩ : ∃ z5 ∈ Ioo S5a S5b, Vf z5 = 2 :=
    intermediate_value_Ioo' o5.le
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨v5b, v5a⟩
  have z5mem : z5 ∈ Icc S5a S5b := Ioo_subset_Icc_self hz5
  -- the seventh turning point is in the fourth bracket (u above one: v increasing)
  have Vmono6 := V_mono E (a := S6a) (b := S6b) s6apos fun x hx =>
    lt_trans (by norm_num) (uC6 x hx).1
  obtain ⟨z6, hz6, hVz6⟩ : ∃ z6 ∈ Ioo S6a S6b, Vf z6 = 2 :=
    intermediate_value_Ioo o6.le
      (fun t ht => ((hom_at E (by linarith [ht.1])).2.continuousAt.continuousWithinAt)) ⟨v6a, v6b⟩
  have z6mem : z6 ∈ Icc S6a S6b := Ioo_subset_Icc_self hz6
  have z45 : z4 < z5 := by linarith [hz4.2, z5mem.1, o45, oE5]
  have z56 : z5 < z6 := by linarith [hz5.2, z6mem.1, o56]
  -- signs of Y between the zeros
  have Y45 : ∀ x ∈ Ioo z4 z5, 0 < Y φ x := by
    intro x hx
    rw [hYV]
    rcases le_or_gt x S4b with h | h
    · have := Vmono4 z4mem ⟨by linarith [hx.1, z4mem.1], h⟩ hx.1
      linarith
    rcases le_or_gt x (Real.exp tE) with h' | h'
    · linarith [vD x ⟨h.le, h'⟩]
    rcases le_or_gt x S5a with h'' | h''
    · linarith [vE x ⟨h'.le, h''⟩]
    · have := Vanti5 ⟨h''.le, by linarith [hx.2, z5mem.2]⟩ z5mem hx.2
      linarith
  have Y56 : ∀ x ∈ Ioo z5 z6, Y φ x < 0 := by
    intro x hx
    rw [hYV]
    rcases le_or_gt x S5b with h | h
    · have := Vanti5 z5mem ⟨by linarith [hx.1, z5mem.1], h⟩ hx.1
      linarith
    rcases le_or_gt x S6a with h' | h'
    · linarith [vF x ⟨h.le, h'⟩]
    · have := Vmono6 ⟨h'.le, by linarith [hx.2, z6mem.2]⟩ z6mem hx.2
      linarith
  have Y6 : ∀ x ∈ Ioo z6 S6b, 0 < Y φ x := by
    intro x hx
    rw [hYV]
    have := Vmono6 z6mem ⟨by linarith [hx.1, z6mem.1], hx.2.le⟩ hx.1
    linarith
  have A45 := lam_anti E (a := z4) (b := z5) (by linarith [z4mem.1]) Y45
  have M56 := lam_mono E (a := z5) (b := z6) (by linarith [z5mem.1]) Y56
  have A6 := lam_anti E (a := z6) (b := S6b) (by linarith [z6mem.1]) Y6
  have I3 : StrictMonoOn (lam w) (Icc (ζ 5) (ζ 6)) := hmono 2
  have D3 : StrictAntiOn (lam w) (Icc (ζ 6) (ζ 7)) := hanti 3
  have h56 : ζ 5 < ζ 6 := hm (by norm_num)
  have h67 : ζ 6 < ζ 7 := hm (by norm_num)
  have e5 : ζ 5 = z5 := by
    rcases lt_trichotomy (ζ 5) z5 with h | h | h
    · exfalso
      exact no_both (a := ζ 5) (b := min z5 (ζ 6)) (lt_min h h56) I3 A45
        ⟨le_rfl, h56.le⟩ ⟨le_min h.le h56.le, min_le_right _ _⟩
        ⟨by rw [← e4]; exact h45.le, h.le⟩ ⟨by rw [← e4]; linarith [le_min h.le h56.le, h45], min_le_left _ _⟩
    · exact h
    · exfalso
      exact no_both (a := z5) (b := min (ζ 5) z6) (lt_min h z56) M56 D2
        ⟨le_rfl, z56.le⟩ ⟨le_min h.le z56.le, min_le_right _ _⟩
        ⟨by rw [e4]; exact z45.le, h.le⟩
        ⟨by rw [e4]; linarith [le_min h.le z56.le], min_le_left _ _⟩
  have e6 : ζ 6 = z6 := by
    rcases lt_trichotomy (ζ 6) z6 with h | h | h
    · exfalso
      exact no_both (a := ζ 6) (b := min z6 (ζ 7)) (lt_min h h67) M56 D3
        ⟨by rw [← e5]; exact h56.le, h.le⟩ ⟨by rw [← e5]; linarith [le_min h.le h67.le, h56], min_le_left _ _⟩
        ⟨le_rfl, h67.le⟩ ⟨le_min h.le h67.le, min_le_right _ _⟩
    · exact h
    · exfalso
      have hlt : z6 < S6b := hz6.2
      exact no_both (a := z6) (b := min (ζ 6) S6b) (lt_min h hlt) I3 A6
        ⟨by rw [e5]; exact z56.le, h.le⟩ ⟨by rw [e5]; linarith [le_min h.le hlt.le], min_le_left _ _⟩
        ⟨le_rfl, hlt.le⟩ ⟨le_min h.le hlt.le, min_le_right _ _⟩
  have z5pos : 0 < z5 := by linarith [z5mem.1]
  have k5 := at_zero_U E z5pos (by rw [hYV, hVz5]; ring)
  have l5 : ζ 5 ^ 2 * Real.exp (w (ζ 5)) = 2 * Uf z5 := by
    rw [e5]; have : U w φ z5 = Uf z5 := rfl; rw [← this, k5]; unfold lam; ring
  have z6pos : 0 < z6 := by linarith [z6mem.1]
  have k6 := at_zero_U E z6pos (by rw [hYV, hVz6]; ring)
  have l6 : ζ 6 ^ 2 * Real.exp (w (ζ 6)) = 2 * Uf z6 := by
    rw [e6]; have : U w φ z6 = Uf z6 := rfl; rw [← this, k6]; unfold lam; ring
  have b3 := uC3 z3 z3in
  have b4 := uC4 z4 z4mem
  have b5 := uC5 z5 z5mem
  have b6 := uC6 z6 z6mem
  rw [l3, l4, l5, l6]
  norm_num
  exact ⟨⟨by linarith [b3.1], by linarith [b3.2]⟩, ⟨by linarith [b4.1], by linarith [b4.2]⟩,
    ⟨by linarith [b5.1], by linarith [b5.2]⟩, ⟨by linarith [b6.1], by linarith [b6.2]⟩⟩

end Work.Math.GelfandLam6
'''
head = '''import Checked.Math.GelfandLam4
import Work.Math.GSegData7

/-! Gelfand problem, `GelfandLam6` (run 2026-11-21T1028Z): the value of the branch parameter λ(s) = s² e^{w(s)} of
the regular isothermal solution at its fourth to seventh turning points, for every sequence of turning points with
the monotonicity pattern of `Checked.Math.GelfandExtrema.gelfand_extrema`. Route: the proof of
`Checked.Math.GelfandLam4.lam34_band`, continued from the last cell of `GSegData` through the segments of
`GSegData7` (v above two, u in a window below one, v below two, u in a window above one, v above two); the zeros of
v − two in the two new brackets by the intermediate value theorem, identified with the sixth and seventh turning
points by strict monotonicity of λ at two points, and λ = two times u at a zero of v − two. -/

namespace Work.Math.GelfandLam6
open Set Checked.Math.GelfandExtremaMain Checked.Math.GLamCell Checked.Math.GLamBands
open Checked.Math.GContract Checked.Math.GSeg Checked.Math.GSegData Work.Math.GSegData7 Checked.Sim
open Checked.Math.GelfandLam4

set_option maxHeartbeats 16000000 in
'''
open("Work/Math/GelfandLam6.lean", "w").write(head + body + cont)
