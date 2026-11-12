import Mathlib
import Work.Math.BEChain
import Checked.Math.GProfile
import Checked.Math.GFinal

/-! Bonnor–Ebert sphere, `BEMain`: assembly of the critical-state theorem from the certified chain
(`Work.Math.BEChain.chain`). The derivative of the mass m(s) = s²(−φ)e^{w/2}/√(4π) is
s² e^{w/2} (e^w − φ²/2)/√(4π); its sign is that of g = e^w − φ²/2, positive on (0, 6.450751440]
and negative on [6.4507515, 7] by the chain; on the bracket cell g is strictly decreasing (g′ = 2e^wφ + 2φ²/s < 0
by the cell enclosure), so g has exactly one zero ξ₁ there. Values at ξ₁ from the enclosure at the bracket's
left end, monotonicity of w and the mean value theorem. Constants: `runs/2026-11-12T0427Z/scripts/be_consts.py`. -/

namespace Work.Math.BEMain
open Set Checked.Sim Checked.Sim.QPoly Checked.Math.GCellQ Work.Math.BECellQ Work.Math.BEQData

theorem hasDerivAt_mass {w φ : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hw : HasDerivAt w (φ s) s)
    (hφ : HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s) :
    HasDerivAt (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
      (s ^ 2 * Real.exp (w s / 2) * (Real.exp (w s) - φ s ^ 2 / 2) / Real.sqrt (4 * Real.pi)) s := by
  have h1 := (((hasDerivAt_pow 2 s).mul hφ.neg).mul ((hw.div_const 2).exp)).div_const
    (Real.sqrt (4 * Real.pi))
  convert h1 using 1
  simp only [Pi.mul_apply, Pi.neg_apply]
  field_simp
  push_cast
  ring

theorem hasDerivAt_g {w φ : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hw : HasDerivAt w (φ s) s)
    (hφ : HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s) :
    HasDerivAt (fun s => Real.exp (w s) - φ s ^ 2 / 2)
      (2 * Real.exp (w s) * φ s + 2 * φ s ^ 2 / s) s := by
  have h1 := hw.exp.sub ((hφ.pow 2).div_const 2)
  convert h1 using 1
  field_simp
  push_cast
  ring

/-- The rational constants of the bracket cell (computed and checked in `be_consts.py`). -/
theorem gap_consts :
    (356073813053/5000000000000 : ℚ) ≤ lo c332.pe c332.h - c332.B ∧
    hi c332.pe c332.h + c332.B ≤ (3560738291909/50000000000000 : ℚ) ∧
    (-7547967420267/20000000000000 : ℚ) ≤ lo c332.pp c332.h - c332.B ∧
    hi c332.pp c332.h + c332.B ≤ (-37739836551561/100000000000000 : ℚ) ∧
    (3560738211159/50000000000000 : ℚ) ≤ c332.pe.headD 0 - c332.B ∧
    c332.pe.headD 0 + c332.B ≤ (44509227641/625000000000 : ℚ) ∧
    (-37739836826569/100000000000000 : ℚ) ≤ c332.pp.headD 0 - c332.B ∧
    c332.pp.headD 0 + c332.B ≤ (-37739836826327/100000000000000 : ℚ) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem bonnor_ebert_critical (S : ℝ) (hS : 7 ≤ S) (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s)
    (hφ0 : ContinuousWithinAt φ (Icc 0 S) 0)
    (hφ : ∀ s ∈ Ioc (0 : ℝ) S,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s)
    (h0 : w 0 = 0) :
    ∃ ξ₁ : ℝ, 6.4507514 ≤ ξ₁ ∧ ξ₁ ≤ 6.4507515 ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc 0 ξ₁) ∧
      StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc ξ₁ 7) ∧
      1.1822265 ≤ ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ₁ ^ 2 * (-φ ξ₁) * Real.exp (w ξ₁ / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 ∧
      14.042032 ≤ Real.exp (-w ξ₁) ∧ Real.exp (-w ξ₁) ≤ 14.042033 := by
  -- restriction to [0, 7]
  have hsub : Icc (0 : ℝ) 7 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  have hw7 : ∀ s ∈ Icc (0 : ℝ) 7, HasDerivWithinAt w (φ s) (Icc 0 7) s :=
    fun s hs => (hw s (hsub hs)).mono hsub
  have hφ07 : ContinuousWithinAt φ (Icc 0 7) 0 := hφ0.mono hsub
  have hφ7 : ∀ s ∈ Ioc (0 : ℝ) 7,
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 7) s :=
    fun s hs => (hφ s ⟨hs.1, hs.2.trans hS⟩).mono hsub
  obtain ⟨C1, C2, C3⟩ := Work.Math.BEChain.chain hw7 hφ07 hφ7 h0
  obtain ⟨P1, P2, -⟩ := Checked.Math.GProfile.profile_bounds 7 (by norm_num) w φ hw7 hφ07 hφ7 h0
  have dv : ∀ s ∈ Ioo (0 : ℝ) 7, HasDerivAt w (φ s) s ∧
      HasDerivAt φ (-(2 / s * φ s) - Real.exp (w s)) s :=
    fun s hs => Checked.Math.GFinal.derivs_at hw7 hφ7 hs
  -- continuity on [0, 7]
  have cw : ContinuousOn w (Icc 0 7) := fun s hs => (hw7 s hs).continuousWithinAt
  have cφ : ContinuousOn φ (Icc 0 7) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact hφ07
    · exact (hφ7 t ⟨h, ht.2⟩).continuousWithinAt
  set m : ℝ → ℝ := fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) with hm
  set g : ℝ → ℝ := fun s => Real.exp (w s) - φ s ^ 2 / 2 with hg
  have cm : ContinuousOn m (Icc 0 7) :=
    ((((continuous_pow 2).continuousOn).mul cφ.neg).mul (cw.div_const 2).rexp).div_const _
  have cg : ContinuousOn g (Icc 0 7) := cw.rexp.sub ((cφ.pow 2).div_const 2)
  clear_value m g
  -- the constants
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 80634393 / 12500000 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 12901503 / 2000000 := ⟨_, rfl⟩
  rw [← hA] at C1 C2
  rw [← hB] at C2 C3
  have hAB : A < B := by rw [hA, hB]; norm_num
  have hB7 : B ≤ 7 := by rw [hB]; norm_num
  have hA0 : 0 < A := by rw [hA]; norm_num
  -- sign of g on (0, A]
  have G1 : ∀ t ∈ Ioc (0 : ℝ) A, 0 < g t := by
    intro t ht
    rcases le_or_gt t (1 / 64) with h | h
    · have t7 : t ∈ Icc (0 : ℝ) 7 := ⟨ht.1.le, by linarith⟩
      obtain ⟨p1, p2⟩ := P1 t t7
      obtain ⟨q1, -⟩ := P2 t t7
      have e1 := Real.add_one_le_exp (w t)
      have hφs : φ t ^ 2 ≤ (t / 3) ^ 2 := by
        rw [← neg_sq (φ t)]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      have ht2 : t ^ 2 ≤ (1 / 64) ^ 2 := pow_le_pow_left₀ ht.1.le h 2
      rw [hg]
      show 0 < Real.exp (w t) - φ t ^ 2 / 2
      nlinarith
    · have := C1 t ⟨h.le, ht.2⟩
      simp only [BInv] at this
      rw [hg]
      show 0 < Real.exp (w t) - φ t ^ 2 / 2
      linarith
  have G3 : ∀ t ∈ Icc B 7, g t < 0 := by
    intro t ht
    have := C3 t ht
    simp only [BInv] at this
    rw [hg]
    show Real.exp (w t) - φ t ^ 2 / 2 < 0
    linarith
  -- enclosure on the bracket cell
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := gap_consts
  have r1 : ((356073813053/5000000000000 : ℚ) : ℝ) ≤ ((lo c332.pe c332.h - c332.B : ℚ) : ℝ) := by
    exact_mod_cast k1
  have r3 : ((-7547967420267/20000000000000 : ℚ) : ℝ) ≤ ((lo c332.pp c332.h - c332.B : ℚ) : ℝ) := by
    exact_mod_cast k3
  have r4 : ((hi c332.pp c332.h + c332.B : ℚ) : ℝ) ≤ ((-37739836551561/100000000000000 : ℚ) : ℝ) := by
    exact_mod_cast k4
  have r5 : ((3560738211159/50000000000000 : ℚ) : ℝ) ≤ ((c332.pe.headD 0 - c332.B : ℚ) : ℝ) := by
    exact_mod_cast k5
  have r6 : ((c332.pe.headD 0 + c332.B : ℚ) : ℝ) ≤ ((44509227641/625000000000 : ℚ) : ℝ) := by
    exact_mod_cast k6
  have r7 : ((-37739836826569/100000000000000 : ℚ) : ℝ) ≤ ((c332.pp.headD 0 - c332.B : ℚ) : ℝ) := by
    exact_mod_cast k7
  have r8 : ((c332.pp.headD 0 + c332.B : ℚ) : ℝ) ≤ ((-37739836826327/100000000000000 : ℚ) : ℝ) := by
    exact_mod_cast k8
  push_cast at r1 r3 r4 r5 r6 r7 r8
  have hh : (c332.h : ℝ) = B - A := by rw [c332_h, hA, hB]; norm_num
  have gapE : ∀ t ∈ Icc A B, 356073813053/5000000000000 ≤ Real.exp (w t) := by
    intro t ht
    have e := abs_le.1 (C2 t ht).1
    have l := lo_le c332.pe (h := c332.h) (σ := t - A) (by linarith [ht.1]) (by rw [hh]; linarith [ht.2])
    linarith [e.1]
  have gapP : ∀ t ∈ Icc A B, -7547967420267/20000000000000 ≤ φ t ∧
      φ t ≤ -37739836551561/100000000000000 := by
    intro t ht
    have e := abs_le.1 (C2 t ht).2
    have l := lo_le c332.pp (h := c332.h) (σ := t - A) (by linarith [ht.1]) (by rw [hh]; linarith [ht.2])
    have u := le_hi c332.pp (h := c332.h) (σ := t - A) (by linarith [ht.1]) (by rw [hh]; linarith [ht.2])
    constructor <;> linarith [e.1, e.2]
  have atA : 3560738211159/50000000000000 ≤ Real.exp (w A) ∧ Real.exp (w A) ≤ 44509227641/625000000000 ∧
      -37739836826569/100000000000000 ≤ φ A ∧ φ A ≤ -37739836826327/100000000000000 := by
    have hA' : A ∈ Icc A B := ⟨le_rfl, hAB.le⟩
    have e := C2 A hA'
    rw [sub_self, evalQ_zero_head, evalQ_zero_head] at e
    have e1 := abs_le.1 e.1
    have e2 := abs_le.1 e.2
    refine ⟨by linarith [e1.1], by linarith [e1.2], by linarith [e2.1], by linarith [e2.2]⟩
  -- g strictly decreasing on the bracket cell
  have gAnti : StrictAntiOn g (Icc A B) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc A B)
      (cg.mono (Icc_subset_Icc hA0.le hB7)) (f' := fun s => 2 * Real.exp (w s) * φ s + 2 * φ s ^ 2 / s)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      have hx7 : x ∈ Ioo (0 : ℝ) 7 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [hg]
      exact (hasDerivAt_g (by linarith [hx.1]) (dv x hx7).1 (dv x hx7).2).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have hxI : x ∈ Icc A B := ⟨hx.1.le, hx.2.le⟩
      have hE := gapE x hxI
      obtain ⟨p1, p2⟩ := gapP x hxI
      have hx0 : 0 < x := by linarith [hx.1]
      have q1 : Real.exp (w x) * φ x ≤ 356073813053/5000000000000 * (-37739836551561/100000000000000) := by
        nlinarith [Real.exp_pos (w x)]
      have q2 : φ x ^ 2 ≤ (7547967420267/20000000000000) ^ 2 := by nlinarith
      have q3 : 2 * φ x ^ 2 / x ≤ 2 * (7547967420267/20000000000000) ^ 2 / A := by
        rw [div_le_div_iff₀ hx0 hA0]
        have hAx : A ≤ x := hx.1.le
        have c0 : (0 : ℝ) ≤ 2 * (7547967420267/20000000000000) ^ 2 := by norm_num
        calc 2 * φ x ^ 2 * A ≤ 2 * (7547967420267/20000000000000) ^ 2 * A :=
              mul_le_mul_of_nonneg_right (by linarith) hA0.le
          _ ≤ 2 * (7547967420267/20000000000000) ^ 2 * x := mul_le_mul_of_nonneg_left hAx c0
      show 2 * Real.exp (w x) * φ x + 2 * φ x ^ 2 / x < 0
      have : 2 * (356073813053/5000000000000 : ℝ) * (-37739836551561/100000000000000) +
          2 * (7547967420267/20000000000000) ^ 2 / A < 0 := by rw [hA]; norm_num
      linarith
  -- the zero ξ₁ of g
  have gA : 0 < g A := G1 A ⟨hA0, le_rfl⟩
  have gB : g B < 0 := G3 B ⟨le_rfl, hB7⟩
  obtain ⟨ξ₁, hξI, hξ0⟩ := intermediate_value_Icc' hAB.le (cg.mono (Icc_subset_Icc hA0.le hB7))
    (show (0 : ℝ) ∈ Icc (g B) (g A) from ⟨gB.le, gA.le⟩)
  have hξ7 : ξ₁ ≤ 7 := hξI.2.trans hB7
  have hξ0' : 0 < ξ₁ := lt_of_lt_of_le hA0 hξI.1
  have Gpos : ∀ t ∈ Ioo (0 : ℝ) ξ₁, 0 < g t := by
    intro t ht
    rcases le_or_gt t A with h | h
    · exact G1 t ⟨ht.1, h⟩
    · have := gAnti ⟨h.le, (ht.2.trans_le hξI.2).le⟩ hξI ht.2
      rw [hξ0] at this; exact this
  have Gneg : ∀ t ∈ Ioo ξ₁ 7, g t < 0 := by
    intro t ht
    rcases lt_or_ge t B with h | h
    · have := gAnti hξI ⟨(hξI.1.trans ht.1.le), h.le⟩ ht.1
      rw [hξ0] at this; exact this
    · exact G3 t ⟨h, ht.2.le⟩
  have dm : ∀ x ∈ Ioo (0 : ℝ) 7, HasDerivAt m
      (x ^ 2 * Real.exp (w x / 2) * g x / Real.sqrt (4 * Real.pi)) x := fun x hx => by
    rw [hm, hg]
    exact hasDerivAt_mass (ne_of_gt hx.1) (dv x hx).1 (dv x hx).2
  have sp : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have mMono : StrictMonoOn m (Icc 0 ξ₁) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 ξ₁)
      (cm.mono (Icc_subset_Icc le_rfl hξ7))
      (f' := fun x => x ^ 2 * Real.exp (w x / 2) * g x / Real.sqrt (4 * Real.pi))
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (dm x ⟨hx.1, hx.2.trans_le hξ7⟩).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have hgx := Gpos x hx
      exact div_pos (mul_pos (mul_pos (pow_pos hx.1 2) (Real.exp_pos _)) hgx) sp
  have mAnti : StrictAntiOn m (Icc ξ₁ 7) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc ξ₁ 7)
      (cm.mono (Icc_subset_Icc hξ0'.le le_rfl))
      (f' := fun x => x ^ 2 * Real.exp (w x / 2) * g x / Real.sqrt (4 * Real.pi))
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (dm x ⟨hξ0'.trans hx.1, hx.2⟩).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have hgx := Gneg x hx
      have hx0 : 0 < x := hξ0'.trans hx.1
      have h1 : 0 < x ^ 2 * Real.exp (w x / 2) := by positivity
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 hgx) sp
  -- values
  have sqE : 26686094548131/100000000000000 ≤ Real.exp (w A / 2) ∧
      Real.exp (w A / 2) ≤ 5337218909717/20000000000000 := by
    rw [Real.exp_half]
    constructor
    · rw [Real.le_sqrt (by norm_num) (Real.exp_pos _).le]; nlinarith [atA.1]
    · rw [Real.sqrt_le_left (by norm_num)]; nlinarith [atA.2.1]
  have sqP : 354490770181103/100000000000000 ≤ Real.sqrt (4 * Real.pi) ∧
      Real.sqrt (4 * Real.pi) ≤ 22155673136319/6250000000000 := by
    have p1 := Real.pi_gt_d20
    have p2 := Real.pi_lt_d20
    constructor
    · rw [Real.le_sqrt (by norm_num) (by positivity)]; norm_num at p1 ⊢; linarith
    · rw [Real.sqrt_le_left (by norm_num)]; norm_num at p2 ⊢; linarith
  have mA_lo : 11822265/10000000 ≤ m A := by
    rw [hm]
    show 11822265/10000000 ≤ A ^ 2 * (-φ A) * Real.exp (w A / 2) / Real.sqrt (4 * Real.pi)
    rw [le_div_iff₀ sp]
    have n1 : A ^ 2 * (37739836826327/100000000000000) * (26686094548131/100000000000000) ≤
        A ^ 2 * (-φ A) * Real.exp (w A / 2) := by
      apply mul_le_mul _ sqE.1 (by norm_num)
        (mul_nonneg (sq_nonneg A) (by linarith [atA.2.2.2]))
      exact mul_le_mul_of_nonneg_left (by linarith [atA.2.2.2]) (sq_nonneg A)
    have n2 : 11822265/10000000 * Real.sqrt (4 * Real.pi) ≤
        11822265/10000000 * (22155673136319/6250000000000) := by nlinarith [sqP.2]
    have n3 : (11822265/10000000 : ℝ) * (22155673136319/6250000000000) ≤
        A ^ 2 * (37739836826327/100000000000000) * (26686094548131/100000000000000) := by
      rw [hA]; norm_num
    linarith
  have mA_hi : m A ≤ A ^ 2 * (37739836826569/100000000000000) * (5337218909717/20000000000000) /
      (354490770181103/100000000000000) := by
    rw [hm]
    show A ^ 2 * (-φ A) * Real.exp (w A / 2) / Real.sqrt (4 * Real.pi) ≤ _
    have n1 : A ^ 2 * (-φ A) * Real.exp (w A / 2) ≤
        A ^ 2 * (37739836826569/100000000000000) * (5337218909717/20000000000000) := by
      apply mul_le_mul _ sqE.2 (Real.exp_pos _).le (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith [atA.2.2.1]) (sq_nonneg A)
    have n0 : 0 ≤ A ^ 2 * (-φ A) * Real.exp (w A / 2) := by
      have : 0 ≤ -φ A := by linarith [atA.2.2.2]
      positivity
    calc A ^ 2 * (-φ A) * Real.exp (w A / 2) / Real.sqrt (4 * Real.pi)
        ≤ A ^ 2 * (-φ A) * Real.exp (w A / 2) / (354490770181103/100000000000000) :=
          div_le_div_of_nonneg_left n0 (by norm_num) sqP.1
      _ ≤ _ := div_le_div_of_nonneg_right n1 (by norm_num)
  -- m(ξ₁) ≥ m(A)
  have mξ_lo : m A ≤ m ξ₁ := by
    rcases eq_or_lt_of_le hξI.1 with h | h
    · rw [h]
    · exact (mMono ⟨hA0.le, hξI.1⟩ ⟨hξ0'.le, le_rfl⟩ h).le
  -- m(ξ₁) ≤ m(A) + (B − A) B² g(A) by the mean value theorem
  have gA_hi : g A ≤ 44509227641/625000000000 - (37739836826327/100000000000000) ^ 2 / 2 := by
    rw [hg]
    show Real.exp (w A) - φ A ^ 2 / 2 ≤ _
    have h1 : (0 : ℝ) ≤ 37739836826327/100000000000000 := by norm_num
    have h2 : (37739836826327/100000000000000 : ℝ) ≤ -φ A := by linarith [atA.2.2.2]
    have : (37739836826327/100000000000000 : ℝ) ^ 2 ≤ φ A ^ 2 := by
      rw [← neg_sq (φ A)]; exact pow_le_pow_left₀ h1 h2 2
    linarith [atA.2.1]
  have mξ_hi : m ξ₁ ≤ m A + (B - A) * (B ^ 2 *
      (44509227641/625000000000 - (37739836826327/100000000000000) ^ 2 / 2)) := by
    rcases eq_or_lt_of_le hξI.1 with h | h
    · rw [← h]
      have : 0 ≤ (B - A) * (B ^ 2 *
          (44509227641/625000000000 - (37739836826327/100000000000000 : ℝ) ^ 2 / 2)) := by
        rw [hA, hB]; norm_num
      linarith
    · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope m
        (fun x => x ^ 2 * Real.exp (w x / 2) * g x / Real.sqrt (4 * Real.pi)) h
        (cm.mono (Icc_subset_Icc hA0.le hξ7))
        (fun x hx => dm x ⟨hA0.trans hx.1, hx.2.trans_le hξ7⟩)
      beta_reduce at hcs
      have hcI : c ∈ Icc A B := ⟨hc.1.le, (hc.2.trans_le hξI.2).le⟩
      have gc : g c < g A := gAnti ⟨le_rfl, hAB.le⟩ hcI hc.1
      have gc0 : 0 < g c := Gpos c ⟨hA0.trans hc.1, hc.2⟩
      have c7 : c ∈ Icc (0 : ℝ) 7 := ⟨(hA0.trans hc.1).le, (hc.2.trans_le hξ7).le⟩
      have ew : Real.exp (w c / 2) ≤ 1 := by
        have := (P2 c c7).2
        rw [Real.exp_le_one_iff]; linarith only [this]
      have s1 : 1 ≤ Real.sqrt (4 * Real.pi) := by linarith only [sqP.1]
      have cB : c ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (hA0.trans hc.1).le hcI.2 2
      have dle : c ^ 2 * Real.exp (w c / 2) * g c / Real.sqrt (4 * Real.pi) ≤
          B ^ 2 * (44509227641/625000000000 - (37739836826327/100000000000000) ^ 2 / 2) := by
        rw [div_le_iff₀ sp]
        have e1 : c ^ 2 * Real.exp (w c / 2) * g c ≤ B ^ 2 * 1 * g A := by
          apply mul_le_mul (mul_le_mul cB ew (Real.exp_pos _).le (sq_nonneg B)) gc.le gc0.le
            (by positivity)
        have e2 : B ^ 2 * 1 * g A ≤ B ^ 2 *
            (44509227641/625000000000 - (37739836826327/100000000000000) ^ 2 / 2) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left gA_hi (sq_nonneg B)
        have e3 : 0 ≤ B ^ 2 * (44509227641/625000000000 - (37739836826327/100000000000000 : ℝ) ^ 2 / 2) := by
          rw [hB]; norm_num
        exact (e1.trans e2).trans (le_mul_of_one_le_right e3 s1)
      rw [hcs] at dle
      have hpos : 0 < ξ₁ - A := by linarith
      rw [div_le_iff₀ hpos] at dle
      have : (ξ₁ - A) * (B ^ 2 *
          (44509227641/625000000000 - (37739836826327/100000000000000 : ℝ) ^ 2 / 2)) ≤
          (B - A) * (B ^ 2 *
          (44509227641/625000000000 - (37739836826327/100000000000000 : ℝ) ^ 2 / 2)) := by
        apply mul_le_mul_of_nonneg_right (by linarith [hξI.2])
        rw [hB]; norm_num
      linarith
  -- contrast
  have wanti : w ξ₁ ≤ w A := by
    have hanti : AntitoneOn w (Icc 0 7) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 7) cw (f' := φ)
        (fun x hx => ?_) (fun x hx => ?_)
      · rw [interior_Icc] at hx; exact (dv x hx).1.hasDerivWithinAt
      · rw [interior_Icc] at hx; exact (P1 x ⟨hx.1.le, hx.2.le⟩).2
    exact hanti ⟨hA0.le, (hAB.le.trans hB7)⟩ ⟨hξ0'.le, hξ7⟩ hξI.1
  have Eξ_lo : 356073813053/5000000000000 ≤ Real.exp (w ξ₁) := gapE ξ₁ hξI
  have Eξ_hi : Real.exp (w ξ₁) ≤ 44509227641/625000000000 :=
    (Real.exp_le_exp.2 wanti).trans atA.2.1
  have mlo : 1.1822265 ≤ m ξ₁ := by
    have := mA_lo.trans mξ_lo; norm_num at this ⊢; linarith
  have mhi : m ξ₁ ≤ 1.1822266 := by
    have h2 : A ^ 2 * (37739836826569/100000000000000) * (5337218909717/20000000000000) /
        (354490770181103/100000000000000) + (B - A) * (B ^ 2 *
        (44509227641/625000000000 - (37739836826327/100000000000000 : ℝ) ^ 2 / 2)) ≤ 1.1822266 := by
      rw [hA, hB]; norm_num
    linarith [mξ_hi, mA_hi]
  rw [hm] at mlo mhi
  beta_reduce at mlo mhi
  refine ⟨ξ₁, ?_, ?_, mMono, mAnti, mlo, mhi, ?_, ?_⟩
  · have := hξI.1; rw [hA] at this; norm_num at this ⊢; linarith
  · have := hξI.2; rw [hB] at this; norm_num at this ⊢; linarith
  · rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    have : (44509227641/625000000000 : ℝ) ≤ (14.042032 : ℝ)⁻¹ := by norm_num
    linarith
  · rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have : (14.042033 : ℝ)⁻¹ ≤ 356073813053/5000000000000 := by norm_num
    linarith

end Work.Math.BEMain
