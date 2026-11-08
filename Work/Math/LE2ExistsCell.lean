import Checked.Sim.DuffingExists
import Work.Math.LENCellQ

/-!
# Lane–Emden index two: validated cells for the clamped flow (existence, run 2026-11-08T0228Z)

The clamped field `Fc t (θ, φ) = (cl 1 φ, −(2/t) cl 1 φ − (cl 1 θ)²)` is globally Lipschitz and
bounded for t ≥ 1/2 (Picard–Lindelöf applies on [1/2, 5]). On the box |θ| ≤ TH ≤ 1, |φ| ≤ 1 it
equals the Lane–Emden field of index two, so the validated cell step (`tube_cell_t`, confinement by
the enclosure itself) applies to the clamped flow directly once the cell's approximation stays a
margin inside the box (`boxOK`). The enclosure then shows the clamps inactive on the cell.
Chains of such cells are checked by kernel evaluation (`segOKC`), on the cell data of
`Work.Math.LENCellQ`.
-/

namespace Work.Math.LE2ExistsCell
open Set Checked.Sim Checked.Sim.QPoly Checked.Sim.DuffingExists Work.Math.LENCell Work.Math.LENCellQ

/-- Clamped Lane–Emden field of index two. -/
noncomputable def Fc (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cl 1 p.2, -(2 / t * cl 1 p.2) - cl 1 p.1 ^ 2)

/-- The box where the clamps are inactive. -/
def box (TH : ℝ) : Set (ℝ × ℝ) := {p | |p.1| ≤ TH ∧ |p.2| ≤ 1}

theorem Fc_eq {TH t : ℝ} (hTH : TH ≤ 1) {p : ℝ × ℝ} (hp : p ∈ box TH) : Fc t p = leF 2 t p := by
  simp only [Fc, leF, cl_of_abs_le hp.2, cl_of_abs_le (hp.1.trans hTH)]

/-- One validated cell for the clamped flow: the enclosure holds on the whole cell. -/
theorem cellC (pt pp : List ℚ) {θ φ : ℝ → ℝ} {t0 h δ ε B TH K : ℝ}
    (ht0 : 0 < t0) (hh : 0 < h) (hK1 : 1 ≤ K)
    (hK : 2 / t0 + ((2 : ℕ) : ℝ) * TH ^ (2 - 1) ≤ K) (hKh : K * h < 1) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hTH : TH ≤ 1)
    (hθ : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt θ (cl 1 (φ t)) (Icc t0 (t0 + h)) t)
    (hφ : ∀ t ∈ Icc t0 (t0 + h),
      HasDerivWithinAt φ (-(2 / t * cl 1 (φ t)) - cl 1 (θ t) ^ 2) (Icc t0 (t0 + h)) t)
    (ht1 : ∀ σ ∈ Icc 0 h, -(TH - 1 / 100) ≤ evalQ pt σ)
    (ht2 : ∀ σ ∈ Icc 0 h, evalQ pt σ ≤ TH - 1 / 100)
    (hp1 : ∀ σ ∈ Icc 0 h, -(1 - 1 / 100) ≤ evalQ pp σ)
    (hp2 : ∀ σ ∈ Icc 0 h, evalQ pp σ ≤ 1 - 1 / 100)
    (hd1 : ∀ σ ∈ Icc 0 h, |dEvalQ pt σ - evalQ pp σ| ≤ ε)
    (hd2 : ∀ σ ∈ Icc 0 h,
      |(t0 + σ) * dEvalQ pp σ + 2 * evalQ pp σ + (t0 + σ) * evalQ pt σ ^ 2| ≤ ε * t0)
    (h0 : |θ t0 - evalQ pt 0| ≤ δ) (h0' : |φ t0 - evalQ pp 0| ≤ δ)
    (hB : δ * (1 / (1 - K * h)) + ε / K * (1 / (1 - K * h) - 1) ≤ B)
    (hBM : B < 1 / 100) :
    ∀ t ∈ Icc t0 (t0 + h), |θ t - evalQ pt (t - t0)| ≤ B ∧ |φ t - evalQ pp (t - t0)| ≤ B := by
  have hK0 : (0 : ℝ) < K := by linarith
  have hs : ∀ t ∈ Icc t0 (t0 + h), t - t0 ∈ Icc 0 h := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set f : ℝ → ℝ × ℝ := fun t => (θ t, φ t) with hfdef
  set g : ℝ → ℝ × ℝ := fun t => (evalQ pt (t - t0), evalQ pp (t - t0)) with hg
  have hfd : ∀ t ∈ Icc t0 (t0 + h), HasDerivWithinAt f (Fc t (f t)) (Icc t0 (t0 + h)) t :=
    fun t ht => (hθ t ht).prodMk (hφ t ht)
  have hgbox : ∀ t ∈ Icc t0 (t0 + h), g t ∈ box TH := fun t ht => by
    have g1 := ht1 _ (hs t ht)
    have g2 := ht2 _ (hs t ht)
    have p1 := hp1 _ (hs t ht)
    have p2 := hp2 _ (hs t ht)
    refine ⟨?_, ?_⟩
    · show |evalQ pt (t - t0)| ≤ TH
      rw [abs_le]; constructor <;> linarith
    · show |evalQ pp (t - t0)| ≤ 1
      rw [abs_le]; constructor <;> linarith
  have key := tube_cell_t (F := Fc) (K := Real.toNNReal K) (S := box TH) (f := f) (g := g)
    (g' := fun t => (dEvalQ pt (t - t0), dEvalQ pp (t - t0))) (a := t0) (b := t0 + h)
    (δ := δ) (ε := ε) (B := B) (B' := 1 / 100)
    (fun t ht => by
      have hL := (lip_slab 2 ht0 ht.1 hK1 hK).mono
        (show box TH ⊆ slab TH from fun p hp => hp.1)
      refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
      rw [Fc_eq hTH hp, Fc_eq hTH hq]
      exact hL.dist_le_mul p hp q hq) (by linarith)
    (fun t ht => (hfd t ht).continuousWithinAt)
    (fun t ht => (hfd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩))
    (((continuous_evalQ pt).comp (continuous_sub_right t0)).prodMk
      ((continuous_evalQ pp).comp (continuous_sub_right t0))).continuousOn
    (fun t _ => (((hasDerivAt_evalQ pt (t - t0)).comp_sub_const t t0).prodMk
      ((hasDerivAt_evalQ pp (t - t0)).comp_sub_const t t0)).hasDerivWithinAt)
    (fun t ht => by
      have hσ := hs t (Ico_subset_Icc_self ht)
      have htpos : 0 < t := lt_of_lt_of_le ht0 ht.1
      rw [Fc_eq hTH (hgbox t (Ico_subset_Icc_self ht))]
      simp only [hg, leF, Prod.dist_eq, Real.dist_eq]
      refine max_le (hd1 _ hσ) ?_
      have h2 := hd2 _ hσ
      have et : t0 + (t - t0) = t := by ring
      rw [et] at h2
      have e : dEvalQ pp (t - t0) - (-(2 / t * evalQ pp (t - t0)) - evalQ pt (t - t0) ^ 2) =
          (t * dEvalQ pp (t - t0) + 2 * evalQ pp (t - t0) + t * evalQ pt (t - t0) ^ 2) / t := by
        field_simp
        ring
      rw [e, abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
      exact h2.trans (mul_le_mul_of_nonneg_left ht.1 hε))
    (fun t ht z hz => by
      simp only [hg, Prod.dist_eq, Real.dist_eq, max_lt_iff] at hz
      have g1 := ht1 _ (hs t ht)
      have g2 := ht2 _ (hs t ht)
      have p1 := hp1 _ (hs t ht)
      have p2 := hp2 _ (hs t ht)
      have a1 := abs_lt.1 hz.1
      have a2 := abs_lt.1 hz.2
      refine ⟨?_, ?_⟩
      · show |z.1| ≤ TH
        rw [abs_le]; constructor <;> linarith [a1.1, a1.2]
      · show |z.2| ≤ 1
        rw [abs_le]; constructor <;> linarith [a2.1, a2.2])
    hBM
    (by
      simp only [hfdef, hg, sub_self, Prod.dist_eq, Real.dist_eq]
      exact max_le h0 h0')
    (fun t ht => by
      rw [Real.coe_toNNReal _ hK0.le]
      have := gronwallBound_le_cell (K := K) hδ hε hK0
        (show t - t0 ≤ h by linarith [ht.2]) hh hKh
      exact this.trans hB)
  intro t ht
  have h1 := key t ht
  simp only [hfdef, hg, Prod.dist_eq, Real.dist_eq] at h1
  exact ⟨(le_max_left _ _).trans h1, (le_max_right _ _).trans h1⟩

/-- The approximation of φ stays a margin inside the clamp, and the slab is inside the clamp. -/
def boxOK (c : Cell) : Bool :=
  decide (c.TH ≤ 1 ∧ -(1 - 1 / 100) ≤ c.pp.headD 0 - c.h * qabs c.pp.tail c.h ∧
    c.pp.headD 0 + c.h * qabs c.pp.tail c.h ≤ 1 - 1 / 100)

/-- The clamped flow on the cell, from its Boolean checks: enclosure on the whole cell. -/
theorem cell_qC {T : ℚ} (c : Cell) (hok : cellOK 2 T c = true) (hbox : boxOK c = true)
    {θ φ : ℝ → ℝ}
    (hθ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt θ (cl 1 (φ t)) (Icc (c.t0 : ℝ) (c.t0 + c.h)) t)
    (hφ : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      HasDerivWithinAt φ (-(2 / t * cl 1 (φ t)) - cl 1 (θ t) ^ 2) (Icc (c.t0 : ℝ) (c.t0 + c.h)) t)
    (h0 : |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ)
    (h0' : |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      |θ t - evalQ c.pt (t - c.t0)| ≤ c.B ∧ |φ t - evalQ c.pp (t - c.t0)| ≤ c.B := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ :
    CellProp 2 T c := of_decide_eq_true hok
  obtain ⟨b1, b2, b3⟩ := of_decide_eq_true hbox
  have r14 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k14
  have r5 : ((2 / c.t0 + (2 : ℕ) * c.TH ^ (2 - 1) : ℚ) : ℝ) ≤ (c.K : ℝ) := by exact_mod_cast k5
  have r9 : ((-(c.TH - 1 / 100) : ℚ) : ℝ) ≤ ((c.pt.headD 0 - c.h * qabs c.pt.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast k9
  have r10 : ((c.pt.headD 0 + c.h * qabs c.pt.tail c.h : ℚ) : ℝ) ≤ ((c.TH - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast k10
  have s2 : ((-(1 - 1 / 100) : ℚ) : ℝ) ≤ ((c.pp.headD 0 - c.h * qabs c.pp.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast b2
  have s3 : ((c.pp.headD 0 + c.h * qabs c.pp.tail c.h : ℚ) : ℝ) ≤ ((1 - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast b3
  have r11 : ((qabs (qsub (qderiv c.pt) c.pp) c.h : ℚ) : ℝ) ≤ (c.ε : ℝ) := by exact_mod_cast k11
  have r12 : ((qabs (defect2 2 c) c.h : ℚ) : ℝ) ≤ ((c.ε * c.t0 : ℚ) : ℝ) := by exact_mod_cast k12
  have r13 : ((c.δ * (1 / (1 - c.K * c.h)) + c.ε / c.K * (1 / (1 - c.K * c.h) - 1) : ℚ) : ℝ) ≤
      (c.B : ℝ) := by exact_mod_cast k13
  push_cast at r5 r9 r10 r12 r13 r14 s2 s3
  refine cellC c.pt c.pp (t0 := (c.t0 : ℝ)) (h := (c.h : ℝ)) (δ := (c.δ : ℝ))
    (ε := (c.ε : ℝ)) (B := (c.B : ℝ)) (TH := (c.TH : ℝ)) (K := (c.K : ℝ))
    (by exact_mod_cast k1) (by exact_mod_cast k3) (by exact_mod_cast k4)
    (by push_cast; linarith [r5]) (by exact_mod_cast k6) (by exact_mod_cast k7)
    (by exact_mod_cast k8) (by exact_mod_cast b1)
    hθ hφ ?_ ?_ ?_ ?_ ?_ ?_ (by rw [evalQ_zero_head]; exact h0) (by rw [evalQ_zero_head]; exact h0')
    r13 r14
  · intro σ hσ
    have := lower_q c.pt (h := c.h) hσ.1 hσ.2
    push_cast at this; linarith
  · intro σ hσ
    have := upper_q c.pt (h := c.h) hσ.1 hσ.2
    push_cast at this; linarith
  · intro σ hσ
    have := lower_q c.pp (h := c.h) hσ.1 hσ.2
    push_cast at this; linarith
  · intro σ hσ
    have := upper_q c.pp (h := c.h) hσ.1 hσ.2
    push_cast at this; linarith
  · intro σ hσ
    rw [dEvalQ_eq, ← evalQ_qsub]
    exact (abs_le_qabs _ hσ.1 hσ.2).trans r11
  · intro σ hσ
    rw [defect2_eval 2]
    exact (abs_le_qabs _ hσ.1 hσ.2).trans r12

/-- On a checked cell the clamped flow stays strictly inside the clamps. -/
theorem cell_inside {T : ℚ} (c : Cell) (hok : cellOK 2 T c = true) (hbox : boxOK c = true)
    {θ φ : ℝ → ℝ}
    (hc : ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h),
      |θ t - evalQ c.pt (t - c.t0)| ≤ c.B ∧ |φ t - evalQ c.pp (t - c.t0)| ≤ c.B) :
    ∀ t ∈ Icc (c.t0 : ℝ) (c.t0 + c.h), |θ t| ≤ 1 ∧ |φ t| ≤ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, k9, k10, -, -, -, k14⟩ : CellProp 2 T c := of_decide_eq_true hok
  obtain ⟨b1, b2, b3⟩ := of_decide_eq_true hbox
  have r14 : ((c.B : ℚ) : ℝ) < ((1 / 100 : ℚ) : ℝ) := by exact_mod_cast k14
  have r9 : ((-(c.TH - 1 / 100) : ℚ) : ℝ) ≤ ((c.pt.headD 0 - c.h * qabs c.pt.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast k9
  have r10 : ((c.pt.headD 0 + c.h * qabs c.pt.tail c.h : ℚ) : ℝ) ≤ ((c.TH - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast k10
  have s1 : ((c.TH : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast b1
  have s2 : ((-(1 - 1 / 100) : ℚ) : ℝ) ≤ ((c.pp.headD 0 - c.h * qabs c.pp.tail c.h : ℚ) : ℝ) := by
    exact_mod_cast b2
  have s3 : ((c.pp.headD 0 + c.h * qabs c.pp.tail c.h : ℚ) : ℝ) ≤ ((1 - 1 / 100 : ℚ) : ℝ) := by
    exact_mod_cast b3
  push_cast at r9 r10 r14 s1 s2 s3
  intro t ht
  have hσ0 : 0 ≤ t - c.t0 := by linarith [ht.1]
  have hσ1 : t - c.t0 ≤ c.h := by linarith [ht.2]
  have l1 := lower_q c.pt (h := c.h) hσ0 hσ1
  have u1 := upper_q c.pt (h := c.h) hσ0 hσ1
  have l2 := lower_q c.pp (h := c.h) hσ0 hσ1
  have u2 := upper_q c.pp (h := c.h) hσ0 hσ1
  push_cast at l1 u1 l2 u2
  have e1 := abs_le.1 (hc t ht).1
  have e2 := abs_le.1 (hc t ht).2
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- A chain of clamped-flow cells (cell check, box check, links), ending in the input box of `d`. -/
def chainC (T : ℚ) (d : Cell) : List Cell → Bool
  | [] => false
  | [c] => cellOK 2 T c && boxOK c && linkOK c d
  | c :: e :: l => cellOK 2 T c && boxOK c && linkOK c e && chainC T d (e :: l)

/-- The cells of a checked chain advance in time up to `d`. -/
theorem le_of_chainC {T : ℚ} (d : Cell) :
    ∀ (c : Cell) (l : List Cell), chainC T d (c :: l) = true → (c.t0 : ℝ) ≤ d.t0 := by
  intro c l
  induction l generalizing c with
  | nil =>
    intro hok
    simp only [chainC, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, -⟩, kl⟩ := hok
    obtain ⟨ke, -, -⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
    linarith
  | cons e l ih =>
    intro hok
    simp only [chainC, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨k1, -⟩, kl⟩, krest⟩ := hok
    obtain ⟨ke, -, -⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (e.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
    have := ih e krest
    linarith

/-- A chain of clamped-flow cells: the flow stays inside the clamps from the first cell's start to
the start of `d`, and enters the input box of `d`. -/
theorem chainC_gen {T : ℚ} (d : Cell) :
    ∀ (l : List Cell) (c : Cell), chainC T d (c :: l) = true →
    ∀ {θ φ : ℝ → ℝ} {s : Set ℝ},
    (∀ t ∈ Icc (c.t0 : ℝ) d.t0, HasDerivWithinAt θ (cl 1 (φ t)) s t) →
    (∀ t ∈ Icc (c.t0 : ℝ) d.t0, HasDerivWithinAt φ (-(2 / t * cl 1 (φ t)) - cl 1 (θ t) ^ 2) s t) →
    Icc (c.t0 : ℝ) d.t0 ⊆ s →
    |θ c.t0 - ((c.pt.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    |φ c.t0 - ((c.pp.headD 0 : ℚ) : ℝ)| ≤ c.δ →
    (c.t0 : ℝ) ≤ d.t0 ∧ (∀ t ∈ Icc (c.t0 : ℝ) d.t0, |θ t| ≤ 1 ∧ |φ t| ≤ 1) ∧
    |θ d.t0 - ((d.pt.headD 0 : ℚ) : ℝ)| ≤ d.δ ∧ |φ d.t0 - ((d.pp.headD 0 : ℚ) : ℝ)| ≤ d.δ := by
  intro l
  induction l with
  | nil =>
    intro c hok θ φ s hθ hφ hs h0 h0'
    simp only [chainC, Bool.and_eq_true] at hok
    obtain ⟨⟨k1, kb⟩, kl⟩ := hok
    obtain ⟨ke, kθ, kφ⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (d.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
    have hsub : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ s := by rw [he]; exact hs
    have hc := cell_qC c k1 kb (θ := θ) (φ := φ)
      (fun t ht => (hθ t (by rw [← he]; exact ht)).mono hsub)
      (fun t ht => (hφ t (by rw [← he]; exact ht)).mono hsub) h0 h0'
    have hin := cell_inside c k1 kb hc
    have kθ' : |((qeval c.pt c.h : ℚ) : ℝ) - ((d.pt.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kθ
    have kφ' : |((qeval c.pp c.h : ℚ) : ℝ) - ((d.pp.headD 0 : ℚ) : ℝ)| + c.B ≤ d.δ := by
      exact_mod_cast kφ
    have e1 := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    have e2 := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).2
    rw [add_sub_cancel_left, ← qeval_cast, he] at e1 e2
    refine ⟨by linarith, fun t ht => hin t (by rw [he]; exact ht), abs_link e1 kθ', abs_link e2 kφ'⟩
  | cons e l ih =>
    intro c hok θ φ s hθ hφ hs h0 h0'
    simp only [chainC, Bool.and_eq_true] at hok
    obtain ⟨⟨⟨k1, kb⟩, kl⟩, krest⟩ := hok
    obtain ⟨ke, kθ, kφ⟩ := of_decide_eq_true kl
    have he : ((c.t0 + c.h : ℚ) : ℝ) = (e.t0 : ℝ) := by exact_mod_cast ke
    push_cast at he
    have hh : (0 : ℝ) < c.h := by exact_mod_cast (cellOK_basic c k1).2.2
    -- the rest of the chain starts at e.t0 and ends at d.t0 ≥ e.t0
    have hed : (e.t0 : ℝ) ≤ d.t0 := by
      by_contra hlt
      push Not at hlt
      -- use the tail chain's first conclusion is not yet available; derive from the data instead
      exact absurd hlt (not_lt.2 (le_of_chainC d e l krest))
    have hsub : Icc (c.t0 : ℝ) (c.t0 + c.h) ⊆ Icc (c.t0 : ℝ) d.t0 :=
      Icc_subset_Icc le_rfl (by rw [he]; exact hed)
    have hc := cell_qC c k1 kb (θ := θ) (φ := φ)
      (fun t ht => (hθ t (hsub ht)).mono (hsub.trans hs))
      (fun t ht => (hφ t (hsub ht)).mono (hsub.trans hs)) h0 h0'
    have hin := cell_inside c k1 kb hc
    have kθ' : |((qeval c.pt c.h : ℚ) : ℝ) - ((e.pt.headD 0 : ℚ) : ℝ)| + c.B ≤ e.δ := by
      exact_mod_cast kθ
    have kφ' : |((qeval c.pp c.h : ℚ) : ℝ) - ((e.pp.headD 0 : ℚ) : ℝ)| + c.B ≤ e.δ := by
      exact_mod_cast kφ
    have e1 := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).1
    have e2 := (hc (c.t0 + c.h) ⟨by linarith, le_rfl⟩).2
    rw [add_sub_cancel_left, ← qeval_cast, he] at e1 e2
    have hce : (c.t0 : ℝ) ≤ e.t0 := by linarith
    obtain ⟨-, hin2, hd1, hd2⟩ := ih e krest (θ := θ) (φ := φ) (s := s)
      (fun t ht => hθ t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hφ t ⟨by linarith [ht.1], ht.2⟩)
      ((Icc_subset_Icc hce le_rfl).trans hs)
      (abs_link e1 kθ') (abs_link e2 kφ')
    refine ⟨by linarith, fun t ht => ?_, hd1, hd2⟩
    rcases le_or_gt t e.t0 with h1 | h1
    · exact hin t ⟨ht.1, by rw [he]; exact h1⟩
    · exact hin2 t ⟨h1.le, ht.2⟩

end Work.Math.LE2ExistsCell
