import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.Townes.TExLeft
import Checked.Townes.TExFlow
import Checked.Townes.TExLimit
/-! Townes ground state, `TExAssemble`: the shooting argument: open exclusive events and the supremum of the undershoot central values. Promoted from `Work/Townes/TExAssemble.lean`. -/

namespace Checked.Townes.TExAssemble
open Set Filter Topology

/-- Gluing a left piece on [0, 1/5] and a right piece on [1/5, T]. -/
theorem glue {fL fR : ℝ → ℝ} {d T x : ℝ} (heq : fL (1 / 5) = fR (1 / 5))
    (hx : x ∈ Icc (0 : ℝ) T)
    (hL : x ≤ 1 / 5 → HasDerivWithinAt fL d (Icc 0 (1 / 5)) x)
    (hR : 1 / 5 ≤ x → HasDerivWithinAt fR d (Icc (1 / 5) T) x) :
    HasDerivWithinAt (fun t => if t ≤ 1 / 5 then fL t else fR t) d (Icc 0 T) x := by
  have eL : EqOn (fun t => if t ≤ 1 / 5 then fL t else fR t) fL (Icc 0 (1 / 5)) :=
    fun t ht => by simp only [if_pos ht.2]
  have eR : EqOn (fun t => if t ≤ 1 / 5 then fL t else fR t) fR (Icc (1 / 5) T) := by
    intro t ht
    rcases ht.1.lt_or_eq with h | h
    · simp only [if_neg (not_le.2 h)]
    · subst h; simp only [le_refl, if_true, heq]
  rcases lt_trichotomy x (1 / 5) with h | h | h
  · have h1 := (hL h.le).congr eL (eL ⟨hx.1, h.le⟩)
    refine h1.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Iio (1 / 5), isOpen_Iio, h, fun t ht => ⟨ht.2.1, ht.1.le⟩⟩
  · have hT : (1 / 5 : ℝ) ≤ T := by rw [← h]; exact hx.2
    have h1 := (hL h.le).congr eL (eL ⟨hx.1, h.le⟩)
    have h2 := (hR h.ge).congr eR (eR ⟨h.ge, hx.2⟩)
    have := h1.union h2
    rwa [Icc_union_Icc_eq_Icc (by norm_num) hT] at this
  · have h2 := (hR h.le).congr eR (eR ⟨h.le, hx.2⟩)
    refine h2.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Ioi (1 / 5), isOpen_Ioi, h, fun t ht => ⟨ht.1.le, ht.2.2⟩⟩

theorem cast_le_cast {n m : ℕ} (h : n ≤ m) : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
  have := (Nat.cast_le (α := ℝ)).2 h; linarith

theorem fifth_lt (n : ℕ) : (1 / 5 : ℝ) < (n : ℝ) + 1 := by
  have := n.cast_nonneg (α := ℝ); linarith

theorem flow (n : ℕ) : ∃ α : ℝ × ℝ → ℝ → ℝ × ℝ, ∃ L : ℝ,
    (∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) 3, α p (1 / 5) = p ∧
      ∀ t ∈ Icc (1 / 5 : ℝ) ((n : ℝ) + 1),
        HasDerivWithinAt (α p) (TExFlow.F t (α p t)) (Icc (1 / 5) ((n : ℝ) + 1)) t) ∧
    ∀ t ∈ Icc (1 / 5 : ℝ) ((n : ℝ) + 1), ∀ p ∈ Metric.closedBall (0 : ℝ × ℝ) 3,
      ∀ q ∈ Metric.closedBall (0 : ℝ × ℝ) 3, dist (α p t) (α q t) ≤ L * dist p q := by
  obtain ⟨α, h1, L, h2⟩ := TExFlow.exists_flow ((n : ℝ) + 1) (fifth_lt n)
  exact ⟨α, L, h1, h2⟩

/-- An event that holds at `c` on a compact time window holds nearby, given uniform Lipschitz
dependence on the parameter: positivity version. -/
theorem pos_near {f : ℝ → ℝ → ℝ} {a b c M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hcont : ContinuousOn (f c) (Icc a b)) (hpos : ∀ s ∈ Icc a b, 0 < f c s) :
    ∃ m > 0, ∀ c', (∀ s ∈ Icc a b, |f c s - f c' s| ≤ M * |c - c'|) →
      |c' - c| < m / (M + 1) → ∀ s ∈ Icc a b, 0 < f c' s := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hcont
  refine ⟨f c s₀, hpos s₀ hs₀, fun c' hlip hc' s hs => ?_⟩
  have h1 := hlip s hs
  have h2 : f c s₀ ≤ f c s := hmin hs
  have hm := hpos s₀ hs₀
  have h3 : M * |c - c'| < f c s₀ := by
    rw [abs_sub_comm]
    have hM1 : 0 < M + 1 := by linarith
    have : |c' - c| * (M + 1) < f c s₀ := (lt_div_iff₀ hM1).1 hc'
    nlinarith [abs_nonneg (c' - c)]
  have := (abs_le.1 h1).2
  linarith

theorem core
    (hU : ∀ (S : ℝ), 68 / 5 ≤ S → ∀ (θ φ : ℝ → ℝ),
      (∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r) →
      ContinuousWithinAt φ (Icc 0 S) 0 →
      (∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r) →
      θ 0 = 2.2062008646 → ∃ r ∈ Ioc (0 : ℝ) (68 / 5), 0 < φ r ∧ ∀ s ∈ Icc 0 r, 0 < θ s)
    (hO : ∀ (S : ℝ), 68 / 5 ≤ S → ∀ (θ φ : ℝ → ℝ),
      (∀ r ∈ Icc (0 : ℝ) S, HasDerivWithinAt θ (φ r) (Icc 0 S) r) →
      ContinuousWithinAt φ (Icc 0 S) 0 →
      (∀ r ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) (Icc 0 S) r) →
      θ 0 = 2.2062008647 → ∃ r ∈ Ioc (0 : ℝ) (68 / 5), θ r < 0 ∧ ∀ s ∈ Ioc 0 r, φ s < 0) :
    ∃ c ∈ Ioo (2.2062008646 : ℝ) 2.2062008647, ∃ θ φ : ℝ → ℝ,
      θ 0 = c ∧ φ 0 = 0 ∧
      (∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θ (φ r) (Ici 0) r) ∧
      ContinuousWithinAt φ (Ici 0) 0 ∧
      (∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (-(1 / r * φ r) + θ r - θ r ^ 3) r) ∧
      (∀ r ∈ Ici (0 : ℝ), 0 < θ r) ∧ (∀ r ∈ Ioi (0 : ℝ), φ r < 0) ∧
      Tendsto θ atTop (𝓝 0) := by
  obtain ⟨Θ, Φ, hL, K, hK⟩ := TExLeft.left
  choose α L hα hlip using flow
  -- the initial state at r = 1/5
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ → ℝ × ℝ, p = fun c => (Θ c (1 / 5), Φ c (1 / 5)) := ⟨_, rfl⟩
  have m15 : (1 / 5 : ℝ) ∈ Icc (0 : ℝ) (1 / 5) := ⟨by norm_num, le_rfl⟩
  have hp1 : ∀ c ∈ Icc (2.2 : ℝ) 2.21, |(p c).1| ≤ 5 / 2 := by
    intro c hc
    have := ((hL c hc).2.2.2.2.2.1 _ m15)
    rw [hpdef, abs_le]; constructor <;> linarith [this.1, this.2]
  have hp2 : ∀ c ∈ Icc (2.2 : ℝ) 2.21, |(p c).2| ≤ 3 := by
    intro c hc; rw [hpdef]; exact (hL c hc).2.2.2.2.2.2.2 _ m15
  have hpball : ∀ c ∈ Icc (2.2 : ℝ) 2.21, p c ∈ Metric.closedBall (0 : ℝ × ℝ) 3 := by
    intro c hc
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le ((hp1 c hc).trans (by norm_num)) (hp2 c hc)
  -- the glued pair on [0, n + 1]
  obtain ⟨th, hth⟩ : ∃ th : ℕ → ℝ → ℝ → ℝ,
      th = fun n c t => if t ≤ 1 / 5 then Θ c t else (α n (p c) t).1 := ⟨_, rfl⟩
  obtain ⟨ph, hph⟩ : ∃ ph : ℕ → ℝ → ℝ → ℝ,
      ph = fun n c t => if t ≤ 1 / 5 then Φ c t else (α n (p c) t).2 := ⟨_, rfl⟩
  have thL : ∀ (n : ℕ) (c t : ℝ), t ≤ 1 / 5 → th n c t = Θ c t := by
    intro n c t ht; rw [hth]; simp only [if_pos ht]
  have phL : ∀ (n : ℕ) (c t : ℝ), t ≤ 1 / 5 → ph n c t = Φ c t := by
    intro n c t ht; rw [hph]; simp only [if_pos ht]
  have thR : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t, 1 / 5 ≤ t → th n c t = (α n (p c) t).1 := by
    intro n c hc t ht
    rcases ht.lt_or_eq with h | h
    · rw [hth]; simp only [if_neg (not_le.2 h)]
    · subst h; rw [thL n c _ le_rfl, (hα n (p c) (hpball c hc)).1, hpdef]
  have phR : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t, 1 / 5 ≤ t → ph n c t = (α n (p c) t).2 := by
    intro n c hc t ht
    rcases ht.lt_or_eq with h | h
    · rw [hph]; simp only [if_neg (not_le.2 h)]
    · subst h; rw [phL n c _ le_rfl, (hα n (p c) (hpball c hc)).1, hpdef]
  have thF : ∀ (n : ℕ) (c : ℝ), th n c = fun t => if t ≤ 1 / 5 then Θ c t else (α n (p c) t).1 := by
    intro n c; rw [hth]
  have phF : ∀ (n : ℕ) (c : ℝ), ph n c = fun t => if t ≤ 1 / 5 then Φ c t else (α n (p c) t).2 := by
    intro n c; rw [hph]
  -- the clamps are inactive along the flow
  have hbd : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t ∈ Icc (1 / 5 : ℝ) ((n : ℝ) + 1),
      |(α n (p c) t).1| < 3 ∧ |(α n (p c) t).2| < 5 := by
    intro n c hc
    have h0 := (hα n (p c) (hpball c hc)).1
    exact TExFlow.bounds (α n (p c)) (hα n (p c) (hpball c hc)).2
      (by rw [h0]; exact hp1 c hc) (by rw [h0]; exact hp2 c hc)
  have hderR : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t ∈ Icc (1 / 5 : ℝ) ((n : ℝ) + 1),
      HasDerivWithinAt (fun r => (α n (p c) r).1) (α n (p c) t).2
        (Icc (1 / 5) ((n : ℝ) + 1)) t ∧
      HasDerivWithinAt (fun r => (α n (p c) r).2)
        (-(1 / t * (α n (p c) t).2) + (α n (p c) t).1 - (α n (p c) t).1 ^ 3)
        (Icc (1 / 5) ((n : ℝ) + 1)) t := by
    intro n c hc t ht
    have hd := (hα n (p c) (hpball c hc)).2 t ht
    have hb := hbd n c hc t ht
    rw [TExFlow.F_eq ht.1 hb.1 hb.2] at hd
    exact ⟨TExFlow.fst_derivW hd, TExFlow.snd_derivW hd⟩
  -- the glued pair solves the equation on [0, n + 1]
  have dθ : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      HasDerivWithinAt (th n c) (ph n c t) (Icc 0 ((n : ℝ) + 1)) t := by
    intro n c hc t ht
    rw [thF n c]
    refine glue (by rw [(hα n (p c) (hpball c hc)).1, hpdef]) ht (fun h => ?_) (fun h => ?_)
    · rw [phL n c t h]; exact (hL c hc).2.2.1 t ⟨ht.1, h⟩
    · rw [phR n c hc t h]; exact (hderR n c hc t ⟨h, ht.2⟩).1
  have dφ : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t ∈ Ioc (0 : ℝ) ((n : ℝ) + 1),
      HasDerivWithinAt (ph n c) (-(1 / t * ph n c t) + th n c t - th n c t ^ 3)
        (Icc 0 ((n : ℝ) + 1)) t := by
    intro n c hc t ht
    nth_rewrite 1 [phF n c]
    refine glue (by rw [(hα n (p c) (hpball c hc)).1, hpdef]) ⟨ht.1.le, ht.2⟩
      (fun h => ?_) (fun h => ?_)
    · rw [phL n c t h, thL n c t h]; exact (hL c hc).2.2.2.2.1 t ⟨ht.1, h⟩
    · rw [phR n c hc t h, thR n c hc t h]; exact (hderR n c hc t ⟨h, ht.2⟩).2
  have cφ : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ContinuousWithinAt (ph n c) (Icc 0 ((n : ℝ) + 1)) 0 := by
    intro n c hc
    have h1 : ContinuousWithinAt (Φ c) (Icc 0 (1 / 5)) 0 :=
      (hL c hc).2.2.2.1 0 ⟨le_rfl, by norm_num⟩
    have h2 : ContinuousWithinAt (ph n c) (Icc 0 (1 / 5)) 0 :=
      h1.congr (fun t ht => phL n c t ht.2) (phL n c 0 (by norm_num))
    refine h2.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    exact ⟨Iio (1 / 5), isOpen_Iio, by norm_num, fun t ht => ⟨ht.2.1, ht.1.le⟩⟩
  have th0 : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, th n c 0 = c := by
    intro n c hc; rw [thL n c 0 (by norm_num)]; exact (hL c hc).1
  have ph0 : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ph n c 0 = 0 := by
    intro n c hc; rw [phL n c 0 (by norm_num)]; exact (hL c hc).2.1
  have thlow : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t ∈ Icc (0 : ℝ) (1 / 5), 3 / 2 ≤ th n c t := by
    intro n c hc t ht; rw [thL n c t ht.2]; exact ((hL c hc).2.2.2.2.2.1 t ht).1
  have phneg : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t ∈ Ioc (0 : ℝ) (1 / 5), ph n c t < 0 := by
    intro n c hc t ht; rw [phL n c t ht.2]; exact (hL c hc).2.2.2.2.2.2.1 t ht
  -- agreement across horizons
  have agree : ∀ n m : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t, t ∈ Icc 0 ((n : ℝ) + 1) →
      t ∈ Icc 0 ((m : ℝ) + 1) → th n c t = th m c t ∧ ph n c t = ph m c t := by
    intro n m c hc t htn htm
    rcases le_or_gt t (1 / 5) with h | h
    · rw [thL n c t h, thL m c t h, phL n c t h, phL m c t h]; exact ⟨rfl, rfl⟩
    have key : α n (p c) t = α m (p c) t := by
      rcases le_total n m with hnm | hnm
      · exact TExFlow.consistent (cast_le_cast hnm) _ _
          (by rw [(hα n (p c) (hpball c hc)).1, (hα m (p c) (hpball c hc)).1])
          (hα n (p c) (hpball c hc)).2 (hα m (p c) (hpball c hc)).2 ⟨h.le, htn.2⟩
      · exact (TExFlow.consistent (cast_le_cast hnm) _ _
          (by rw [(hα n (p c) (hpball c hc)).1, (hα m (p c) (hpball c hc)).1])
          (hα m (p c) (hpball c hc)).2 (hα n (p c) (hpball c hc)).2 ⟨h.le, htm.2⟩).symm
    rw [thR n c hc t h.le, thR m c hc t h.le, phR n c hc t h.le, phR m c hc t h.le, key]
    exact ⟨rfl, rfl⟩
  -- Lipschitz dependence on c
  have lip : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ c' ∈ Icc (2.2 : ℝ) 2.21,
      ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      |th n c t - th n c' t| ≤ (|K| + |L n| * |K|) * |c - c'| ∧
      |ph n c t - ph n c' t| ≤ (|K| + |L n| * |K|) * |c - c'| := by
    intro n c hc c' hc' t ht
    have hKc : 0 ≤ |L n| * |K| * |c - c'| := by positivity
    rcases le_or_gt t (1 / 5) with h | h
    · rw [thL n c t h, thL n c' t h, phL n c t h, phL n c' t h]
      obtain ⟨h1, h2⟩ := hK c hc c' hc' t ⟨ht.1, h⟩
      have hK' : K * |c - c'| ≤ |K| * |c - c'| :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
      have e : (|K| + |L n| * |K|) * |c - c'| = |K| * |c - c'| + |L n| * |K| * |c - c'| := by
        ring
      rw [e]
      exact ⟨by linarith, by linarith⟩
    · rw [thR n c hc t h.le, thR n c' hc' t h.le, phR n c hc t h.le, phR n c' hc' t h.le]
      have hd := hlip n t ⟨h.le, ht.2⟩ (p c) (hpball c hc) (p c') (hpball c' hc')
      have hpd : dist (p c) (p c') ≤ |K| * |c - c'| := by
        obtain ⟨h1, h2⟩ := hK c hc c' hc' (1 / 5) m15
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hpdef]
        have hK' : K * |c - c'| ≤ |K| * |c - c'| :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
        exact max_le (h1.trans hK') (h2.trans hK')
      have hd2 : dist (α n (p c) t) (α n (p c') t) ≤ |L n| * (|K| * |c - c'|) := by
        refine hd.trans ?_
        calc L n * dist (p c) (p c') ≤ |L n| * dist (p c) (p c') :=
              mul_le_mul_of_nonneg_right (le_abs_self _) dist_nonneg
          _ ≤ |L n| * (|K| * |c - c'|) := mul_le_mul_of_nonneg_left hpd (abs_nonneg _)
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hd2
      have hK0 : 0 ≤ |K| * |c - c'| := by positivity
      have e : (|K| + |L n| * |K|) * |c - c'| = |K| * |c - c'| + |L n| * (|K| * |c - c'|) := by
        ring
      have m1 : |(α n (p c) t).1 - (α n (p c') t).1| ≤
          max |(α n (p c) t).1 - (α n (p c') t).1| |(α n (p c) t).2 - (α n (p c') t).2| :=
        le_max_left _ _
      have m2 : |(α n (p c) t).2 - (α n (p c') t).2| ≤
          max |(α n (p c) t).1 - (α n (p c') t).1| |(α n (p c) t).2 - (α n (p c') t).2| :=
        le_max_right _ _
      rw [e]
      exact ⟨by linarith, by linarith⟩
  -- no equilibrium is reached
  have equil : ∀ n : ℕ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ t ∈ Ioc (0 : ℝ) ((n : ℝ) + 1),
      ∀ e : ℝ × ℝ, (∀ s, TExFlow.F s e = 0) → e.1 < 3 / 2 →
      th n c t = e.1 → ph n c t = e.2 → False := by
    intro n c hc t ht e he he1 h1 h2
    rcases le_or_gt t (1 / 5) with h | h
    · have := thlow n c hc t ⟨ht.1.le, h⟩; linarith
    · rw [thR n c hc t h.le] at h1
      rw [phR n c hc t h.le] at h2
      have hb := TExFlow.equilibrium_backward e he ⟨h.le, ht.2⟩ (α n (p c))
        (hα n (p c) (hpball c hc)).2 (Prod.ext h1 h2)
      rw [(hα n (p c) (hpball c hc)).1] at hb
      have := thlow n c hc (1 / 5) m15
      rw [thL n c _ le_rfl] at this
      have h3 : (p c).1 = e.1 := by rw [hb]
      rw [hpdef] at h3
      simp only at h3
      linarith
  -- events
  let U : ℝ → Prop := fun c => ∃ n : ℕ, ∃ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
    0 < ph n c t ∧ ∀ s ∈ Icc 0 t, 0 < th n c s
  let O : ℝ → Prop := fun c => ∃ n : ℕ, ∃ t ∈ Icc (1 / 5 : ℝ) ((n : ℝ) + 1),
    th n c t < 0 ∧ ∀ s ∈ Icc (1 / 5) t, ph n c s < 0
  have hN : ∀ k N : ℕ, k ≤ N → ∀ t ∈ Icc (0 : ℝ) ((k : ℝ) + 1), t ∈ Icc (0 : ℝ) ((N : ℝ) + 1) :=
    fun k N hk t ht => ⟨ht.1, ht.2.trans (cast_le_cast hk)⟩
  have excl : ∀ c ∈ Icc (2.2 : ℝ) 2.21, U c → O c → False := by
    rintro c hc ⟨n, t₁, ht₁, h₁, h₁'⟩ ⟨m, t₂, ht₂, h₂, h₂'⟩
    set N := max n m
    have ht₁' := hN n N (le_max_left _ _) t₁ ht₁
    have ht₂0 : t₂ ∈ Icc (0 : ℝ) ((m : ℝ) + 1) := ⟨by linarith [ht₂.1], ht₂.2⟩
    have ht₂' := hN m N (le_max_right _ _) t₂ ht₂0
    rw [(agree n N c hc t₁ ht₁ ht₁').2] at h₁
    rw [(agree m N c hc t₂ ht₂0 ht₂').1] at h₂
    rcases le_or_gt t₁ t₂ with h | h
    · rcases le_or_gt (1 / 5) t₁ with h' | h'
      · have := h₂' t₁ ⟨h', h⟩
        rw [(agree m N c hc t₁ ⟨ht₁.1, h.trans ht₂.2⟩ (hN m N (le_max_right _ _) t₁
          ⟨ht₁.1, h.trans ht₂.2⟩)).2] at this
        linarith
      · rcases ht₁.1.lt_or_eq with h0 | h0
        · have := phneg N c hc t₁ ⟨h0, h'.le⟩; linarith
        · rw [← h0, ph0 N c hc] at h₁; linarith
    · have := h₁' t₂ ⟨ht₂0.1, h.le⟩
      rw [(agree n N c hc t₂ ⟨ht₂0.1, h.le.trans ht₁.2⟩ (hN n N (le_max_left _ _) t₂
        ⟨ht₂0.1, h.le.trans ht₁.2⟩)).1] at this
      linarith
  -- the constants
  have hP : ∀ c ∈ Icc (2.2062008646 : ℝ) 2.2062008647, c ∈ Icc (2.2 : ℝ) 2.21 :=
    fun c hc => ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hlo : (2.2062008646 : ℝ) ∈ Icc (2.2062008646 : ℝ) 2.2062008647 := ⟨le_rfl, by norm_num⟩
  have hhi : (2.2062008647 : ℝ) ∈ Icc (2.2062008646 : ℝ) 2.2062008647 := ⟨by norm_num, le_rfl⟩
  have hM0 : ∀ n : ℕ, 0 ≤ |K| + |L n| * |K| := fun n => by positivity
  -- openness
  have openU : ∀ c ∈ Icc (2.2062008646 : ℝ) 2.2062008647, U c →
      ∃ ε > 0, ∀ c' ∈ Icc (2.2062008646 : ℝ) 2.2062008647, |c' - c| < ε → U c' := by
    rintro c hc ⟨n, t, ht, h1, h2⟩
    have hcP := hP c hc
    have hcont : ContinuousOn (th n c) (Icc 0 t) := fun s hs =>
      ((dθ n c hcP s ⟨hs.1, hs.2.trans ht.2⟩).continuousWithinAt).mono
        (Icc_subset_Icc_right ht.2)
    obtain ⟨m, hm, hm'⟩ := pos_near (f := th n) (M := |K| + |L n| * |K|) ht.1 (hM0 n) hcont h2
    set M := |K| + |L n| * |K|
    refine ⟨min m (ph n c t) / (M + 1), div_pos (lt_min hm h1) (by linarith [hM0 n]),
      fun c' hc' hd => ⟨n, t, ht, ?_, ?_⟩⟩
    · have hl := (lip n c hcP c' (hP c' hc') t ht).2
      have hM1 : 0 < M + 1 := by linarith [hM0 n]
      have h3 : |c' - c| * (M + 1) < min m (ph n c t) := (lt_div_iff₀ hM1).1 hd
      have h4 : M * |c - c'| < ph n c t := by
        rw [abs_sub_comm]; nlinarith [abs_nonneg (c' - c), min_le_right m (ph n c t)]
      linarith [(abs_le.1 hl).2]
    · refine hm' c' (fun s hs => (lip n c hcP c' (hP c' hc') s ⟨hs.1, hs.2.trans ht.2⟩).1) ?_
      exact lt_of_lt_of_le hd (div_le_div_of_nonneg_right (min_le_left _ _) (by linarith [hM0 n]))
  have openO : ∀ c ∈ Icc (2.2062008646 : ℝ) 2.2062008647, O c →
      ∃ ε > 0, ∀ c' ∈ Icc (2.2062008646 : ℝ) 2.2062008647, |c' - c| < ε → O c' := by
    rintro c hc ⟨n, t, ht, h1, h2⟩
    have hcP := hP c hc
    have hcont : ContinuousOn (fun s => -ph n c s) (Icc (1 / 5) t) := fun s hs =>
      ((dφ n c hcP s ⟨by linarith [hs.1], hs.2.trans ht.2⟩).continuousWithinAt.neg).mono
        (fun r hr => ⟨by linarith [hr.1], hr.2.trans ht.2⟩)
    obtain ⟨m, hm, hm'⟩ := pos_near (f := fun c s => -ph n c s) (M := |K| + |L n| * |K|)
      ht.1 (hM0 n) hcont (fun s hs => by linarith [h2 s hs])
    set M := |K| + |L n| * |K|
    refine ⟨min m (-th n c t) / (M + 1), div_pos (lt_min hm (by linarith)) (by linarith [hM0 n]),
      fun c' hc' hd => ⟨n, t, ht, ?_, ?_⟩⟩
    · have hl := (lip n c hcP c' (hP c' hc') t ⟨by linarith [ht.1], ht.2⟩).1
      have hM1 : 0 < M + 1 := by linarith [hM0 n]
      have h3 : |c' - c| * (M + 1) < min m (-th n c t) := (lt_div_iff₀ hM1).1 hd
      have h4 : M * |c - c'| < -th n c t := by
        rw [abs_sub_comm]; nlinarith [abs_nonneg (c' - c), min_le_right m (-th n c t)]
      linarith [(abs_le.1 hl).1]
    · intro s hs
      have := hm' c' (fun s hs => by
          have := (lip n c hcP c' (hP c' hc') s ⟨by linarith [hs.1], hs.2.trans ht.2⟩).2
          rw [show -ph n c s - -ph n c' s = -(ph n c s - ph n c' s) by ring, abs_neg]
          exact this)
        (lt_of_lt_of_le hd (div_le_div_of_nonneg_right (min_le_left _ _) (by linarith [hM0 n])))
        s hs
      linarith
  -- the two ends of the bracket
  have h14 : (68 / 5 : ℝ) ≤ ((13 : ℕ) : ℝ) + 1 := by norm_num
  have Ulo : U 2.2062008646 := by
    have hc := hP _ hlo
    obtain ⟨r, hr, h1, h2⟩ := hU _ h14 (th 13 2.2062008646) (ph 13 2.2062008646)
      (dθ 13 _ hc) (cφ 13 _ hc) (dφ 13 _ hc) (th0 13 _ hc)
    exact ⟨13, r, ⟨hr.1.le, hr.2.trans h14⟩, h1, h2⟩
  have Ohi : O 2.2062008647 := by
    have hc := hP _ hhi
    obtain ⟨r, hr, h1, h2⟩ := hO _ h14 (th 13 2.2062008647) (ph 13 2.2062008647)
      (dθ 13 _ hc) (cφ 13 _ hc) (dφ 13 _ hc) (th0 13 _ hc)
    have hr5 : 1 / 5 ≤ r := by
      by_contra h
      push Not at h
      have := thlow 13 _ hc r ⟨hr.1.le, h.le⟩
      linarith
    exact ⟨13, r, ⟨hr5, hr.2.trans h14⟩, h1, fun s hs => h2 s ⟨by linarith [hs.1], hs.2⟩⟩
  -- the critical value
  let S : Set ℝ := {c | c ∈ Icc (2.2062008646 : ℝ) 2.2062008647 ∧ U c}
  have hne : S.Nonempty := ⟨_, hlo, Ulo⟩
  have hbdd : BddAbove S := ⟨2.2062008647, fun s hs => hs.1.2⟩
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀, c₀ = sSup S := ⟨_, rfl⟩
  have hc₀lo : (2.2062008646 : ℝ) < c₀ := by
    obtain ⟨ε, hε, hε'⟩ := openU _ hlo Ulo
    have hpos : 0 < min (ε / 2) ((2.2062008647 : ℝ) - 2.2062008646) :=
      lt_min (by linarith) (by norm_num)
    have hmem : (2.2062008646 : ℝ) + min (ε / 2) ((2.2062008647 : ℝ) - 2.2062008646) ∈
        Icc (2.2062008646 : ℝ) 2.2062008647 :=
      ⟨by linarith, by linarith [min_le_right (ε / 2) ((2.2062008647 : ℝ) - 2.2062008646)]⟩
    have hU' := hε' _ hmem (by
      rw [add_sub_cancel_left, abs_of_pos hpos]; linarith [min_le_left (ε / 2) ((2.2062008647 : ℝ) - 2.2062008646)])
    have := le_csSup hbdd (show _ ∈ S from ⟨hmem, hU'⟩)
    rw [← hc₀def] at this
    linarith
  have hc₀hi : c₀ < 2.2062008647 := by
    obtain ⟨ε, hε, hε'⟩ := openO _ hhi Ohi
    have hle : c₀ ≤ 2.2062008647 - ε := by
      rw [hc₀def]
      refine csSup_le hne (fun s hs => ?_)
      by_contra h
      push Not at h
      exact excl s (hP s hs.1) hs.2 (hε' s hs.1 (by
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hs.1.2])]; linarith))
    linarith
  have hc₀ : c₀ ∈ Icc (2.2062008646 : ℝ) 2.2062008647 := ⟨hc₀lo.le, hc₀hi.le⟩
  have hc₀P := hP c₀ hc₀
  have notU : ¬ U c₀ := by
    intro hU0
    obtain ⟨ε, hε, hε'⟩ := openU c₀ hc₀ hU0
    have hpos : 0 < min (ε / 2) ((2.2062008647 : ℝ) - c₀) := lt_min (by linarith) (by linarith)
    have hmem : c₀ + min (ε / 2) ((2.2062008647 : ℝ) - c₀) ∈ Icc (2.2062008646 : ℝ) 2.2062008647 :=
      ⟨by linarith, by linarith [min_le_right (ε / 2) ((2.2062008647 : ℝ) - c₀)]⟩
    have hU' := hε' _ hmem (by
      rw [add_sub_cancel_left, abs_of_pos hpos]; linarith [min_le_left (ε / 2) ((2.2062008647 : ℝ) - c₀)])
    have := le_csSup hbdd (show _ ∈ S from ⟨hmem, hU'⟩)
    rw [← hc₀def] at this
    linarith
  have notO : ¬ O c₀ := by
    intro hO0
    obtain ⟨ε, hε, hε'⟩ := openO c₀ hc₀ hO0
    obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup hne
      (show c₀ - ε < sSup S by rw [← hc₀def]; linarith)
    have hle : s ≤ c₀ := by rw [hc₀def]; exact le_csSup hbdd hsS
    exact excl s (hP s hsS.1) hsS.2 (hε' s hsS.1 (by rw [abs_lt]; constructor <;> linarith))
  -- the global solution at c₀
  have hmemidx : ∀ t : ℝ, 0 ≤ t → t ∈ Icc (0 : ℝ) (((⌈t⌉₊ : ℕ) : ℝ) + 1) :=
    fun t ht => ⟨ht, by linarith [Nat.le_ceil t]⟩
  obtain ⟨θg, hθg⟩ : ∃ θg : ℝ → ℝ, θg = fun t => th ⌈t⌉₊ c₀ t := ⟨_, rfl⟩
  obtain ⟨φg, hφg⟩ : ∃ φg : ℝ → ℝ, φg = fun t => ph ⌈t⌉₊ c₀ t := ⟨_, rfl⟩
  have geq : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1), θg t = th n c₀ t ∧ φg t = ph n c₀ t := by
    intro n t ht
    have := agree ⌈t⌉₊ n c₀ hc₀P t (hmemidx t ht.1) ht
    rw [hθg, hφg]
    exact this
  have hnbr : ∀ t : ℝ, 0 ≤ t → t < (((⌈t⌉₊ + 1 : ℕ) : ℝ) + 1) := by
    intro t ht; push_cast; linarith [Nat.le_ceil t]
  have gθ : ∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt θg (φg r) (Ici 0) r := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := hr
    set n := ⌈r⌉₊ + 1
    have hrn := hnbr r hr0
    have hrm : r ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨hr0, hrn.le⟩
    have hnhds : Icc 0 ((n : ℝ) + 1) ∈ 𝓝[Ici 0] r := by
      have := inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iic_mem_nhds hrn)
      rwa [Ici_inter_Iic] at this
    have heq : θg =ᶠ[𝓝[Ici 0] r] th n c₀ :=
      Filter.mem_of_superset hnhds (fun τ hτ => (geq n τ hτ).1)
    have h1 := ((dθ n c₀ hc₀P r hrm).mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq heq
      (geq n r hrm).1
    rwa [← (geq n r hrm).2] at h1
  have gφ : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt φg (-(1 / r * φg r) + θg r - θg r ^ 3) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    set n := ⌈r⌉₊ + 1
    have hrn := hnbr r hr0.le
    have hrm : r ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨hr0.le, hrn.le⟩
    have hnh : Icc 0 ((n : ℝ) + 1) ∈ 𝓝 r := Icc_mem_nhds hr0 hrn
    have heq : φg =ᶠ[𝓝 r] ph n c₀ := Filter.mem_of_superset hnh (fun τ hτ => (geq n τ hτ).2)
    have h1 := ((dφ n c₀ hc₀P r ⟨hr0, hrn.le⟩).hasDerivAt hnh).congr_of_eventuallyEq heq
    rwa [← (geq n r hrm).1, ← (geq n r hrm).2] at h1
  have gθ0 : θg 0 = c₀ := by rw [(geq 0 0 ⟨le_rfl, by norm_num⟩).1]; exact th0 0 c₀ hc₀P
  have gφ0 : φg 0 = 0 := by rw [(geq 0 0 ⟨le_rfl, by norm_num⟩).2]; exact ph0 0 c₀ hc₀P
  have gc : ContinuousWithinAt φg (Ici 0) 0 := by
    have hnhds : Icc (0 : ℝ) (((0 : ℕ) : ℝ) + 1) ∈ 𝓝[Ici 0] 0 := by
      have := inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iic_mem_nhds (show (0 : ℝ) < ((0 : ℕ) : ℝ) + 1
        by norm_num))
      rwa [Ici_inter_Iic] at this
    have h1 : ContinuousWithinAt φg (Icc 0 (((0 : ℕ) : ℝ) + 1)) 0 :=
      (cφ 0 c₀ hc₀P).congr (fun τ hτ => (geq 0 τ hτ).2) (geq 0 0 ⟨le_rfl, by norm_num⟩).2
    exact h1.mono_of_mem_nhdsWithin hnhds
  obtain ⟨hpos, hneg, hlim⟩ := TExLimit.limit θg φg gθ gφ
    (by rw [gθ0]; linarith [hc₀P.1])
    ⟨1 / 5, by norm_num, fun r hr => by
      rw [(geq 0 r ⟨hr.1.le, by linarith [hr.2]⟩).2]; exact phneg 0 c₀ hc₀P r hr⟩
    (fun r hr h1 h2 => equil ⌈r⌉₊ c₀ hc₀P r ⟨hr, (hmemidx r (le_of_lt hr)).2⟩ 0
      TExFlow.F_zero (by norm_num)
      (by rw [← (geq _ r (hmemidx r (le_of_lt hr))).1]; exact h1)
      (by rw [← (geq _ r (hmemidx r (le_of_lt hr))).2]; exact h2))
    (fun r hr h1 h2 => equil ⌈r⌉₊ c₀ hc₀P r ⟨hr, (hmemidx r (le_of_lt hr)).2⟩ (1, 0)
      TExFlow.F_one (by norm_num)
      (by rw [← (geq _ r (hmemidx r (le_of_lt hr))).1]; exact h1)
      (by rw [← (geq _ r (hmemidx r (le_of_lt hr))).2]; exact h2))
    (by
      rintro ⟨t, ht, h1, h2⟩
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      refine notU ⟨⌈t⌉₊, t, hmemidx t ht0, ?_, fun s hs => ?_⟩
      · rw [← (geq _ t (hmemidx t ht0)).2]; exact h1
      · rw [← (geq _ s ⟨hs.1, hs.2.trans (hmemidx t ht0).2⟩).1]; exact h2 s hs)
    (by
      rintro ⟨t, ht, h1, h2⟩
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      have ht5 : 1 / 5 ≤ t := by
        by_contra h
        push Not at h
        rw [(geq 0 t ⟨ht0, by linarith⟩).1] at h1
        linarith [thlow 0 c₀ hc₀P t ⟨ht0, h.le⟩]
      refine notO ⟨⌈t⌉₊, t, ⟨ht5, (hmemidx t ht0).2⟩, ?_, fun s hs => ?_⟩
      · rw [← (geq _ t (hmemidx t ht0)).1]; exact h1
      · have hs0 : s ∈ Icc (0 : ℝ) (((⌈t⌉₊ : ℕ) : ℝ) + 1) :=
          ⟨by linarith [hs.1], hs.2.trans (hmemidx t ht0).2⟩
        rw [← (geq _ s hs0).2]; exact h2 s ⟨by linarith [hs.1], hs.2⟩)
  exact ⟨c₀, ⟨hc₀lo, hc₀hi⟩, θg, φg, gθ0, gφ0, gθ, gc, gφ, hpos, hneg, hlim⟩

end Checked.Townes.TExAssemble
