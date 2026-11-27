import Work.Quantum.AngularCert
import Work.Quantum.RadialStart
/-!
# H₂⁺ route step 4 (iii), first piece: the radial Frobenius solution is positive on [1, 2] (run 2026-11-27T0828Z)

The first conjunct of `RegularUnique.OverIVP k₂ A`: RL(k₂, A, ξ − 1) > 0 for ξ ∈ [1, 2], for every A in the
angular bracket [a, b] of `AngularCert` (`aQ`, `bQ`). RL = ∑ cₙ uⁿ (u = ξ − 1) with cₙ = `FrobParam.fc` at
w₂ = 1, v = (4 − k + A, 4 − 2k, −k) (`RadialStart.RL`).

Method as `AngularCert`: the recurrence of `fc` carried on intervals (A ∈ [a, b], u in a piece of [0, 1]), with the
partial sum ∑_{n<N} cₙ uⁿ, outward-rounded; tail 3 · 12¹⁹ (2/3)ᴺ from the uniform bound `FrobParam.fc_geom`
(`tail_series_le`). [0, 1] in 8 pieces, N = 140 (emulation `runs/2026-11-27T0828Z/scripts/rl_interval.py`: RL ≥ 0.04).
`freeze_of_radial_flows`: the H₂⁺ freeze from the two regular flows past ξ = 2 (the rest of step 4 (iii)).
-/

namespace Work.Quantum.FrobCert
open Set Work.Quantum.AngularCert Work.Quantum.FrobParam Work.Quantum.RadialStart

/-- One step of the recurrence of `fc` (w₂ = 1, v₀ = 4 − k + A, v₁ = 4 − 2k, v₂ = −k) on intervals, k = kq exact. -/
def stepF (kq : ℚ) (AI U : Iv) (n : ℕ) (st : St) : St :=
  let t : Iv := ⟨-(((n : ℚ) + 2) * ((n : ℚ) + 3) + (4 - kq + AI.hi)),
    -(((n : ℚ) + 2) * ((n : ℚ) + 3) + (4 - kq + AI.lo))⟩
  let num := iadd (iadd (imul t st.b2) (imul ⟨-(4 - 2 * kq), -(4 - 2 * kq)⟩ st.b1)) (imul ⟨kq, kq⟩ st.b0)
  ⟨st.b1, st.b2, rnd (ismul (1 / (2 * ((n : ℚ) + 3) ^ 2)) num), st.gs,
    rnd (iadd st.ms (imul st.b0 st.pw)), rnd (imul st.pw U)⟩

/-- The start: c₀ = 1, c₁ = −v₀/2, c₂ = (−(2 + v₀) c₁ − v₁)/8. -/
def startF (kq : ℚ) (AI : Iv) : St :=
  let V0 : Iv := ⟨4 - kq + AI.lo, 4 - kq + AI.hi⟩
  let c1 := imul ⟨-1 / 2, -1 / 2⟩ V0
  ⟨⟨1, 1⟩, c1, ismul (1 / 8) (iadd (imul (ineg (iadd ⟨2, 2⟩ V0)) c1) ⟨-(4 - 2 * kq), -(4 - 2 * kq)⟩), ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨1, 1⟩⟩

def runF (kq : ℚ) (AI U : Iv) : ℕ → St
  | 0 => startF kq AI
  | n + 1 => stepF kq AI U n (runF kq AI U n)

/-- The coefficients at (k, A). -/
noncomputable def cf (k A : ℝ) : ℕ → ℝ := fc 1 (4 - k + A) (4 - 2 * k) (-k)

/-- Partial sums of RL. -/
noncomputable def SR (k A u : ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, cf k A j * u ^ j

def InvF (k A u : ℝ) (n : ℕ) (st : St) : Prop :=
  Iv.mem (cf k A n) st.b0 ∧ Iv.mem (cf k A (n + 1)) st.b1 ∧ Iv.mem (cf k A (n + 2)) st.b2 ∧
    Iv.mem (SR k A u n) st.ms ∧ Iv.mem (u ^ n) st.pw

theorem mem_pt (c : ℚ) : Iv.mem (c : ℝ) ⟨c, c⟩ := ⟨le_rfl, le_rfl⟩

theorem runF_sound (kq : ℚ) (AI U : Iv) {A u : ℝ} (hA : Iv.mem A AI) (hu : Iv.mem u U) :
    ∀ n, InvF kq A u n (runF kq AI U n) := by
  have hV0 : Iv.mem (4 - (kq : ℝ) + A) ⟨4 - kq + AI.lo, 4 - kq + AI.hi⟩ := by
    unfold Iv.mem at *; push_cast; constructor <;> linarith [hA.1, hA.2]
  intro n
  induction n with
  | zero =>
    have h1 : Iv.mem (cf kq A 1) (imul ⟨-1 / 2, -1 / 2⟩ ⟨4 - kq + AI.lo, 4 - kq + AI.hi⟩) := by
      have := mem_mul (mem_pt (-1 / 2)) hV0
      convert this using 1
      simp only [cf, fc]; push_cast; ring
    refine ⟨?_, h1, ?_, ?_, ?_⟩
    · simp [Iv.mem, cf, fc, runF, startF]
    · have h2 : Iv.mem (2 + (4 - (kq : ℝ) + A)) (iadd ⟨2, 2⟩ ⟨4 - kq + AI.lo, 4 - kq + AI.hi⟩) := by
        have := mem_add (mem_pt 2) hV0; simpa using this
      have := mem_smul (c := 1 / 8) (by norm_num)
        (mem_add (mem_mul (mem_neg h2) h1) (mem_pt (-(4 - 2 * kq))))
      simp only [runF, startF]
      convert this using 1
      simp only [cf, fc]; push_cast; ring
    · simp [Iv.mem, SR, runF, startF]
    · simp [Iv.mem, runF, startF]
  | succ n ih =>
    obtain ⟨i0, i1, i2, im, ip⟩ := ih
    refine ⟨i1, i2, ?_, ?_, ?_⟩
    · have ht : Iv.mem (-(((n : ℝ) + 2) * ((n : ℝ) + 3) + (4 - kq + A)))
          ⟨-(((n : ℚ) + 2) * ((n : ℚ) + 3) + (4 - kq + AI.hi)), -(((n : ℚ) + 2) * ((n : ℚ) + 3) + (4 - kq + AI.lo))⟩ := by
        unfold Iv.mem at *; push_cast; constructor <;> linarith [hA.1, hA.2]
      have hnum := mem_add (mem_add (mem_mul ht i2) (mem_mul (mem_pt (-(4 - 2 * kq))) i1)) (mem_mul (mem_pt kq) i0)
      have hpos : (0 : ℚ) ≤ 1 / (2 * ((n : ℚ) + 3) ^ 2) := by positivity
      have := mem_rnd (mem_smul hpos hnum)
      simp only [runF, stepF]
      convert this using 1
      rw [show n + 1 + 2 = n + 3 by ring]
      simp only [cf]
      rw [fc_succ3]
      push_cast; ring
    · have := mem_rnd (mem_add im (mem_mul i0 ip))
      simp only [runF, stepF]
      convert this using 1
      simp only [SR, Finset.sum_range_succ]
    · have := mem_rnd (mem_mul ip hu)
      simp only [runF, stepF]
      convert this using 1
      ring

/-- Tail of a power series with geometric coefficient bound C (2/3)ⁿ, for |x| ≤ 1. -/
theorem tail_series_le {c : ℕ → ℝ} {C x : ℝ} (hc : ∀ n, |c n| ≤ C * (2 / 3 : ℝ) ^ n) (hx : |x| ≤ 1) (N : ℕ) :
    |∑' n, c n * x ^ n - ∑ i ∈ Finset.range N, c i * x ^ i| ≤ 3 * C * (2 / 3 : ℝ) ^ N := by
  have hq : ‖(2 / 3 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
  have hT : HasSum (fun n : ℕ => C * (2 / 3 : ℝ) ^ (n + N)) (3 * C * (2 / 3 : ℝ) ^ N) := by
    have h := (hasSum_geometric_of_norm_lt_one hq).mul_left (C * (2 / 3 : ℝ) ^ N)
    convert h using 1
    · funext n; ring
    · norm_num; ring
  have hbd : ∀ n, |c n * x ^ n| ≤ C * (2 / 3 : ℝ) ^ n := fun n => by
    rw [abs_mul, abs_pow]
    calc |c n| * |x| ^ n ≤ C * (2 / 3 : ℝ) ^ n * 1 := by
          gcongr
          · exact le_trans (abs_nonneg _) (hc n)
          · exact hc n
          · exact pow_le_one₀ (abs_nonneg x) hx
      _ = _ := mul_one _
  have hs : Summable (fun n => c n * x ^ n) := by
    have : Summable (fun n : ℕ => C * (2 / 3 : ℝ) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
    exact Summable.of_norm_bounded this (fun n => by rw [Real.norm_eq_abs]; exact hbd n)
  rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hs' : Summable (fun n => c (n + N) * x ^ (n + N)) := (summable_nat_add_iff N).mpr hs
  calc |∑' n, c (n + N) * x ^ (n + N)| ≤ ∑' n, |c (n + N) * x ^ (n + N)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs'.norm
    _ ≤ ∑' n : ℕ, C * (2 / 3 : ℝ) ^ (n + N) := hs'.abs.tsum_le_tsum (fun n => hbd (n + N)) hT.summable
    _ = 3 * C * (2 / 3 : ℝ) ^ N := hT.tsum_eq

def tailFQ (N : ℕ) : ℚ := 3 * 12 ^ 19 * (2 / 3) ^ N

def checkRL (kq : ℚ) (AI U : Iv) (N : ℕ) : Bool := decide (0 < (runF kq AI U N).ms.lo - tailFQ N)

theorem RL_pos_of_check {kq : ℚ} {AI U : Iv} {N : ℕ} (h : checkRL kq AI U N = true) {A u : ℝ}
    (hA : Iv.mem A AI) (hu : Iv.mem u U) (hu1 : |u| ≤ 1) (hs : Small 1 (4 - kq + A) (4 - 2 * kq) (-kq)) :
    0 < RL kq A u := by
  have hm := (runF_sound kq AI U hA hu N).2.2.2.1
  have ht : |RL kq A u - SR kq A u N| ≤ 3 * CF * (2 / 3 : ℝ) ^ N := tail_series_le (fc_geom hs) hu1 N
  have hc : (0 : ℝ) < (((runF kq AI U N).ms.lo - tailFQ N : ℚ) : ℝ) := by exact_mod_cast (of_decide_eq_true h)
  have hCF : (3 * CF * (2 / 3 : ℝ) ^ N) = ((tailFQ N : ℚ) : ℝ) := by unfold CF tailFQ; push_cast; ring
  rw [hCF] at ht
  push_cast at hc
  linarith [hm.1, (abs_le.mp ht).1]

/-! The eight pieces of [0, 1] at k = k₂. -/

def k2Q : ℚ := 22052684289900 / 10 ^ 13
def ABr : Iv := ⟨aQ, bQ⟩
def Up (j : ℕ) : Iv := ⟨j / 8, (j + 1) / 8⟩

theorem check_rl_0 : checkRL k2Q ABr (Up 0) 140 = true := by decide +kernel
theorem check_rl_1 : checkRL k2Q ABr (Up 1) 140 = true := by decide +kernel
theorem check_rl_2 : checkRL k2Q ABr (Up 2) 140 = true := by decide +kernel
theorem check_rl_3 : checkRL k2Q ABr (Up 3) 140 = true := by decide +kernel
theorem check_rl_4 : checkRL k2Q ABr (Up 4) 140 = true := by decide +kernel
theorem check_rl_5 : checkRL k2Q ABr (Up 5) 140 = true := by decide +kernel
theorem check_rl_6 : checkRL k2Q ABr (Up 6) 140 = true := by decide +kernel
theorem check_rl_7 : checkRL k2Q ABr (Up 7) 140 = true := by decide +kernel

theorem check_rl (j : ℕ) (hj : j < 8) : checkRL k2Q ABr (Up j) 140 = true := by
  interval_cases j
  exacts [check_rl_0, check_rl_1, check_rl_2, check_rl_3, check_rl_4, check_rl_5, check_rl_6, check_rl_7]

/-- The first conjunct of `RegularUnique.OverIVP k₂ A` for every A of the bracket. -/
theorem RL_pos_k₂ : ∀ A ∈ Icc (aQ : ℝ) (bQ : ℝ), ∀ ξ ∈ Icc (1 : ℝ) 2,
    0 < RL H2PlusConditional.k₂ A (ξ - 1) := by
  intro A hA ξ hξ
  have hk : (H2PlusConditional.k₂ : ℝ) = ((k2Q : ℚ) : ℝ) := by
    unfold H2PlusConditional.k₂ k2Q; push_cast; ring
  rw [hk]
  obtain ⟨j, hj, h1, h2⟩ := exists_piece (lo := 0) (w := 1 / 8) (x := ξ - 1) (P := 8) (by norm_num) (by norm_num)
    (by linarith [hξ.1]) (by norm_num; linarith [hξ.2])
  have hA' : A ∈ Icc (0 : ℝ) 3 := ⟨le_trans (by unfold aQ; norm_num) hA.1, le_trans hA.2 (by unfold bQ; norm_num)⟩
  have hk' : ((k2Q : ℚ) : ℝ) ∈ Icc (0 : ℝ) 3 := by unfold k2Q; push_cast; constructor <;> norm_num
  refine RL_pos_of_check (check_rl j hj) (by unfold Iv.mem ABr; exact hA) ?_ ?_ (small_of hk' hA')
  · unfold Iv.mem Up; push_cast; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2]

/-- The H₂⁺ freeze from the two radial flows past ξ = 2 alone: `hunder` as in `RegularUnique.UnderIVP`, and the
regular IVP part of `RegularUnique.OverIVP` (its Frobenius part is `RL_pos_k₂`). -/
theorem freeze_of_radial_flows
    (hunder : ∀ A ∈ Icc (aQ : ℝ) (bQ : ℝ), RegularUnique.UnderIVP H2PlusConditional.k₁ A)
    (hflow : ∀ A ∈ Icc (aQ : ℝ) (bQ : ℝ), ∃ b, 5 / 2 ≤ b ∧ ∀ f : ℝ → ℝ × ℝ,
      f 2 = (RL H2PlusConditional.k₂ A 1, 3 * RLd H2PlusConditional.k₂ A 1) →
      (∀ t ∈ Icc (2 : ℝ) b, HasDerivWithinAt f (RadialGlobal.vf H2PlusConditional.k₂ A t (f t)) (Icc 2 b) t) →
      (∀ ξ ∈ Icc (2 : ℝ) b, 0 < (f ξ).1) ∧ 0 < (f b).2) :
    H2PlusBlindClosed.Freeze :=
  freeze_of_radial_events hunder (fun A hA => ⟨RL_pos_k₂ A hA, hflow A hA⟩)

end Work.Quantum.FrobCert
