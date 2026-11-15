import Mathlib
import Work.Math.BEState300
import Work.Math.BEFocus
import Work.Math.BE3Ext
import Checked.Math.BE3Main
import Checked.Math.BEHMain

/-! Bonnor–Ebert sphere, `BEAllMain`: the assembly behind `Work.Math.BonnorEbertAll.bonnor_ebert_all_extrema`
(run 2026-11-15T0028Z): the first five extrema from the certified chain (`BE3Ext`, a copy of `BE3Main` with two
more outputs), the state at radius 300000 (`BEState300`), and every later extremum from the analytic argument
near the focus of the homology field (`BEFocus.tail`), joined through u v³ = 4π m². -/

namespace Work.Math.BEAllMain
open Set Filter Topology
open Checked.Math.BEOCell (Nw)

/-- The pressure-confined mass. -/
noncomputable def Mf (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)

/-- Homology variable u. -/
noncomputable def Uf (w φ : ℝ → ℝ) (s : ℝ) : ℝ := s * Real.exp (w s) / -φ s

/-- Homology variable v. -/
noncomputable def Vf (w φ : ℝ → ℝ) (s : ℝ) : ℝ := -(s * φ s)

/-- u v³ = 4π m². -/
noncomputable def Pf (w φ : ℝ → ℝ) (s : ℝ) : ℝ := Uf w φ s * Vf w φ s ^ 3

/-- The sequence: five certified extrema, then the tail zeros. -/
def seq (a b c d e : ℝ) (ζ : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | k + 5 => ζ k

theorem seq_add5 (a b c d e : ℝ) (ζ : ℕ → ℝ) (k : ℕ) : seq a b c d e ζ (k + 5) = ζ k := rfl

/-- √(2/π) between two decimals. -/
theorem c_bounds : (0.7978 : ℝ) < Real.sqrt (2 / Real.pi) ∧ Real.sqrt (2 / Real.pi) < 0.8009 := by
  have pil := Real.pi_gt_d6
  have pih := Real.pi_lt_d6
  have hp : 0 < Real.pi := Real.pi_pos
  constructor
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ hp]; nlinarith
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ hp]; nlinarith

/-- 4π · (√(2/π))² = 8. -/
theorem c_sq : Real.sqrt (2 / Real.pi) ^ 2 * (4 * Real.pi) = 8 := by
  have hp : 0 < Real.pi := Real.pi_pos
  rw [Real.sq_sqrt (by positivity)]; field_simp; ring

/-- The mass below/above √(2/π) according to u v³ below/above 8. -/
theorem band {w φ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hp : φ s < 0) :
    (Pf w φ s < 8 → Mf w φ s < Real.sqrt (2 / Real.pi)) ∧
    (8 < Pf w φ s → Real.sqrt (2 / Real.pi) < Mf w φ s) := by
  obtain ⟨h1, h2⟩ := Checked.Math.BEHMain.mass_sq (w := w) hs hp
  have hc := c_sq
  have hc0 : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hpi : 0 < 4 * Real.pi := by positivity
  change Mf w φ s ^ 2 * (4 * Real.pi) = Pf w φ s at h1
  change 0 < Mf w φ s at h2
  constructor
  · intro h
    apply lt_of_pow_lt_pow_left₀ 2 hc0
    have : Mf w φ s ^ 2 * (4 * Real.pi) < Real.sqrt (2 / Real.pi) ^ 2 * (4 * Real.pi) := by linarith
    exact lt_of_mul_lt_mul_right this hpi.le
  · intro h
    apply lt_of_pow_lt_pow_left₀ 2 h2.le
    have : Real.sqrt (2 / Real.pi) ^ 2 * (4 * Real.pi) < Mf w φ s ^ 2 * (4 * Real.pi) := by linarith
    exact lt_of_mul_lt_mul_right this hpi.le

/-- Comparing masses through u v³ with a decimal bound on one side. -/
theorem P_lt_of_M {w φ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hp : φ s < 0) {c : ℝ} (hc : 0 ≤ c)
    (h : c ≤ Mf w φ s) : c ^ 2 * (4 * Real.pi) ≤ Pf w φ s := by
  obtain ⟨h1, -⟩ := Checked.Math.BEHMain.mass_sq (w := w) hs hp
  change Mf w φ s ^ 2 * (4 * Real.pi) = Pf w φ s at h1
  rw [← h1]
  have : c ^ 2 ≤ Mf w φ s ^ 2 := pow_le_pow_left₀ hc h 2
  have hpi : 0 < 4 * Real.pi := by positivity
  nlinarith

theorem P_le_of_M {w φ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hp : φ s < 0) {c : ℝ}
    (h : Mf w φ s ≤ c) : Pf w φ s ≤ c ^ 2 * (4 * Real.pi) := by
  obtain ⟨h1, h2⟩ := Checked.Math.BEHMain.mass_sq (w := w) hs hp
  change Mf w φ s ^ 2 * (4 * Real.pi) = Pf w φ s at h1
  change 0 < Mf w φ s at h2
  rw [← h1]
  have : Mf w φ s ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ h2.le h 2
  have hpi : 0 < 4 * Real.pi := by positivity
  nlinarith

/-- The mass as a square root of u v³. -/
theorem M_eq {w φ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hp : φ s < 0) :
    Mf w φ s = Real.sqrt (Pf w φ s / (4 * Real.pi)) := by
  obtain ⟨h1, h2⟩ := Checked.Math.BEHMain.mass_sq (w := w) hs hp
  change Mf w φ s ^ 2 * (4 * Real.pi) = Pf w φ s at h1
  change 0 < Mf w φ s at h2
  have hpi : 0 < 4 * Real.pi := by positivity
  rw [← h1, mul_div_assoc, div_self hpi.ne', mul_one, Real.sqrt_sq h2.le]

/-- Restriction of the half-line hypotheses to [0, S]. -/
theorem restrict {w φ : ℝ → ℝ} (S : ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s) :
    (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s) ∧
    ContinuousWithinAt φ (Icc 0 S) 0 ∧
    (∀ s ∈ Ioc (0 : ℝ) S, HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s) :=
  ⟨fun s hs => (hw s hs.1).mono Icc_subset_Ici_self, hφ0.mono Icc_subset_Ici_self,
    fun s hs => (hφ s hs.1).mono Icc_subset_Ici_self⟩

/-- Positive part of the tail bookkeeping: on each segment between consecutive zeros, u v³ is strictly
monotone, and the extremal values are ordered. -/
theorem P_mono_of_pos {P g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt P (P t * g t / t) t) (hP : ∀ t ∈ Icc a b, 0 < P t)
    (hg : ∀ t ∈ Ioo a b, 0 < g t) : StrictMonoOn P (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x (Ioo_subset_Icc_self hx)).deriv]
  have := hP x (Ioo_subset_Icc_self hx)
  have := hg x hx
  have : 0 < x := by linarith [hx.1]
  positivity

theorem P_anti_of_neg {P g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt P (P t * g t / t) t) (hP : ∀ t ∈ Icc a b, 0 < P t)
    (hg : ∀ t ∈ Ioo a b, g t < 0) : StrictAntiOn P (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x (Ioo_subset_Icc_self hx)).deriv]
  have h1 := hP x (Ioo_subset_Icc_self hx)
  have h2 := hg x hx
  have h3 : 0 < x := by linarith [hx.1]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 h2) h3

/-- Every point beyond ζ a lies in a segment [ζ i, ζ (i+1)] with i ≥ a, left-closed, right-open. -/
theorem locate {ζ : ℕ → ℝ} (hζ : StrictMono ζ) (hT : Tendsto ζ atTop atTop) (a : ℕ) {s : ℝ}
    (hs : ζ a ≤ s) : ∃ i, a ≤ i ∧ ζ i ≤ s ∧ s < ζ (i + 1) := by
  have hex : ∃ n, s < ζ n := (hT.eventually (eventually_gt_atTop s)).exists
  classical
  let n := Nat.find hex
  have hn : s < ζ n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    have : s < ζ 0 := by rw [← h0]; exact hn
    have : ζ 0 ≤ ζ a := hζ.monotone (Nat.zero_le a)
    linarith
  obtain ⟨i, hi⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hmin : ¬ s < ζ i := Nat.find_min hex (by omega)
  refine ⟨i, ?_, le_of_not_gt hmin, by rw [← hi]; exact hn⟩
  by_contra h
  push_neg at h
  have : ζ (i + 1) ≤ ζ a := hζ.monotone (by omega)
  rw [← hi] at this
  linarith

/-- The tail bookkeeping on u v³: given the zeros ζ, the monotonicity on each segment and the ordered
values at the zeros, the envelope properties. -/
theorem envelope {P : ℝ → ℝ} {ζ : ℕ → ℝ} (hζ : StrictMono ζ) (hT : Tendsto ζ atTop atTop)
    (hmono : ∀ k, StrictMonoOn P (Icc (ζ (2 * k)) (ζ (2 * k + 1))))
    (hanti : ∀ k, StrictAntiOn P (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2))))
    (hmin : StrictMono (fun m => P (ζ (2 * m))))
    (hmax : StrictAnti (fun m => P (ζ (2 * m + 1))))
    (hsep : ∀ m j, P (ζ (2 * m)) < P (ζ (2 * j + 1))) :
    (∀ j, ∀ s, ζ (2 * j) ≤ s → s ≠ ζ (2 * j + 1) → P s < P (ζ (2 * j + 1))) ∧
    (∀ j, ∀ s, ζ (2 * j + 1) ≤ s → s ≠ ζ (2 * j + 2) → P (ζ (2 * j + 2)) < P s) ∧
    (∀ s, ζ 0 ≤ s → P (ζ 0) ≤ P s) ∧ (∀ s, ζ 0 ≤ s → P s ≤ P (ζ 1)) := by
  -- values at the zeros
  have vup : ∀ j i, 2 * j ≤ i → P (ζ i) ≤ P (ζ (2 * j + 1)) := by
    intro j i hi
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
    · exact (hsep m j).le
    · exact hmax.antitone (by omega)
  have vlow : ∀ j i, 2 * j ≤ i → P (ζ (2 * j)) ≤ P (ζ i) := by
    intro j i hi
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
    · exact hmin.monotone (by omega)
    · exact (hsep j m).le
  -- inside a segment
  have seg : ∀ i, ∀ s ∈ Icc (ζ i) (ζ (i + 1)),
      min (P (ζ i)) (P (ζ (i + 1))) ≤ P s ∧ P s ≤ max (P (ζ i)) (P (ζ (i + 1))) := by
    intro i s hs
    have hi : ζ i ≤ ζ (i + 1) := hζ.monotone (Nat.le_succ i)
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
    · have h := (hmono m).monotoneOn
      exact ⟨min_le_left _ _ |>.trans (h ⟨le_rfl, hi⟩ hs hs.1),
        (h hs ⟨hi, le_rfl⟩ hs.2).trans (le_max_right _ _)⟩
    · have h := (hanti m).antitoneOn
      have e : 2 * m + 1 + 1 = 2 * m + 2 := by ring
      rw [e] at hs hi ⊢
      exact ⟨min_le_right _ _ |>.trans (h hs ⟨hi, le_rfl⟩ hs.2),
        (h ⟨le_rfl, hi⟩ hs hs.1).trans (le_max_left _ _)⟩
  have up : ∀ j, ∀ s, ζ (2 * j) ≤ s → P s ≤ P (ζ (2 * j + 1)) := by
    intro j s hs
    obtain ⟨i, hi, h1, h2⟩ := locate hζ hT (2 * j) hs
    have := (seg i s ⟨h1, h2.le⟩).2
    exact this.trans (max_le (vup j i hi) (vup j (i + 1) (by omega)))
  have low : ∀ j, ∀ s, ζ (2 * j) ≤ s → P (ζ (2 * j)) ≤ P s := by
    intro j s hs
    obtain ⟨i, hi, h1, h2⟩ := locate hζ hT (2 * j) hs
    have := (seg i s ⟨h1, h2.le⟩).1
    exact (le_min (vlow j i hi) (vlow j (i + 1) (by omega))).trans this
  have vlow' : ∀ j i, 2 * j + 1 ≤ i → P (ζ (2 * j + 2)) ≤ P (ζ i) := by
    intro j i hi
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
    · have : P (ζ (2 * (j + 1))) ≤ P (ζ (2 * m)) := hmin.monotone (show j + 1 ≤ m by omega)
      rwa [show 2 * (j + 1) = 2 * j + 2 by ring] at this
    · have := (hsep (j + 1) m).le
      rwa [show 2 * (j + 1) = 2 * j + 2 by ring] at this
  have lowodd : ∀ j, ∀ s, ζ (2 * j + 1) ≤ s → P (ζ (2 * j + 2)) ≤ P s := by
    intro j s hs
    obtain ⟨i, hi, h1, h2⟩ := locate hζ hT (2 * j + 1) hs
    have := (seg i s ⟨h1, h2.le⟩).1
    exact (le_min (vlow' j i hi) (vlow' j (i + 1) (by omega))).trans this
  refine ⟨?_, ?_, fun s hs => low 0 s (by simpa using hs), fun s hs => up 0 s (by simpa using hs)⟩
  · intro j s hs hne
    have h12 : ζ (2 * j + 1) < ζ (2 * j + 2) := hζ (by omega)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hmono j) ⟨hs, hlt.le⟩ ⟨hζ.monotone (by omega), le_rfl⟩ hlt
    rcases le_or_gt s (ζ (2 * j + 2)) with h2 | h2
    · exact (hanti j) ⟨le_rfl, h12.le⟩ ⟨hgt.le, h2⟩ hgt
    · have := up (j + 1) s (by rw [show 2 * (j + 1) = 2 * j + 2 by ring]; exact h2.le)
      have hm := hmax (show j < j + 1 by omega)
      simp only at hm
      rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring] at this hm
      linarith
  · intro j s hs hne
    have h23 : ζ (2 * j + 2) < ζ (2 * j + 3) := hζ (by omega)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hanti j) ⟨hs, hlt.le⟩ ⟨hζ.monotone (by omega), le_rfl⟩ hlt
    rcases le_or_gt s (ζ (2 * j + 3)) with h3 | h3
    · have hm := hmono (j + 1)
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 1 = 2 * j + 3 by ring] at hm
      exact hm ⟨le_rfl, h23.le⟩ ⟨hgt.le, h3⟩ hgt
    · have := lowodd (j + 1) s (by rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]; exact h3.le)
      have hm : P (ζ (2 * (j + 1))) < P (ζ (2 * (j + 2))) := hmin (show j + 1 < j + 2 by omega)
      rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring] at this
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * (j + 2) = 2 * j + 4 by ring] at hm
      linarith

/-- The window of the weighted norm at radius 300000 from the windows of u and v. -/
theorem N0_bounds {u v : ℝ} (hu : |u - 998005545 / 1000000000| ≤ 4 / 10000000)
    (hv : |v - 2002054156 / 1000000000| ≤ 4 / 10000000) :
    Nw (u - 1) (v - 2) ≤ 3234 / 100000000 ∧ 0 < Nw (u - 1) (v - 2) := by
  obtain ⟨u1, u2⟩ := abs_le.1 hu
  obtain ⟨v1, v2⟩ := abs_le.1 hv
  unfold Nw
  have hA : (u - 1 - (-1994855 / 1000000000)) * (u - 1 - (-1994055 / 1000000000)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hB : (u - 1 + 2 * (v - 2) - 2112657 / 1000000000) * (u - 1 + 2 * (v - 2) - 2115057 / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  constructor
  · nlinarith
  · have : (1994055 / 1000000000 : ℝ) ^ 2 ≤ (u - 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (u - 1 + 2 * (v - 2))]

/-- From the weighted-norm bound at a zero to a window of u. -/
theorem U_win {U N : ℝ} (hN : N ≤ 3234 / 100000000) (h : 32 * (U - 1) ^ 2 ≤ N) :
    989 / 990 ≤ U ∧ U ≤ 991 / 990 := by
  constructor <;> nlinarith [sq_nonneg (U - 1)]

theorem const_hi : 8 * (991 / 990 : ℝ) ^ 4 < 0.80091 ^ 2 * (4 * Real.pi) := by
  have := Real.pi_gt_d6; nlinarith

theorem const_lo : (0.787995 : ℝ) ^ 2 * (4 * Real.pi) < 8 * (989 / 990) ^ 4 := by
  have := Real.pi_lt_d6; nlinarith

/-- Ordering of the values 8u⁴ at the zeros from the alternating sides of 1 and the shrinking distance. -/
theorem vals {Uz : ℕ → ℝ} (pos : ∀ k, 0 < Uz k) (side : ∀ k, Uz (2 * k) < 1 ∧ 1 < Uz (2 * k + 1))
    (dec : ∀ k, |Uz (k + 1) - 1| < |Uz k - 1|) :
    StrictMono (fun m => 8 * Uz (2 * m) ^ 4) ∧ StrictAnti (fun m => 8 * Uz (2 * m + 1) ^ 4) ∧
    ∀ m j, 8 * Uz (2 * m) ^ 4 < 8 * Uz (2 * j + 1) ^ 4 := by
  refine ⟨strictMono_nat_of_lt_succ fun m => ?_, strictAnti_nat_of_succ_lt fun m => ?_, fun m j => ?_⟩
  · have d := (dec (2 * m + 1)).trans (dec (2 * m))
    have s1 := (side m).1
    have s2 := (side (m + 1)).1
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e] at s2
    show 8 * Uz (2 * m) ^ 4 < 8 * Uz (2 * (m + 1)) ^ 4
    rw [e]
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at d
    have h1 : Uz (2 * m) < Uz (2 * m + 1 + 1) := by linarith
    have := pow_lt_pow_left₀ h1 (pos _).le (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  · have d := (dec (2 * m + 1 + 1)).trans (dec (2 * m + 1))
    have s1 := (side m).2
    have s2 := (side (m + 1)).2
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [e] at s2
    show 8 * Uz (2 * (m + 1) + 1) ^ 4 < 8 * Uz (2 * m + 1) ^ 4
    rw [e]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at d
    have h1 : Uz (2 * m + 1 + 1 + 1) < Uz (2 * m + 1) := by linarith
    have := pow_lt_pow_left₀ h1 (pos _).le (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  · have s1 := (side m).1
    have s2 := (side j).2
    have h1 : Uz (2 * m) ^ 4 < 1 := pow_lt_one₀ (pos _).le s1 (by norm_num)
    have h2 : 1 < Uz (2 * j + 1) ^ 4 := one_lt_pow₀ s2 (by norm_num)
    linarith

set_option maxHeartbeats 4000000 in
/-- The assembly behind `Work.Math.BonnorEbertAll.bonnor_ebert_all_extrema`. -/
theorem main (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ξ 0 →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) →
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ,
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) <
          ξ (2 * k) ^ 2 * (-φ (ξ (2 * k))) * Real.exp (w (ξ (2 * k)) / 2) / Real.sqrt (4 * Real.pi)) ∧
      Tendsto (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) atTop
        (𝓝 (Real.sqrt (2 / Real.pi))) := by
  -- φ < 0 from radius 7 on
  have φneg : ∀ s, 7 ≤ s → φ s < 0 := by
    intro s hs
    obtain ⟨r1, r2, r3⟩ := restrict (max s 300000) hw hφ0 hφ
    exact (Work.Math.BEState300.state300 (max s 300000) (le_max_right _ _) w φ r1 r2 r3 h0).1 s
      ⟨hs, le_max_left _ _⟩
  obtain ⟨r1, r2, r3⟩ := restrict 300000 hw hφ0 hφ
  obtain ⟨-, su, sv, sg⟩ := Work.Math.BEState300.state300 300000 le_rfl w φ r1 r2 r3 h0
  obtain ⟨ξ₁, ξ₂, ξ₃, ξ₄, ξ₅, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hmax, hmin, hmax2, hmin2,
    hmax3, M5lo, -, -, -, m4hi, Panti5⟩ := Work.Math.BE3Ext.main_ext 300000 le_rfl w φ r1 r2 r3 h0
  norm_num at a3 a4 a5 a6 a7 a8 a9 a10
  -- derivatives
  have dws : ∀ t : ℝ, 0 < t →
      HasDerivAt w (φ t) t ∧ HasDerivAt φ (-(2 / t * φ t) - Real.exp (w t)) t := fun t ht =>
    ⟨(hw t (le_of_lt ht)).hasDerivAt (Ici_mem_nhds ht), (hφ t ht).hasDerivAt (Ici_mem_nhds ht)⟩
  have dUV : ∀ t : ℝ, 7 ≤ t →
      HasDerivAt (Uf w φ) (Uf w φ t * (3 - Uf w φ t - Vf w φ t) / t) t ∧
      HasDerivAt (Vf w φ) (Vf w φ t * (Uf w φ t - 1) / t) t := fun t ht =>
    Checked.Math.BEHMain.homology_deriv_at (by linarith) (φneg t ht) (dws t (by linarith)).1
      (dws t (by linarith)).2
  have dP : ∀ t ∈ Ici (7 : ℝ), HasDerivAt (Pf w φ) (Pf w φ t * (2 * Uf w φ t - Vf w φ t) / t) t := by
    intro t ht
    obtain ⟨d1, d2⟩ := dUV t ht
    have ht0 : 0 < t := by linarith [mem_Ici.1 ht]
    have hd : HasDerivAt (fun s => Uf w φ s * Vf w φ s ^ 3)
        (Uf w φ t * (3 - Uf w φ t - Vf w φ t) / t * Vf w φ t ^ 3 +
          Uf w φ t * (↑3 * Vf w φ t ^ (3 - 1) * (Vf w φ t * (Uf w φ t - 1) / t))) t :=
      d1.mul (d2.pow 3)
    refine hd.congr_deriv ?_
    unfold Pf
    field_simp; ring
  have UVpos7 : ∀ t : ℝ, 7 ≤ t → 0 < Uf w φ t ∧ 0 < Vf w φ t := by
    intro t ht
    have h1 := φneg t ht
    have h2 := Real.exp_pos (w t)
    have h3 : (0 : ℝ) < t := by linarith
    refine ⟨div_pos (by positivity) (by linarith), ?_⟩
    show 0 < -(t * φ t)
    nlinarith
  have Ppos : ∀ t ∈ Ici (7 : ℝ), 0 < Pf w φ t := fun t ht => by
    obtain ⟨h1, h2⟩ := UVpos7 t ht
    unfold Pf; positivity
  have Mlt : ∀ s t : ℝ, 7 ≤ s → 7 ≤ t → Pf w φ s < Pf w φ t → Mf w φ s < Mf w φ t :=
    fun s t hs ht h => Checked.Math.BEHMain.mass_lt (by linarith) (φneg s hs) (by linarith) (φneg t ht) h
  -- the analytic tail from radius 300000
  have su' : |Uf w φ 300000 - 998005545 / 1000000000| ≤ 4 / 10000000 := su
  have sv' : |Vf w φ 300000 - 2002054156 / 1000000000| ≤ 4 / 10000000 := sv
  obtain ⟨N0le, N0pos⟩ := N0_bounds su' sv'
  have hg0 : 2 * Uf w φ 300000 - Vf w φ 300000 < 0 := sg 300000 ⟨by norm_num, le_rfl⟩
  obtain ⟨ζ, hζ, hT, hζ0, gneg0, gz, gpos, gneg, Uside, Udec, Nz, -, Ulim, Vlim⟩ :=
    Work.Math.BEFocus.tail (U := Uf w φ) (V := Vf w φ) (s0 := 300000) (by norm_num)
      (fun t ht => (dUV t (by linarith [mem_Ici.1 ht])).1)
      (fun t ht => (dUV t (by linarith [mem_Ici.1 ht])).2) (by linarith) N0pos hg0
  have ζbig : ∀ k, 300000 < ζ k := fun k => lt_of_lt_of_le hζ0 (hζ.monotone (Nat.zero_le k))
  have ζ7 : ∀ k, (7 : ℝ) ≤ ζ k := fun k => by linarith [ζbig k]
  have Uw : ∀ k, 989 / 990 ≤ Uf w φ (ζ k) ∧ Uf w φ (ζ k) ≤ 991 / 990 := fun k => U_win N0le (Nz k)
  have Pz : ∀ k, Pf w φ (ζ k) = 8 * Uf w φ (ζ k) ^ 4 := by
    intro k
    have h := gz k
    have hv : Vf w φ (ζ k) = 2 * Uf w φ (ζ k) := by linarith
    unfold Pf; rw [hv]; ring
  have Upos : ∀ k, 0 < Uf w φ (ζ k) := fun k => by linarith [(Uw k).1]
  -- the values at the zeros
  obtain ⟨vmin, vmax, vsep⟩ := vals (Uz := fun k => Uf w φ (ζ k)) Upos Uside Udec
  have hminv : StrictMono (fun m => Pf w φ (ζ (2 * m))) := by
    have e : (fun m => Pf w φ (ζ (2 * m))) = fun m => 8 * Uf w φ (ζ (2 * m)) ^ 4 :=
      funext fun m => Pz _
    rw [e]; exact vmin
  have hmaxv : StrictAnti (fun m => Pf w φ (ζ (2 * m + 1))) := by
    have e : (fun m => Pf w φ (ζ (2 * m + 1))) = fun m => 8 * Uf w φ (ζ (2 * m + 1)) ^ 4 :=
      funext fun m => Pz _
    rw [e]; exact vmax
  have hsep : ∀ m j, Pf w φ (ζ (2 * m)) < Pf w φ (ζ (2 * j + 1)) := fun m j => by
    rw [Pz, Pz]; exact vsep m j
  -- monotonicity on the segments
  have dPI : ∀ a b : ℝ, 7 ≤ a → ∀ t ∈ Icc a b,
      HasDerivAt (Pf w φ) (Pf w φ t * (2 * Uf w φ t - Vf w φ t) / t) t :=
    fun a b ha t ht => dP t (mem_Ici.2 (ha.trans ht.1))
  have PposI : ∀ a b : ℝ, 7 ≤ a → ∀ t ∈ Icc a b, 0 < Pf w φ t :=
    fun a b ha t ht => Ppos t (mem_Ici.2 (ha.trans ht.1))
  have hmono : ∀ k, StrictMonoOn (Pf w φ) (Icc (ζ (2 * k)) (ζ (2 * k + 1))) := fun k =>
    P_mono_of_pos (g := fun t => 2 * Uf w φ t - Vf w φ t) (by linarith [ζ7 (2 * k)])
      (hζ.monotone (by omega)) (dPI _ _ (ζ7 _)) (PposI _ _ (ζ7 _)) (gpos k)
  have hanti : ∀ k, StrictAntiOn (Pf w φ) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2))) := fun k =>
    P_anti_of_neg (g := fun t => 2 * Uf w φ t - Vf w φ t) (by linarith [ζ7 (2 * k + 1)])
      (hζ.monotone (by omega)) (dPI _ _ (ζ7 _)) (PposI _ _ (ζ7 _)) (gneg k)
  have anti0 : StrictAntiOn (Pf w φ) (Icc 300000 (ζ 0)) :=
    P_anti_of_neg (g := fun t => 2 * Uf w φ t - Vf w φ t) (by norm_num) (ζbig 0).le
      (dPI _ _ (by norm_num)) (PposI _ _ (by norm_num)) (fun t ht => gneg0 t ⟨ht.1.le, ht.2⟩)
  obtain ⟨E1, E2, E3, E4⟩ := envelope hζ hT hmono hanti hminv hmaxv hsep
  -- from the third maximum to the first tail zero
  have Panti5' : StrictAntiOn (Pf w φ) (Icc ξ₅ 300000) := Panti5
  have PA : StrictAntiOn (Pf w φ) (Icc ξ₅ (ζ 0)) := by
    intro x hx y hy hxy
    rcases le_or_gt y 300000 with hy3 | hy3
    · exact Panti5' ⟨hx.1, by linarith⟩ ⟨hy.1, hy3⟩ hxy
    rcases le_or_gt 300000 x with hx3 | hx3
    · exact anti0 ⟨hx3, hx.2⟩ ⟨hy3.le, hy.2⟩ hxy
    · have h1 := anti0 ⟨le_rfl, (ζbig 0).le⟩ ⟨hy3.le, hy.2⟩ hy3
      have h2 := Panti5'.antitoneOn ⟨hx.1, hx3.le⟩ ⟨by linarith [hx.1], le_rfl⟩ hx3.le
      linarith
  have h5lo : (84497 : ℝ) ≤ ξ₅ := a9
  have h5hi : ξ₅ ≤ 84516 := a10
  have ξ57 : (7 : ℝ) ≤ ξ₅ := by linarith
  have ξ47 : (7 : ℝ) ≤ ξ₄ := by linarith
  have Pξ5 : 0.80091 ^ 2 * (4 * Real.pi) ≤ Pf w φ ξ₅ :=
    P_lt_of_M (by linarith) (φneg ξ₅ ξ57) (by norm_num) M5lo
  have Pξ4 : Pf w φ ξ₄ ≤ 0.787995 ^ 2 * (4 * Real.pi) :=
    P_le_of_M (by linarith) (φneg ξ₄ ξ47) m4hi
  have Pζ1 : Pf w φ (ζ 1) ≤ 8 * (991 / 990 : ℝ) ^ 4 := by
    rw [Pz]
    have := pow_le_pow_left₀ (Upos 1).le (Uw 1).2 4
    linarith
  have Pζ0 : 8 * (989 / 990 : ℝ) ^ 4 ≤ Pf w φ (ζ 0) := by
    rw [Pz]
    have := pow_le_pow_left₀ (by norm_num) (Uw 0).1 4
    linarith
  have chi := const_hi
  have clo := const_lo
  have T1 : ∀ s : ℝ, 300000 < s → Pf w φ s < Pf w φ ξ₅ := by
    intro s hs
    rcases le_or_gt s (ζ 0) with h | h
    · exact PA ⟨le_rfl, by linarith⟩ ⟨by linarith, h⟩ (by linarith)
    · have := E4 s h.le
      linarith
  have T2 : ∀ s : ℝ, 300000 ≤ s → Pf w φ ξ₄ < Pf w φ s := by
    intro s hs
    have : Pf w φ (ζ 0) ≤ Pf w φ s := by
      rcases le_or_gt s (ζ 0) with h | h
      · exact PA.antitoneOn ⟨by linarith, h⟩ ⟨by linarith [ζbig 0], le_rfl⟩ h
      · exact E3 s h.le
    linarith
  have ξ4lo : (15699 / 2 : ℝ) ≤ ξ₄ := by linarith
  have ξ4hi : ξ₄ ≤ 31399 / 4 := by linarith
  have cb := c_bounds
  -- the mass at the certified extrema relative to √(2/π)
  have M5gt : Real.sqrt (2 / Real.pi) < Mf w φ ξ₅ := by
    have : (0.80091 : ℝ) ≤ Mf w φ ξ₅ := M5lo
    linarith [cb.2]
  have M4lt : Mf w φ ξ₄ < Real.sqrt (2 / Real.pi) := by
    have : Mf w φ ξ₄ ≤ 0.787995 := m4hi
    linarith [cb.1]
  have M51 : Mf w φ ξ₅ < Mf w φ ξ₁ := hmax ξ₅ ⟨by linarith, by linarith⟩ (by
    intro h; norm_num at a1 a2; linarith)
  have M53 : Mf w φ ξ₅ < Mf w φ ξ₃ := hmax2 ξ₅ ⟨by linarith, by linarith⟩ (by intro h; linarith)
  have M24 : Mf w φ ξ₂ < Mf w φ ξ₄ := hmin ξ₄ ⟨by norm_num at a1 a2; linarith, by linarith⟩
    (by intro h; linarith)
  refine ⟨seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ, ?_, ?_, a1, a2, ?_, ?_, ?_, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    match n with
    | 0 => show ξ₁ < ξ₂; norm_num at a1 a2; linarith
    | 1 => show ξ₂ < ξ₃; linarith
    | 2 => show ξ₃ < ξ₄; linarith
    | 3 => show ξ₄ < ξ₅; linarith
    | 4 => show ξ₅ < ζ 0; linarith [ζbig 0]
    | k + 5 => show ζ k < ζ (k + 1); exact hζ (Nat.lt_succ_self k)
  · rw [← Filter.tendsto_add_atTop_iff_nat 5]
    exact hT
  · intro s hs hne
    show Mf w φ s < Mf w φ ξ₁
    rcases le_or_gt s 300000 with h | h
    · exact hmax s ⟨hs, h⟩ hne
    · exact (Mlt s ξ₅ (by linarith) ξ57 (T1 s h)).trans M51
  · intro k
    match k with
    | 0 =>
      intro s hs hne
      show Mf w φ ξ₂ < Mf w φ s
      have hs' : ξ₁ ≤ s := hs
      rcases le_or_gt s 300000 with h | h
      · exact hmin s ⟨hs', h⟩ hne
      · exact M24.trans (Mlt ξ₄ s ξ47 (by linarith) (T2 s h.le))
    | 1 =>
      intro s hs hne
      show Mf w φ ξ₄ < Mf w φ s
      have hs' : ξ₃ ≤ s := hs
      rcases le_or_gt s 300000 with h | h
      · exact hmin2 s ⟨hs', h⟩ hne
      · exact Mlt ξ₄ s ξ47 (by linarith) (T2 s h.le)
    | 2 =>
      intro s hs hne
      show Mf w φ (ζ 0) < Mf w φ s
      have hs' : ξ₅ ≤ s := hs
      have hne' : s ≠ ζ 0 := hne
      apply Mlt (ζ 0) s (ζ7 0) (by linarith)
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · exact PA ⟨hs', hlt.le⟩ ⟨by linarith [ζbig 0], le_rfl⟩ hlt
      rcases le_or_gt s (ζ 1) with h1 | h1
      · exact hmono 0 ⟨le_rfl, (hζ (by norm_num : 0 < 1)).le⟩ ⟨hgt.le, h1⟩ hgt
      · have h02 : Pf w φ (ζ 0) < Pf w φ (ζ 2) := hminv (show 0 < 1 by norm_num)
        rcases eq_or_ne s (ζ 2) with he | he
        · rw [he]; exact h02
        · exact h02.trans (E2 0 s h1.le he)
    | i + 3 =>
      have e1 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3)) = ζ (2 * i + 1) := by
        rw [show 2 * (i + 3) = (2 * i + 1) + 5 by ring]; rfl
      have e2 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3) + 1) = ζ (2 * i + 2) := by
        rw [show 2 * (i + 3) + 1 = (2 * i + 2) + 5 by ring]; rfl
      rw [e1, e2]
      intro s hs hne
      exact Mlt _ s (ζ7 _) (by linarith [ζ7 (2 * i + 1), mem_Ici.1 hs]) (E2 i s hs hne)
  · intro k
    match k with
    | 0 =>
      intro s hs hne
      show Mf w φ s < Mf w φ ξ₃
      have hs' : ξ₂ ≤ s := hs
      rcases le_or_gt s 300000 with h | h
      · exact hmax2 s ⟨hs', h⟩ hne
      · exact (Mlt s ξ₅ (by linarith) ξ57 (T1 s h)).trans M53
    | 1 =>
      intro s hs hne
      show Mf w φ s < Mf w φ ξ₅
      have hs' : ξ₄ ≤ s := hs
      rcases le_or_gt s 300000 with h | h
      · exact hmax3 s ⟨hs', h⟩ hne
      · exact Mlt s ξ₅ (by linarith) ξ57 (T1 s h)
    | i + 2 =>
      have e1 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 2) + 1) = ζ (2 * i) := by
        rw [show 2 * (i + 2) + 1 = 2 * i + 5 by ring]; rfl
      have e2 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 2) + 2) = ζ (2 * i + 1) := by
        rw [show 2 * (i + 2) + 2 = (2 * i + 1) + 5 by ring]; rfl
      rw [e1, e2]
      intro s hs hne
      exact Mlt s _ (by linarith [ζ7 (2 * i), mem_Ici.1 hs]) (ζ7 _) (E1 i s hs hne)
  · intro k
    match k with
    | 0 => exact ⟨(M24.trans M4lt : Mf w φ ξ₂ < _), (M5gt.trans M51 : _ < Mf w φ ξ₁)⟩
    | 1 => exact ⟨(M4lt : Mf w φ ξ₄ < _), (M5gt.trans M53 : _ < Mf w φ ξ₃)⟩
    | 2 =>
      refine ⟨?_, (M5gt : _ < Mf w φ ξ₅)⟩
      show Mf w φ (ζ 0) < _
      apply (band (by linarith [ζ7 0]) (φneg _ (ζ7 0))).1
      rw [Pz]
      have s1 : Uf w φ (ζ 0) < 1 := (Uside 0).1
      have h1 : Uf w φ (ζ 0) ^ 4 < 1 := pow_lt_one₀ (Upos _).le s1 (by norm_num)
      linarith
    | i + 3 =>
      have e1 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3) + 1) = ζ (2 * (i + 1)) := by
        rw [show 2 * (i + 3) + 1 = 2 * (i + 1) + 5 by ring]; rfl
      have e2 : seq ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ ζ (2 * (i + 3)) = ζ (2 * i + 1) := by
        rw [show 2 * (i + 3) = (2 * i + 1) + 5 by ring]; rfl
      rw [e1, e2]
      constructor
      · apply (band (by linarith [ζ7 (2 * (i + 1))]) (φneg _ (ζ7 _))).1
        rw [Pz]
        have h1 : Uf w φ (ζ (2 * (i + 1))) ^ 4 < 1 :=
          pow_lt_one₀ (Upos _).le (Uside (i + 1)).1 (by norm_num)
        linarith
      · apply (band (by linarith [ζ7 (2 * i + 1)]) (φneg _ (ζ7 _))).2
        rw [Pz]
        have h2 : 1 < Uf w φ (ζ (2 * i + 1)) ^ 4 := one_lt_pow₀ (Uside i).2 (by norm_num)
        linarith
  · -- the limit
    have hPl : Tendsto (Pf w φ) atTop (𝓝 (1 * 2 ^ 3)) := Ulim.mul (Vlim.pow 3)
    have hl : Tendsto (fun s => Real.sqrt (Pf w φ s / (4 * Real.pi))) atTop
        (𝓝 (Real.sqrt (1 * 2 ^ 3 / (4 * Real.pi)))) :=
      (hPl.div_const (4 * Real.pi)).sqrt
    have hv : Real.sqrt (1 * 2 ^ 3 / (4 * Real.pi)) = Real.sqrt (2 / Real.pi) := by
      congr 1; have := Real.pi_pos; field_simp; ring
    rw [hv] at hl
    refine hl.congr' ?_
    filter_upwards [eventually_ge_atTop (7 : ℝ)] with s hs
    exact (M_eq (by linarith) (φneg s hs)).symm

end Work.Math.BEAllMain
