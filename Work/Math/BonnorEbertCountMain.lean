import Mathlib
import Checked.Math.BonnorEbertMonotone
import Checked.Math.BonnorEbertMax
import Checked.Math.BonnorEbertMin
import Checked.Math.BonnorEbertMax2
import Checked.Math.BonnorEbertMin2
import Checked.Math.BonnorEbertMax3

/-! Route of `Work.Math.BonnorEbertCount.bonnor_ebert_count` (run 2026-11-18T1628Z, no new certificates).

(1) `count_abstract`: for any continuous f on the half-line with f(0) = 0 and a strictly increasing
sequence ξ of strict alternating extrema (the facts of `bonnor_ebert_extrema_monotone` with the limit
value replaced by any positive L), the number of roots of f = μ: prepend 0 to ξ (`shiftSeq`), so that the
segments are [0, ξ 0], [ξ 0, ξ 1], …; in each segment where μ lies strictly between the end values there is
exactly one root (`seg_root`: intermediate value theorem, injectivity), so the roots below the n-th
segment end number n (`count_prefix`), and the roots beyond it are read off the strict extremum
properties (`count_total` + tail sets). The maxima f(ξ(2k)) decrease and the minima f(ξ(2k+1)) increase
(`maxlt`, `minlt`), all maxima lie above L and all minima below (`hband`).
(2) `ident_max`/`ident_min`: a strict extremum on [a, S] below S equals the strict extremum from a on, when f
is strictly monotone between a and the latter; this identifies the extremisers of the bounded-interval
headlines with ξ 0 … ξ 4 and gives the five value windows. -/

namespace Work.Math.BonnorEbertCountMain
open Set Filter Topology

/-- The sequence 0, ξ 0, ξ 1, …. -/
noncomputable def shiftSeq (ξ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => ξ j

lemma seg_root (f : ℝ → ℝ) (a b μ : ℝ) (hab : a < b) (hc : ContinuousOn f (Icc a b))
    (hinj : InjOn f (Icc a b)) (hP : (f a - μ) * (f b - μ) < 0) :
    ∃ r ∈ Ioo a b, f r = μ ∧ ∀ s ∈ Icc a b, f s = μ → s = r := by
  have hex : ∃ r ∈ Ioo a b, f r = μ := by
    rcases mul_neg_iff.1 hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact intermediate_value_Ioo' hab.le hc ⟨by linarith, by linarith⟩
    · exact intermediate_value_Ioo hab.le hc ⟨by linarith, by linarith⟩
  obtain ⟨r, hr, hfr⟩ := hex
  exact ⟨r, hr, hfr, fun s hs hfs => hinj hs (Ioo_subset_Icc_self hr) (hfs.trans hfr.symm)⟩

lemma count_prefix (f : ℝ → ℝ) (η : ℕ → ℝ) (hη : StrictMono η)
    (hc : ContinuousOn f (Ici (η 0))) (hinj : ∀ j, InjOn f (Icc (η j) (η (j + 1))))
    (μ : ℝ) : ∀ n : ℕ, (∀ j < n, (f (η j) - μ) * (f (η (j + 1)) - μ) < 0) →
      {s ∈ Ico (η 0) (η n) | f s = μ}.encard = n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hP
    have hlt : η n < η (n + 1) := hη (Nat.lt_succ_self n)
    have h0n : η 0 ≤ η n := hη.monotone (Nat.zero_le n)
    have hc' : ContinuousOn f (Icc (η n) (η (n + 1))) :=
      hc.mono (fun x hx => le_trans h0n hx.1)
    obtain ⟨r, hr, hfr, huniq⟩ :=
      seg_root f _ _ μ hlt hc' (hinj n) (hP n (Nat.lt_succ_self n))
    have hsplit : {s ∈ Ico (η 0) (η (n + 1)) | f s = μ} =
        {s ∈ Ico (η 0) (η n) | f s = μ} ∪ {r} := by
      ext s
      simp only [mem_ofPred_eq, mem_union, mem_singleton_iff, mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases hs : s < η n
        · exact Or.inl ⟨⟨h1, hs⟩, h3⟩
        · exact Or.inr (huniq s ⟨le_of_not_gt hs, h2.le⟩ h3)
      · rintro (⟨⟨h1, h2⟩, h3⟩ | rfl)
        · exact ⟨⟨h1, h2.trans hlt⟩, h3⟩
        · exact ⟨⟨le_trans h0n hr.1.le, hr.2⟩, hfr⟩
    have hdisj : Disjoint {s ∈ Ico (η 0) (η n) | f s = μ} {r} := by
      rw [Set.disjoint_left]
      rintro s ⟨⟨_, h2⟩, _⟩ hs
      rw [mem_singleton_iff] at hs
      subst hs
      exact absurd hr.1 (not_lt.2 h2.le)
    rw [hsplit, Set.encard_union_eq hdisj, Set.encard_singleton,
      ih (fun j hj => hP j (Nat.lt_succ_of_lt hj))]
    push_cast
    rfl

lemma count_total (f : ℝ → ℝ) (η : ℕ → ℝ) (hη : StrictMono η)
    (hc : ContinuousOn f (Ici (η 0))) (hinj : ∀ j, InjOn f (Icc (η j) (η (j + 1))))
    (μ : ℝ) (n : ℕ) (hP : ∀ j < n, (f (η j) - μ) * (f (η (j + 1)) - μ) < 0) :
    {s ∈ Ici (η 0) | f s = μ}.encard = n + {s ∈ Ici (η n) | f s = μ}.encard := by
  have h0n : η 0 ≤ η n := hη.monotone (Nat.zero_le n)
  have hsplit : {s ∈ Ici (η 0) | f s = μ} =
      {s ∈ Ico (η 0) (η n) | f s = μ} ∪ {s ∈ Ici (η n) | f s = μ} := by
    ext s
    simp only [mem_ofPred_eq, mem_union, mem_Ico, mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hs : s < η n
      · exact Or.inl ⟨⟨h1, hs⟩, h2⟩
      · exact Or.inr ⟨le_of_not_gt hs, h2⟩
    · rintro (⟨⟨h1, _⟩, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨h0n.trans h1, h2⟩
  have hdisj : Disjoint {s ∈ Ico (η 0) (η n) | f s = μ} {s ∈ Ici (η n) | f s = μ} := by
    rw [Set.disjoint_left]
    rintro s ⟨⟨_, h1⟩, _⟩ ⟨h2, _⟩
    exact absurd h2 (not_le.2 h1)
  rw [hsplit, Set.encard_union_eq hdisj, count_prefix f η hη hc hinj μ n hP]

lemma tail_empty (f : ℝ → ℝ) (a μ : ℝ) (h : ∀ s, a ≤ s → f s ≠ μ) :
    {s ∈ Ici a | f s = μ}.encard = 0 := by
  rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro s ⟨hs, hfs⟩
  exact h s hs hfs

lemma tail_single (f : ℝ → ℝ) (a x μ : ℝ) (hx : a ≤ x) (hfx : f x = μ)
    (h : ∀ s, a ≤ s → s ≠ x → f s ≠ μ) :
    {s ∈ Ici a | f s = μ}.encard = 1 := by
  have : {s ∈ Ici a | f s = μ} = {x} := by
    ext s
    simp only [mem_ofPred_eq, mem_singleton_iff, mem_Ici]
    constructor
    · rintro ⟨hs, hfs⟩
      by_contra hne
      exact h s hs hne hfs
    · rintro rfl
      exact ⟨hx, hfx⟩
  rw [this, Set.encard_singleton]

/-- The counting theorem for an abstract function with the extremum structure. -/
theorem count_abstract (f : ℝ → ℝ) (ξ : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hc : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0) (hmono : StrictMono ξ) (hξ0 : 0 < ξ 0)
    (hpos1 : 0 < f (ξ 1))
    (hmax0 : ∀ s ∈ Ici (0 : ℝ), s ≠ ξ 0 → f s < f (ξ 0))
    (hmin : ∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) → f (ξ (2 * k + 1)) < f s)
    (hmax : ∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) → f s < f (ξ (2 * k + 2)))
    (hband : ∀ k : ℕ, f (ξ (2 * k + 1)) < L ∧ L < f (ξ (2 * k)))
    (hinc0 : StrictMonoOn f (Icc 0 (ξ 0)))
    (hdec : ∀ k : ℕ, StrictAntiOn f (Icc (ξ (2 * k)) (ξ (2 * k + 1))))
    (hinc : ∀ k : ℕ, StrictMonoOn f (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) :
    (∀ μ : ℝ, f (ξ 0) < μ → {s ∈ Ici (0 : ℝ) | f s = μ}.encard = 0) ∧
    {s ∈ Ici (0 : ℝ) | f s = f (ξ 0)}.encard = 1 ∧
    (∀ k : ℕ, ∀ μ : ℝ, f (ξ (2 * k + 2)) < μ → μ < f (ξ (2 * k)) →
      {s ∈ Ici (0 : ℝ) | f s = μ}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
    (∀ k : ℕ, {s ∈ Ici (0 : ℝ) | f s = f (ξ (2 * k + 2))}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
    (∀ μ : ℝ, 0 < μ → μ < f (ξ 1) → {s ∈ Ici (0 : ℝ) | f s = μ}.encard = 1) ∧
    (∀ k : ℕ, {s ∈ Ici (0 : ℝ) | f s = f (ξ (2 * k + 1))}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
    (∀ k : ℕ, ∀ μ : ℝ, f (ξ (2 * k + 1)) < μ → μ < f (ξ (2 * k + 3)) →
      {s ∈ Ici (0 : ℝ) | f s = μ}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
    {s ∈ Ici (0 : ℝ) | f s = L}.encard = ⊤ := by
  set η := shiftSeq ξ with hηdef
  have hη0 : η 0 = 0 := rfl
  have hηs : ∀ j, η (j + 1) = ξ j := fun j => rfl
  have hξnn : ∀ j, 0 ≤ ξ j := fun j => hξ0.le.trans (hmono.monotone (Nat.zero_le j))
  have hηmono : StrictMono η := by
    apply strictMono_nat_of_lt_succ
    intro j
    cases j with
    | zero => rw [hη0, hηs]; exact hξ0
    | succ i => rw [hηs, hηs]; exact hmono (Nat.lt_succ_self i)
  have hc' : ContinuousOn f (Ici (η 0)) := by rw [hη0]; exact hc
  have hinj : ∀ j, InjOn f (Icc (η j) (η (j + 1))) := by
    intro j
    cases j with
    | zero => rw [hη0, hηs]; exact hinc0.injOn
    | succ i =>
      rw [hηs, hηs]
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
      · subst hk; exact (hdec k).injOn
      · subst hk
        have e : 2 * k + 1 + 1 = 2 * k + 2 := by ring
        rw [e]; exact (hinc k).injOn
  -- order of the extreme values
  have maxlt : ∀ i k : ℕ, i ≤ k → f (ξ (2 * k + 2)) < f (ξ (2 * i)) := by
    intro i k hik
    cases i with
    | zero =>
      have := hmax0 (ξ (2 * k + 2)) (hξnn _) (hmono.injective.ne (by omega))
      simpa using this
    | succ i =>
      have e : 2 * (i + 1) = 2 * i + 2 := by ring
      rw [e]
      exact hmax i (ξ (2 * k + 2)) (hmono.monotone (by omega)) (hmono.injective.ne (by omega))
  have maxle : ∀ i k : ℕ, i ≤ k → f (ξ (2 * k)) ≤ f (ξ (2 * i)) := by
    intro i k hik
    rcases eq_or_lt_of_le hik with h | h
    · rw [h]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have e : 2 * (k' + 1) = 2 * k' + 2 := by ring
      rw [e]; exact (maxlt i k' (by omega)).le
  have minlt : ∀ i k : ℕ, i < k → f (ξ (2 * i + 1)) < f (ξ (2 * k + 1)) := by
    intro i k hik
    exact hmin i (ξ (2 * k + 1)) (hmono.monotone (by omega)) (hmono.injective.ne (by omega))
  have minle : ∀ i k : ℕ, i ≤ k → f (ξ (2 * i + 1)) ≤ f (ξ (2 * k + 1)) := by
    intro i k hik
    rcases eq_or_lt_of_le hik with h | h
    · rw [h]
    · exact (minlt i k h).le
  -- the segment condition
  have segOK : ∀ (B : ℕ) (μ : ℝ), 0 < μ → (∀ e : ℕ, 2 * e ≤ B → μ < f (ξ (2 * e))) →
      (∀ o : ℕ, 2 * o + 1 ≤ B → f (ξ (2 * o + 1)) < μ) →
      ∀ j < B + 1, (f (η j) - μ) * (f (η (j + 1)) - μ) < 0 := by
    intro B μ hμ he ho j hj
    cases j with
    | zero =>
      rw [hη0, hηs, hf0]
      have := he 0 (by omega)
      rw [Nat.mul_zero] at this
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    | succ i =>
      rw [hηs, hηs]
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' i
      · subst hk
        have h1 := he k (by omega)
        have h2 := ho k (by omega)
        exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
      · subst hk
        have h1 := ho k (by omega)
        have h2 := he (k + 1) (by omega)
        have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
        rw [e] at h2
        exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have total := fun μ n hP => count_total f η hηmono hc' hinj μ n hP
  -- tail facts
  have tailMax : ∀ k : ℕ, ∀ s, ξ (2 * k + 1) ≤ s → f s ≤ f (ξ (2 * k + 2)) := by
    intro k s hs
    by_cases h : s = ξ (2 * k + 2)
    · rw [h]
    · exact (hmax k s hs h).le
  have tailMin : ∀ k : ℕ, ∀ s, ξ (2 * k) ≤ s → f (ξ (2 * k + 1)) ≤ f s := by
    intro k s hs
    by_cases h : s = ξ (2 * k + 1)
    · rw [h]
    · exact (hmin k s hs h).le
  have hL1 : ∀ o, f (ξ (2 * o + 1)) < L := fun o => (hband o).1
  have hL2 : ∀ e, L < f (ξ (2 * e)) := fun e => (hband e).2
  refine ⟨?ca, ?cb, ?cc, ?cd, ?ce, ?cf, ?cg, ?ch⟩
  case ca =>
    intro μ hμ
    rw [← hη0]
    rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) + 0 by simp]
    rw [total μ 0 (fun j hj => absurd hj (Nat.not_lt_zero j))]
    congr 1
    apply tail_empty
    intro s hs hfs
    rw [hη0] at hs
    by_cases h : s = ξ 0
    · rw [h] at hfs; linarith
    · have := hmax0 s hs h; linarith
  case cb =>
    have : {s ∈ Ici (0 : ℝ) | f s = f (ξ 0)} = {ξ 0} := by
      ext s
      simp only [mem_ofPred_eq, mem_singleton_iff, mem_Ici]
      constructor
      · rintro ⟨hs, hfs⟩
        by_contra h
        have := hmax0 s hs h; linarith
      · rintro rfl; exact ⟨hξnn 0, rfl⟩
    rw [this, Set.encard_singleton]
  case cc =>
    intro k μ h1 h2
    have hμ : 0 < μ := by have := hL2 (k + 1); have e : 2 * (k + 1) = 2 * k + 2 := by ring
                          rw [e] at this; linarith
    rw [← hη0, total μ (2 * k + 1 + 1) (segOK (2 * k + 1) μ hμ
      (fun e he => lt_of_lt_of_le h2 (maxle e k (by omega)))
      (fun o _ => by
        have := hL1 o; have := hL2 (k + 1); have e : 2 * (k + 1) = 2 * k + 2 := by ring
        rw [e] at this; linarith))]
    rw [tail_empty f _ μ (fun s hs hfs => by
      rw [hηs] at hs
      have := tailMax k s hs; linarith)]
    push_cast; ring
  case cd =>
    intro k
    set μ := f (ξ (2 * k + 2)) with hμdef
    have hμ : 0 < μ := by have := hL2 (k + 1); have e : 2 * (k + 1) = 2 * k + 2 := by ring
                          rw [e] at this; linarith
    rw [← hη0, total μ (2 * k + 1 + 1) (segOK (2 * k + 1) μ hμ
      (fun e he => maxlt e k (by omega))
      (fun o _ => by
        have := hL1 o; have := hL2 (k + 1); have e : 2 * (k + 1) = 2 * k + 2 := by ring
        rw [e] at this; linarith))]
    rw [tail_single f _ (ξ (2 * k + 2)) μ (by rw [hηs]; exact (hmono (by omega)).le) rfl
      (fun s hs hne => by
        rw [hηs] at hs
        exact (hmax k s hs hne).ne)]
    push_cast; ring
  case ce =>
    intro μ hμ h1
    rw [← hη0, total μ (0 + 1) (segOK 0 μ hμ
      (fun e he => by
        have e0 : e = 0 := by omega
        subst e0
        have := hL1 0; have := hL2 0; simp only [Nat.mul_zero, Nat.zero_add] at *; linarith)
      (fun o ho => absurd ho (by omega)))]
    rw [tail_empty f _ μ (fun s hs hfs => by
      rw [hηs] at hs
      have := tailMin 0 s (by simpa using hs)
      simp only [Nat.mul_zero, Nat.zero_add] at this
      linarith)]
    simp
  case cf =>
    intro k
    set μ := f (ξ (2 * k + 1)) with hμdef
    have hμ : 0 < μ := lt_of_lt_of_le hpos1 (by have := minle 0 k (by omega); simpa using this)
    rw [← hη0, total μ (2 * k + 1) (segOK (2 * k) μ hμ
      (fun e _ => by have := hL1 k; have := hL2 e; linarith)
      (fun o ho => minlt o k (by omega)))]
    have e : 2 * k + 1 = 2 * k + 1 := rfl
    rw [show η (2 * k + 1) = ξ (2 * k) from rfl]
    rw [tail_single f _ (ξ (2 * k + 1)) μ (hmono (by omega)).le rfl
      (fun s hs hne => (hmin k s hs hne).ne')]
    push_cast; ring
  case cg =>
    intro k μ h1 h2
    have hμ : 0 < μ := by
      have := minle 0 k (by omega); simp only [Nat.mul_zero, Nat.zero_add] at this; linarith
    rw [← hη0, total μ (2 * k + 2 + 1) (segOK (2 * k + 2) μ hμ
      (fun e _ => by
        have h3 := hL1 (k + 1); have := hL2 e
        have e' : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
        rw [e'] at h3; linarith)
      (fun o ho => lt_of_le_of_lt (minle o k (by omega)) h1))]
    rw [show η (2 * k + 2 + 1) = ξ (2 * k + 2) from rfl]
    rw [tail_empty f _ μ (fun s hs hfs => by
      have := tailMin (k + 1) s (by
        have e' : 2 * (k + 1) = 2 * k + 2 := by ring
        rw [e']; exact hs)
      have e' : 2 * (k + 1) + 1 = 2 * k + 3 := by ring
      rw [e'] at this; linarith)]
    push_cast; ring
  case ch =>
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    rw [← hη0, total L n (fun j hj => segOK n L hL (fun e _ => hL2 e) (fun o _ => hL1 o) j
      (Nat.lt_succ_of_lt hj))]
    exact le_self_add

lemma ident_max (f : ℝ → ℝ) (a x ζ S : ℝ) (hax : a ≤ x)
    (hx : ∀ s ∈ Ici a, s ≠ x → f s < f x) (hm : StrictMonoOn f (Icc a x))
    (hζa : a ≤ ζ) (hζS : ζ < S) (hζ : ∀ s ∈ Icc a S, s ≠ ζ → f s < f ζ) : ζ = x := by
  by_contra hne
  have h1 : f ζ < f x := hx ζ hζa hne
  rcases le_or_gt x S with hxS | hxS
  · have := hζ x ⟨hax, hxS⟩ (Ne.symm hne)
    linarith
  · have h2 : f ζ < f S :=
      hm ⟨hζa, (hζS.trans hxS).le⟩ ⟨hζa.trans hζS.le, hxS.le⟩ hζS
    have h3 := hζ S ⟨hζa.trans hζS.le, le_rfl⟩ hζS.ne'
    linarith

lemma ident_min (f : ℝ → ℝ) (a x ζ S : ℝ) (hax : a ≤ x)
    (hx : ∀ s ∈ Ici a, s ≠ x → f x < f s) (hm : StrictAntiOn f (Icc a x))
    (hζa : a ≤ ζ) (hζS : ζ < S) (hζ : ∀ s ∈ Icc a S, s ≠ ζ → f ζ < f s) : ζ = x := by
  by_contra hne
  have h1 : f x < f ζ := hx ζ hζa hne
  rcases le_or_gt x S with hxS | hxS
  · have := hζ x ⟨hax, hxS⟩ (Ne.symm hne)
    linarith
  · have h2 : f S < f ζ :=
      hm ⟨hζa, (hζS.trans hxS).le⟩ ⟨hζa.trans hζS.le, hxS.le⟩ hζS
    have h3 := hζ S ⟨hζa.trans hζS.le, le_rfl⟩ hζS.ne'
    linarith

theorem main (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515 ∧
      1.1822265 ≤ ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 ∧
      0.694366 ≤ ξ 1 ^ 2 * (-φ (ξ 1)) * Real.exp (w (ξ 1) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 1 ^ 2 * (-φ (ξ 1)) * Real.exp (w (ξ 1) / 2) / Real.sqrt (4 * Real.pi) ≤ 0.694367 ∧
      0.8306 ≤ ξ 2 ^ 2 * (-φ (ξ 2)) * Real.exp (w (ξ 2) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 2 ^ 2 * (-φ (ξ 2)) * Real.exp (w (ξ 2) / 2) / Real.sqrt (4 * Real.pi) ≤ 0.8308 ∧
      0.787992 ≤ ξ 3 ^ 2 * (-φ (ξ 3)) * Real.exp (w (ξ 3) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 3 ^ 2 * (-φ (ξ 3)) * Real.exp (w (ξ 3) / 2) / Real.sqrt (4 * Real.pi) ≤ 0.787995 ∧
      0.80091 ≤ ξ 4 ^ 2 * (-φ (ξ 4)) * Real.exp (w (ξ 4) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 4 ^ 2 * (-φ (ξ 4)) * Real.exp (w (ξ 4) / 2) / Real.sqrt (4 * Real.pi) ≤ 0.800916 ∧
      Tendsto (fun k => ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi))
        atTop (𝓝 (Real.sqrt (2 / Real.pi))) ∧
      (∀ μ : ℝ,
        ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi) < μ →
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ}.encard
          = 0) ∧
      {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) =
          ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi)}.encard = 1 ∧
      (∀ k : ℕ, ∀ μ : ℝ,
        ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi) < μ →
        μ < ξ (2 * k) ^ 2 * (-φ (ξ (2 * k))) * Real.exp (w (ξ (2 * k)) / 2) /
            Real.sqrt (4 * Real.pi) →
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ}.encard
          = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ,
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) =
          ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi)}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ μ : ℝ, 0 < μ →
        μ < ξ 1 ^ 2 * (-φ (ξ 1)) * Real.exp (w (ξ 1) / 2) / Real.sqrt (4 * Real.pi) →
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ}.encard
          = 1) ∧
      (∀ k : ℕ,
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) =
          ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi)}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, ∀ μ : ℝ,
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) < μ →
        μ < ξ (2 * k + 3) ^ 2 * (-φ (ξ (2 * k + 3))) * Real.exp (w (ξ (2 * k + 3)) / 2) /
            Real.sqrt (4 * Real.pi) →
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ}.encard
          = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) =
          Real.sqrt (2 / Real.pi)}.encard = ⊤ := by
  obtain ⟨ξ, hmono, htend, hlo, hhi, hmax0, hmin, hmax, hband, hlim, hinc0, hdec, hinc⟩ :=
    Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone w φ hw hφ0 hφ h0
  set f : ℝ → ℝ := fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)
    with hfdef
  -- restriction of the hypotheses to [0, S]
  have restr : ∀ S : ℝ, (∀ s ∈ Icc (0 : ℝ) S, HasDerivWithinAt w (φ s) (Icc 0 S) s) ∧
      ContinuousWithinAt φ (Icc 0 S) 0 ∧
      (∀ s ∈ Ioc (0 : ℝ) S,
        HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Icc 0 S) s) := by
    intro S
    refine ⟨fun s hs => (hw s hs.1).mono Icc_subset_Ici_self,
      hφ0.mono Icc_subset_Ici_self, fun s hs => (hφ s hs.1).mono Icc_subset_Ici_self⟩
  have hmax0' : ∀ s ∈ Ici (0 : ℝ), s ≠ ξ 0 → f s < f (ξ 0) := hmax0
  have hmin0 : ∀ s ∈ Ici (ξ 0), s ≠ ξ 1 → f (ξ 1) < f s := hmin 0
  have hmin1 : ∀ s ∈ Ici (ξ 2), s ≠ ξ 3 → f (ξ 3) < f s := hmin 1
  have hmax1 : ∀ s ∈ Ici (ξ 1), s ≠ ξ 2 → f s < f (ξ 2) := hmax 0
  have hmax2 : ∀ s ∈ Ici (ξ 3), s ≠ ξ 4 → f s < f (ξ 4) := hmax 1
  have hinc0' : StrictMonoOn f (Icc 0 (ξ 0)) := hinc0
  have hdec0 : StrictAntiOn f (Icc (ξ 0) (ξ 1)) := hdec 0
  have hdec1 : StrictAntiOn f (Icc (ξ 2) (ξ 3)) := hdec 1
  have hinc1 : StrictMonoOn f (Icc (ξ 1) (ξ 2)) := hinc 0
  have hinc2 : StrictMonoOn f (Icc (ξ 3) (ξ 4)) := hinc 1
  have l01 : ξ 0 ≤ ξ 1 := (hmono (by norm_num)).le
  have l12 : ξ 1 ≤ ξ 2 := (hmono (by norm_num)).le
  have l23 : ξ 2 ≤ ξ 3 := (hmono (by norm_num)).le
  have l34 : ξ 3 ≤ ξ 4 := (hmono (by norm_num)).le
  have hξ0 : 0 < ξ 0 := by linarith
  -- first maximum
  obtain ⟨y1, a1, b1, hy1, v01, v02⟩ :=
    Checked.Math.BonnorEbertMax.bonnor_ebert_max 7 (by norm_num) w φ (restr 7).1 (restr 7).2.1
      (restr 7).2.2 h0
  have e1 : y1 = ξ 0 := ident_max f 0 (ξ 0) y1 7 hξ0.le hmax0' hinc0' (by linarith) (by linarith) hy1
  subst e1
  -- first minimum
  obtain ⟨z1, z2, a1', b1', a2, b2, hz1, hz2, v11, v12, -, -⟩ :=
    Checked.Math.BonnorEbertMin.bonnor_ebert_min 150 (by norm_num) w φ (restr 150).1
      (restr 150).2.1 (restr 150).2.2 h0
  have e1' : z1 = ξ 0 :=
    ident_max f 0 (ξ 0) z1 150 hξ0.le hmax0' hinc0' (by linarith) (by linarith) hz1
  subst e1'
  have e2 : z2 = ξ 1 :=
    ident_min f (ξ 0) (ξ 1) z2 150 l01 hmin0 hdec0 (by linarith) (by linarith) hz2
  subst e2
  -- second maximum
  obtain ⟨p1, p2, p3, c1, d1, c2, d2, c3, d3, hp1, hp2, hp3, v21, v22, -, -⟩ :=
    Checked.Math.BonnorEbertMax2.bonnor_ebert_second_max 2000 (by norm_num) w φ (restr 2000).1
      (restr 2000).2.1 (restr 2000).2.2 h0
  have f1 : p1 = ξ 0 :=
    ident_max f 0 (ξ 0) p1 2000 hξ0.le hmax0' hinc0' (by linarith) (by linarith) hp1
  subst f1
  have f2 : p2 = ξ 1 :=
    ident_min f (ξ 0) (ξ 1) p2 2000 l01 hmin0 hdec0 (by linarith) (by linarith) hp2
  subst f2
  have f3 : p3 = ξ 2 :=
    ident_max f (ξ 1) (ξ 2) p3 2000 l12 hmax1 hinc1 (by linarith) (by linarith) hp3
  subst f3
  -- second minimum
  obtain ⟨q1, q2, q3, q4, g1, k1, g2, k2, g3, k3, g4, k4, hq1, hq2, hq3, hq4, v31, v32, -, -⟩ :=
    Checked.Math.BonnorEbertMin2.bonnor_ebert_second_min 20000 (by norm_num) w φ (restr 20000).1
      (restr 20000).2.1 (restr 20000).2.2 h0
  have g1e : q1 = ξ 0 :=
    ident_max f 0 (ξ 0) q1 20000 hξ0.le hmax0' hinc0' (by linarith) (by linarith) hq1
  subst g1e
  have g2e : q2 = ξ 1 :=
    ident_min f (ξ 0) (ξ 1) q2 20000 l01 hmin0 hdec0 (by linarith) (by linarith) hq2
  subst g2e
  have g3e : q3 = ξ 2 :=
    ident_max f (ξ 1) (ξ 2) q3 20000 l12 hmax1 hinc1 (by linarith) (by linarith) hq3
  subst g3e
  have g4e : q4 = ξ 3 :=
    ident_min f (ξ 2) (ξ 3) q4 20000 l23 hmin1 hdec1 (by linarith) (by linarith) hq4
  subst g4e
  -- third maximum
  obtain ⟨r1, r2, r3, r4, r5, m1, n1, m2, n2, m3, n3, m4, n4, m5, n5, hr1, hr2, hr3, hr4, hr5,
      v41, v42, -, -⟩ :=
    Checked.Math.BonnorEbertMax3.bonnor_ebert_third_max 300000 (by norm_num) w φ
      (restr 300000).1 (restr 300000).2.1 (restr 300000).2.2 h0
  have h1e : r1 = ξ 0 :=
    ident_max f 0 (ξ 0) r1 300000 hξ0.le hmax0' hinc0' (by linarith) (by linarith) hr1
  subst h1e
  have h2e : r2 = ξ 1 :=
    ident_min f (ξ 0) (ξ 1) r2 300000 l01 hmin0 hdec0 (by linarith) (by linarith) hr2
  subst h2e
  have h3e : r3 = ξ 2 :=
    ident_max f (ξ 1) (ξ 2) r3 300000 l12 hmax1 hinc1 (by linarith) (by linarith) hr3
  subst h3e
  have h4e : r4 = ξ 3 :=
    ident_min f (ξ 2) (ξ 3) r4 300000 l23 hmin1 hdec1 (by linarith) (by linarith) hr4
  subst h4e
  have h5e : r5 = ξ 4 :=
    ident_max f (ξ 3) (ξ 4) r5 300000 l34 hmax2 hinc2 (by linarith) (by linarith) hr5
  subst h5e
  -- continuity and the counting theorem
  have hwc : ContinuousOn w (Ici 0) := fun s hs => (hw s hs).continuousWithinAt
  have hφc : ContinuousOn φ (Ici 0) := by
    intro s hs
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h | h
    · rw [← h]; exact hφ0
    · exact (hφ s h).continuousWithinAt
  have hfc : ContinuousOn f (Ici 0) := by
    simp only [hfdef]
    fun_prop
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hpos1 : 0 < f (ξ 1) := by
    have : (0.694366 : ℝ) ≤ f (ξ 1) := v11
    linarith
  have hL : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨Ca, Cb, Cc, Cd, Ce, Cf, Cg, Ch⟩ :=
    count_abstract f ξ (Real.sqrt (2 / Real.pi)) hL hfc hf0 hmono hξ0 hpos1 hmax0' hmin hmax
      hband hinc0' hdec hinc
  exact ⟨ξ, hmono, htend, hlo, hhi, v01, v02, v11, v12, v21, v22, v31, v32, v41, v42,
    hlim.comp htend, Ca, Cb, Cc, Cd, Ce, Cf, Cg, Ch⟩

end Work.Math.BonnorEbertCountMain
