import Work.FalknerSkan.CroccoWindow
import Work.Hiemenz.HExMono
import Work.Homann.HmExMono

/-!
# The monotone solution: existence and one wall shear (Hiemenz, Homann)

Frozen statements (run 2026-11-08T1028Z), before any proof; companions of
`Work.FalknerSkan.MonotoneWindow`. Hiemenz: f''' + f f'' + 1 − f'² = 0; Homann:
f''' + 2 f f'' + 1 − f'² = 0; f(0) = f'(0) = 0, f'(η) → 1 as η → ∞; first-order system
f' = p, p' = q with derivatives within [0, ∞).

* `hiemenz_exists_monotone`, `homann_exists_monotone`: there is a solution with q = f'' > 0 on
  [0, ∞) and wall shear in the certified window (the existence theorems `hiemenz_exists`,
  `homann_exists` do not say q > 0).
* `hiemenz_monotone_same_wall_shear`, `homann_monotone_same_wall_shear`: any two solutions with
  q > 0 on [0, ∞) have the same wall shear q(0).

Planned proofs: the shooting construction of `Checked.Hiemenz.HExAssemble.exists_bvp` (resp. the
Homann copy) already proves q > 0 inside `HExLimit.no_event`; expose it. Same wall shear: the
Crocco comparison of `Work.FalknerSkan.CroccoWindow` between the two solutions.
-/

namespace Work.FalknerSkan.MonotoneExists
open Set Filter Topology

/-- Two monotone boundary-value solutions (coefficient k ≥ 0): the first wall shear is not
smaller than the second's. Crocco comparison of the two solutions. -/
theorem not_lt_wall {k : ℝ} (hk : 0 ≤ k) {f p q f₂ p₂ q₂ : ℝ → ℝ}
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(k * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(k * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) : ¬ q 0 < q₂ 0 := by
  intro hlt
  have hD0 : 0 < q₂ 0 - q 0 := by linarith
  obtain ⟨ηs, hηs, hqs⟩ := Work.FalknerSkan.CroccoWindow.exists_q_lt hp₂ hp₂0 hlim₂ hpos₂ hD0
  have hηs0 : (0 : ℝ) ≤ ηs := hηs
  have ht1 : p₂ ηs < 1 := Work.FalknerSkan.CroccoWindow.p_lt_one hp₂ hlim₂ hpos₂ ηs hηs
  obtain ⟨E, hE1, hEu⟩ : ∃ E, 1 ≤ E ∧ p₂ ηs < p E := by
    obtain ⟨E, hE⟩ := ((hlim.eventually (lt_mem_nhds ht1)).and (eventually_ge_atTop (1 : ℝ))).exists
    exact ⟨E, hE.2, hE.1⟩
  have hE0 : 0 < E := by linarith
  set E₂ := ηs + 1 with hE₂
  have hE₂0 : 0 < E₂ := by linarith
  have hsubE : Icc 0 E ⊆ Ici 0 := fun x hx => hx.1
  have hsubE₂ : Icc 0 E₂ ⊆ Ici 0 := fun x hx => hx.1
  obtain ⟨ψ1, hψ1a, hψ1b, cz1, cF1, dF1, dz1⟩ := Work.FalknerSkan.CroccoMap.crocco (k := k) hE0
    (fun η hη => (hf η (hsubE hη)).mono hsubE) (fun η hη => (hp η (hsubE hη)).mono hsubE)
    (fun η hη => (hq η (hsubE hη)).mono hsubE) hp0 (fun η hη => hpos η hη.1)
  obtain ⟨ψ2, hψ2a, hψ2b, cz2, cF2, dF2, dz2⟩ := Work.FalknerSkan.CroccoMap.crocco (k := k) hE₂0
    (fun η hη => (hf₂ η (hsubE₂ hη)).mono hsubE₂) (fun η hη => (hp₂ η (hsubE₂ hη)).mono hsubE₂)
    (fun η hη => (hq₂ η (hsubE₂ hη)).mono hsubE₂) hp₂0 (fun η hη => hpos₂ η hη.1)
  have hm₂ := Work.FalknerSkan.CroccoWindow.smono_Ici hp₂ hpos₂
  have hlt₂ : p₂ ηs < p₂ E₂ := hm₂ hηs (show (0 : ℝ) ≤ E₂ by linarith) (by linarith)
  set L := min (p E) (p₂ E₂) with hL
  have hL1 : L ≤ 1 := (min_le_left _ _).trans
    (Work.FalknerSkan.CroccoWindow.p_lt_one hp hlim hpos E hE0.le).le
  have hs1 : Ico 0 L ⊆ Ico 0 (p E) := Ico_subset_Ico_right (min_le_left _ _)
  have hs2 : Ico 0 L ⊆ Ico 0 (p₂ E₂) := Ico_subset_Ico_right (min_le_right _ _)
  have hs1' : Ioo 0 L ⊆ Ioo 0 (p E) := Ioo_subset_Ioo_right (min_le_left _ _)
  have hs2' : Ioo 0 L ⊆ Ioo 0 (p₂ E₂) := Ioo_subset_Ioo_right (min_le_right _ _)
  have hψ10 : ψ1 0 = 0 := by
    have := hψ1b 0 ⟨le_rfl, hE0⟩; rwa [hp0] at this
  have hψ20 : ψ2 0 = 0 := by
    have := hψ2b 0 ⟨le_rfl, hE₂0⟩; rwa [hp₂0] at this
  have hcmp := Work.FalknerSkan.CroccoCompare.compare (k := k) (L := L)
    (z₁ := fun t => q (ψ1 t)) (z₂ := fun t => q₂ (ψ2 t))
    (F₁ := fun t => f (ψ1 t)) (F₂ := fun t => f₂ (ψ2 t)) hk hL1
    (fun t ht => hpos _ (hψ1a t (hs1 ht)).1.1) (fun t ht => hpos₂ _ (hψ2a t (hs2 ht)).1.1)
    (cz1.mono hs1) (cz2.mono hs2) (cF1.mono hs1) (cF2.mono hs2)
    (fun t ht => dF1 t (hs1' ht)) (fun t ht => dF2 t (hs2' ht))
    (fun t ht => dz1 t (hs1' ht)) (fun t ht => dz2 t (hs2' ht))
    (by simp only [hψ10, hψ20, hf0, hf₂0])
    (by simp only [hψ10, hψ20]; exact hlt)
  have hts : p₂ ηs ∈ Ico 0 L := by
    refine ⟨?_, lt_min hEu hlt₂⟩
    have := hm₂.monotoneOn (Set.mem_Ici.2 le_rfl) hηs hηs0
    rwa [hp₂0] at this
  have key := hcmp (p₂ ηs) hts
  simp only [hψ10, hψ20] at key
  rw [hψ2b ηs ⟨hηs0, by linarith⟩] at key
  have hq1 : 0 < q (ψ1 (p₂ ηs)) := hpos _ (hψ1a _ (hs1 hts)).1.1
  linarith

/-- Hiemenz stagnation-point flow: there is a solution of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q − 1 + p², one-sided at 0) with
f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, q > 0 on [0, ∞), and wall shear q(0) = f''(0) strictly
between 1.2325876568 and 1.2325876569. -/
theorem hiemenz_exists_monotone : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
    1.2325876568 < q 0 ∧ q 0 < 1.2325876569 := by
  exact Work.Hiemenz.HExMono.exists_bvp_pos

/-- Homann axisymmetric stagnation-point flow: there is a solution of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (f has derivative p, p has derivative q, q has derivative −2 f q − 1 + p², one-sided at
0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞, q > 0 on [0, ∞), and wall shear q(0) = f''(0)
strictly between 1.3119376938 and 1.3119376939. -/
theorem homann_exists_monotone : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
    1.3119376938 < q 0 ∧ q 0 < 1.3119376939 := by
  exact Work.Homann.HmExMono.exists_bvp_pos

/-- Hiemenz stagnation-point flow: any two solutions of f''' + f f'' + 1 − f'² = 0 on [0, ∞)
(derivatives one-sided at 0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on [0, ∞) have
the same wall shear q(0) = f''(0). -/
theorem hiemenz_monotone_same_wall_shear (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q 0 = q₂ 0 := by
  have hq1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 * f η * q η) - 1 + p η ^ 2) (Ici 0) η :=
    fun η hη => (hq η hη).congr_deriv (by ring)
  have hq₂1 : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(1 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η :=
    fun η hη => (hq₂ η hη).congr_deriv (by ring)
  exact le_antisymm
    (not_lt.1 (not_lt_wall zero_le_one hf₂ hp₂ hq₂1 hf₂0 hp₂0 hlim₂ hpos₂ hf hp hq1 hf0 hp0 hlim hpos))
    (not_lt.1 (not_lt_wall zero_le_one hf hp hq1 hf0 hp0 hlim hpos hf₂ hp₂ hq₂1 hf₂0 hp₂0 hlim₂ hpos₂))

/-- Homann axisymmetric stagnation-point flow: any two solutions of f''' + 2 f f'' + 1 − f'² = 0
on [0, ∞) (derivatives one-sided at 0) with f(0) = 0, p(0) = 0, p(η) → 1 as η → ∞ and q > 0 on
[0, ∞) have the same wall shear q(0) = f''(0). -/
theorem homann_monotone_same_wall_shear (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(2 * f η * q η) - 1 + p η ^ 2) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(2 * f₂ η * q₂ η) - 1 + p₂ η ^ 2) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q 0 = q₂ 0 := by
  exact le_antisymm
    (not_lt.1 (not_lt_wall zero_le_two hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂ hf hp hq hf0 hp0 hlim hpos))
    (not_lt.1 (not_lt_wall zero_le_two hf hp hq hf0 hp0 hlim hpos hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂))

end Work.FalknerSkan.MonotoneExists
