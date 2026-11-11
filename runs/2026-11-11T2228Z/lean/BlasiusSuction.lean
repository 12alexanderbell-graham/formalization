import Checked.Blasius.BExFlow
import Checked.Blasius.BExBounds
import Checked.Blasius.Blasius
import Checked.FalknerSkan.FalknerSkan
import Checked.Trust.NonVacuity
/-! Scratch (run 2026-11-11T2228Z, auditor role): the wall condition `f 0 = 0` is needed in
`Checked.Blasius.blasius_wall_shear` and `Checked.FalknerSkan.fs_zero_wall_shear`. Witness: the
Blasius solution with suction, from the wall state (1, 0, 1), scaled so that p → 1. -/

namespace Checked.Trust.NCH
open Set Filter Topology Checked.Blasius.BExBase

/-- A solution of the clamped Blasius system on [0, T] from (1, 0, 1). -/
theorem local_sol1 (T : ℝ) (hT : 0 < T) : ∃ α : ℝ → ℝ × ℝ × ℝ, α 0 = (1, 0, 1) ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt α (vF t (α t)) (Icc 0 T) t := by
  set L : ℝ := 4 * T + 5 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof vF (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      ((1 : ℝ), (0 : ℝ), (1 : ℝ)) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (4 * T + 2)) :=
    { lipschitzOnWith := fun t ht => (Checked.Blasius.BExFlow.lip ht).lipschitzOnWith
      continuousOn := fun x _ => (Checked.Blasius.BExFlow.cont x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact Checked.Blasius.BExFlow.norm_le ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- A global solution of the clamped Blasius system from (1, 0, 1). -/
theorem exists_flow1 : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = (1, 0, 1) ∧
    ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vF t (Y t)) (Ici 0) t := by
  have hex : ∀ n : ℕ, ∃ α : ℝ → ℝ × ℝ × ℝ, α 0 = (1, 0, 1) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), HasDerivWithinAt α (vF t (α t)) (Icc 0 ((n : ℝ) + 1)) t :=
    fun n => local_sol1 _ (by positivity)
  choose sol hsol0 hsol using hex
  have hag : ∀ k n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((k : ℝ) + 1), s ≤ (n : ℝ) + 1 → sol k s = sol n s := by
    intro k n s hs hsn
    rcases le_total k n with hkn | hnk
    · exact Checked.Blasius.BExFlow.agree (by positivity)
        (by exact_mod_cast (Nat.add_le_add_right hkn 1))
        (sol k) (sol n) ((hsol0 k).trans (hsol0 n).symm) (hsol k) (hsol n) hs
    · exact (Checked.Blasius.BExFlow.agree (by positivity)
        (by exact_mod_cast (Nat.add_le_add_right hnk 1))
        (sol n) (sol k) ((hsol0 n).trans (hsol0 k).symm) (hsol n) (hsol k) ⟨hs.1, hsn⟩).symm
  refine ⟨fun t => sol (⌈t⌉₊) t, ?_, fun t ht => ?_⟩
  · simp [hsol0]
  · set n := ⌈t⌉₊ with hn
    have htn : t ≤ (n : ℝ) := Nat.le_ceil t
    have hlt : t < (n : ℝ) + 1 := by linarith
    have heq : ∀ s ∈ Ico (0 : ℝ) ((n : ℝ) + 1), sol (⌈s⌉₊) s = sol n s := by
      intro s hs
      refine hag _ n s ⟨hs.1, ?_⟩ hs.2.le
      have := Nat.le_ceil s; linarith
    have hnhds : Ico (0 : ℝ) ((n : ℝ) + 1) ∈ nhdsWithin t (Ici 0) := by
      have : Iio ((n : ℝ) + 1) ∈ nhds t := Iio_mem_nhds hlt
      have h2 := inter_mem_nhdsWithin (Ici (0 : ℝ)) this
      refine Filter.mem_of_superset h2 ?_
      intro s hs; exact ⟨hs.1, hs.2⟩
    have hd := (hsol n t ⟨ht, hlt.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset hnhds (fun s hs => ⟨hs.1, hs.2.le⟩))
    have ht0 : sol (⌈t⌉₊) t = sol n t := rfl
    simp only
    rw [ht0]
    refine hd.congr_of_eventuallyEq ?_ (heq t ⟨ht, hlt⟩)
    exact Filter.mem_of_superset hnhds (fun s hs => heq s hs)

open Checked.Blasius.BExBounds in
/-- Along the clamped flow from (1, 0, 1) every clamp is inactive, and p increases to a limit
in (0, 2]: f ≥ 1, so p + 2q is non-increasing (derivative q(1 − f) ≤ 0). -/
theorem suction (Y : ℝ → ℝ × ℝ × ℝ) (h0 : Y 0 = (1, 0, 1))
    (hY : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Y (vF t (Y t)) (Ici 0) t) :
    Checked.Blasius.BTail.IsSol (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) ∧
    ∃ α : ℝ, 0 < α ∧ α ≤ 2 ∧ Tendsto (fun t => (Y t).2.1) atTop (𝓝 α) := by
  set g : ℝ → ℝ := fun t => (Y t).1 with hgdef
  set p : ℝ → ℝ := fun t => (Y t).2.1 with hpdef
  set q : ℝ → ℝ := fun t => (Y t).2.2 with hqdef
  have dg : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt g (cl 4 (p t)) (Ici 0) t :=
    fun t ht => fst_derivW (hY t ht)
  have dp : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt p (cl 2 (q t)) (Ici 0) t :=
    fun t ht => fst_derivW (snd_derivW (hY t ht))
  have dq : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt q (-(cl (4 * max t 0 + 1) (g t) * cl 2 (q t) / 2)) (Ici 0) t :=
    fun t ht => snd_derivW (snd_derivW (hY t ht))
  have g0 : g 0 = 1 := by simp [hgdef, h0]
  have p0 : p 0 = 0 := by simp [hpdef, h0]
  have q0 : q 0 = 1 := by simp [hqdef, h0]
  have cg : ContinuousOn g (Ici 0) := fun t ht => (dg t ht).continuousWithinAt
  have cp : ContinuousOn p (Ici 0) := fun t ht => (dp t ht).continuousWithinAt
  have cq : ContinuousOn q (Ici 0) := fun t ht => (dq t ht).continuousWithinAt
  have mx : ∀ t : ℝ, 0 ≤ 4 * max t 0 + 1 := fun t => by
    have := le_max_right t 0; linarith
  -- q > 0
  have zb : ∀ t₁ : ℝ, 0 ≤ t₁ → q t₁ = 0 → q 0 = 0 := by
    intro t₁ ht₁ hz
    have h := ODE_solution_unique_of_mem_Icc_left
      (v := fun t y => -(cl (4 * max t 0 + 1) (g t) * cl 2 y / 2))
      (s := fun _ => univ) (K := Real.toNNReal ((4 * t₁ + 1) / 2)) (a := 0) (b := t₁) (f := q)
      (g := fun _ => 0)
      (fun t ht => lipcl ((cl_abs (mx t)).trans (by
        have := max_le ht.2 ht₁; linarith)))
      (cq.mono Icc_subset_Ici_self)
      (fun t ht => ((dq t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)).hasDerivWithinAt)
      (fun _ _ => mem_univ _) continuousOn_const
      (fun t _ => by
        rw [show cl 2 (0 : ℝ) = 0 from cl_of_abs_le (by norm_num)]
        simp only [mul_zero, zero_div, neg_zero]
        exact hasDerivWithinAt_const _ _ _)
      (fun _ _ => mem_univ _) hz
    exact h ⟨le_rfl, ht₁⟩
  have qpos : ∀ t ∈ Ici (0 : ℝ), 0 < q t := by
    intro t ht
    by_contra hn
    push Not at hn
    obtain ⟨u, hu, hqu⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ t from ht)
      (cq.mono Icc_subset_Ici_self) (show (0 : ℝ) ∈ Icc (q t) (q 0) from ⟨hn, by rw [q0]; norm_num⟩)
    have := zb u hu.1 hqu
    rw [q0] at this
    norm_num at this
  have pmono : MonotoneOn p (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => cl 2 (q t)) cp ?_ ?_
    · intro x hx; rw [interior_Ici] at hx ⊢
      exact ((dp x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx
      exact cl_nonneg (by norm_num) (qpos x (mem_Ici.2 (le_of_lt hx))).le
  have z0 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.2 le_rfl
  have pnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ p t := fun t ht => p0 ▸ pmono z0 ht ht
  have gmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => cl 4 (p t)) cg ?_ ?_
    · intro x hx; rw [interior_Ici] at hx ⊢
      exact ((dg x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx
      exact cl_nonneg (by norm_num) (pnn x (mem_Ici.2 (le_of_lt hx)))
  have gge : ∀ t ∈ Ici (0 : ℝ), 1 ≤ g t := fun t ht => g0 ▸ gmono z0 ht ht
  have qanti : AntitoneOn q (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (f' := fun t => -(cl (4 * max t 0 + 1) (g t) * cl 2 (q t) / 2)) cq ?_ ?_
    · intro x hx; rw [interior_Ici] at hx ⊢
      exact ((dq x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx
      have h1 := cl_nonneg (mx x) (by linarith [gge x (mem_Ici.2 (le_of_lt hx))] : 0 ≤ g x)
      have h2 := cl_nonneg (by norm_num : (0 : ℝ) ≤ 2) (qpos x (mem_Ici.2 (le_of_lt hx))).le
      have := mul_nonneg h1 h2
      linarith
  have qle1 : ∀ t ∈ Ici (0 : ℝ), q t ≤ 1 := fun t ht => q0 ▸ qanti z0 ht ht
  have gle : ∀ t ∈ Ici (0 : ℝ), g t ≤ 4 * t + 1 := by
    have hA : AntitoneOn (fun t => g t - 4 * t) (Ici 0) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
        (f' := fun t => cl 4 (p t) - 4 * 1) (cg.sub (by fun_prop)) ?_ ?_
      · intro x hx; rw [interior_Ici] at hx ⊢
        exact (((dg x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).sub
          ((hasDerivAt_id' x).const_mul 4)).hasDerivWithinAt
      · intro x hx
        have := cl_le (c := 4) (y := p x) (by norm_num)
        linarith
    intro t ht
    have := hA z0 ht ht
    simp only [g0] at this
    linarith
  have clq : ∀ t ∈ Ici (0 : ℝ), cl 2 (q t) = q t := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [qpos t ht], by linarith [qle1 t ht]⟩)
  have clg : ∀ t ∈ Ici (0 : ℝ), cl (4 * max t 0 + 1) (g t) = g t := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [gge t ht, mx t], by
      have := gle t ht; have := le_max_left t 0; linarith⟩)
  -- p + 2 q is non-increasing
  have hW : AntitoneOn (fun t => p t + 2 * q t) (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (f' := fun t => cl 2 (q t) + 2 * -(cl (4 * max t 0 + 1) (g t) * cl 2 (q t) / 2))
      (cp.add (continuousOn_const.mul cq)) ?_ ?_
    · intro x hx; rw [interior_Ici] at hx ⊢
      exact (((dp x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).add
        (((dq x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).const_mul 2)).hasDerivWithinAt
    · intro x hx; rw [interior_Ici] at hx
      have hx' : x ∈ Ici (0 : ℝ) := mem_Ici.2 (le_of_lt hx)
      rw [clq x hx', clg x hx']
      nlinarith [gge x hx', qpos x hx']
  have ple : ∀ t ∈ Ici (0 : ℝ), p t ≤ 2 := by
    intro t ht
    have := hW z0 ht ht
    simp only [p0, q0] at this
    linarith [qpos t ht]
  have clp : ∀ t ∈ Ici (0 : ℝ), cl 4 (p t) = p t := fun t ht =>
    cl_of_abs_le (abs_le.2 ⟨by linarith [pnn t ht], by linarith [ple t ht]⟩)
  refine ⟨⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_⟩, ?_⟩
  · have h := dg η hη; rwa [clp η hη] at h
  · have h := dp η hη; rwa [clq η hη] at h
  · have h := dq η hη; rwa [clq η hη, clg η hη] at h
  · set pt : ℝ → ℝ := fun t => p (max t 0) with hpt
    have hmono : Monotone pt := fun a b hab =>
      pmono (mem_Ici.2 (le_max_right a 0)) (mem_Ici.2 (le_max_right b 0)) (max_le_max hab le_rfl)
    have hbdd : BddAbove (range pt) :=
      ⟨2, by rintro _ ⟨t, rfl⟩; exact ple (max t 0) (mem_Ici.2 (le_max_right _ _))⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    refine ⟨⨆ i, pt i, ?_, ciSup_le fun t => ple (max t 0) (mem_Ici.2 (le_max_right _ _)),
      hlim.congr' ((eventually_ge_atTop 0).mono fun t ht => ?_)⟩
    · have hsm : StrictMonoOn p (Ici 0) := by
        refine strictMonoOn_of_deriv_pos (convex_Ici 0) cp (fun x hx => ?_)
        rw [interior_Ici] at hx
        rw [((dp x (mem_Ici.2 (le_of_lt hx))).hasDerivAt (Ici_mem_nhds hx)).deriv]
        exact cl_pos (by norm_num) (qpos x (mem_Ici.2 (le_of_lt hx)))
      have h1 : p 0 < p 1 := hsm z0 (mem_Ici.2 (by norm_num)) (by norm_num)
      have h2 : pt 1 ≤ ⨆ i, pt i := le_ciSup hbdd 1
      have h3 : pt 1 = p 1 := by simp [hpt]
      linarith
    · simp [hpt, max_eq_left ht]

/-- The Blasius problem with suction: a solution of f''' + f f''/2 = 0 on [0, ∞) with p(0) = 0,
p → 1, f(0) = 1/c and q(0) = 1/c³ for some c with 0 < c and c² ≤ 2. -/
theorem suction_profile : ∃ c : ℝ, 0 < c ∧ c ^ 2 ≤ 2 ∧ ∃ f p q : ℝ → ℝ,
    Checked.Blasius.BTail.IsSol f p q ∧ f 0 = 1 / c ∧ p 0 = 0 ∧ q 0 = 1 / c ^ 3 ∧
    Tendsto p atTop (𝓝 1) := by
  obtain ⟨Y, hY0, hY⟩ := exists_flow1
  obtain ⟨S, α, hα, hα2, hlim⟩ := suction Y hY0 hY
  set c : ℝ := Real.sqrt α with hcdef
  have hc : 0 < c := Real.sqrt_pos.2 hα
  have hc2 : c ^ 2 = α := Real.sq_sqrt hα.le
  have S' := Checked.Blasius.BTail.scale S hc
  refine ⟨c, hc, hc2 ▸ hα2, fun t => (Y (t / c)).1 / c, fun t => (Y (t / c)).2.1 / c ^ 2,
    fun t => (Y (t / c)).2.2 / c ^ 3, S', ?_, ?_, ?_, ?_⟩
  · simp [hY0]
  · simp [hY0]
  · simp [hY0]
  · have h := (hlim.comp (tendsto_id.atTop_div_const hc)).div_const (c ^ 2)
    have e : α / c ^ 2 = 1 := by rw [hc2, div_self hα.ne']
    rw [e] at h
    exact h

/-- c³ ≤ 2√2 < 2.83 when c² ≤ 2. -/
theorem cube_le {c : ℝ} (hc : 0 < c) (h2 : c ^ 2 ≤ 2) : c ^ 3 < 283 / 100 := by
  have hc1 : c < 1.4143 := by nlinarith
  nlinarith

/-- Blasius: the wall condition f(0) = 0 is needed: the suction profile has f(0) = 1/c ≠ 0 and
wall shear 1/c³ > 100/283 > 0.33205733621520. -/
theorem blasius_wall_shear_h4 : necessity% Checked.Blasius.blasius_wall_shear 4 := by
  obtain ⟨c, hc, hc2, f, p, q, S, -, hp0, hq0, hl⟩ := suction_profile
  refine ⟨f, p, q, S.hf, S.hp, S.hq, hp0, hl, ?_⟩
  rintro ⟨-, h⟩
  rw [hq0] at h
  have h3 := cube_le hc hc2
  have hc3 : 0 < c ^ 3 := by positivity
  rw [div_le_iff₀ hc3] at h
  nlinarith

/-- Falkner–Skan β = 0: the wall condition f(0) = 0 is needed: the suction profile in the
β = 0 scaling (factor √2/2) has f(0) = (√2/2)/c ≠ 0 and wall shear √2/c³ > 0.4696. -/
theorem fs_zero_wall_shear_h4 : necessity% Checked.FalknerSkan.fs_zero_wall_shear 4 := by
  obtain ⟨c, hc, hc2, f, p, q, S, -, hp0, hq0, hl⟩ := suction_profile
  set k : ℝ := Real.sqrt 2 / 2 with hk
  have hs := Checked.FalknerSkan.FSScale.lt_sqrt2
  have hs' := Checked.FalknerSkan.FSScale.sqrt2_lt
  have hk0 : 0 < k := by positivity
  have hk2 : k ^ 2 = 1 / 2 := by
    rw [hk, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(1 / 2 * f η * q η) - 0 * (1 - p η ^ 2))
      (Ici 0) η := fun η hη => (S.hq η hη).congr_deriv (by ring)
  obtain ⟨A, B, C⟩ := Checked.FalknerSkan.FSScale.scale hk0 S.hf S.hp hq'
  refine ⟨_, _, _, A, B, fun s hs => (C s hs).congr_deriv (by rw [hk2]; ring), by simp [hp0],
    Checked.FalknerSkan.FSScale.scale_lim hk0 hl, ?_⟩
  rintro ⟨-, h⟩
  simp only [zero_div, hq0] at h
  have h3 := cube_le hc hc2
  have hc3 : 0 < c ^ 3 := by positivity
  rw [div_div, div_le_iff₀ (by positivity)] at h
  nlinarith

end Checked.Trust.NCH
