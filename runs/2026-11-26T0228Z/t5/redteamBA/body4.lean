/-! BA attempt 6: Gelfand headline. Closure named `Checked`, R := True, the proof of `bound_no_radial` copied into the
closure (its own lemmas are used as constants), with the bound variable threaded into the last step. -/
open Set Filter Topology Metric InnerProductSpace Laplacian
open scoped Interval
open Checked.Math.GSymFree Checked.Math.GRadialPoisson

namespace Bench
namespace SecondReading
def Rtrue : Prop := True
end SecondReading

theorem _root_.Checked : SecondReading.Rtrue ↔ type_of% Checked.Math.GelfandPDEBound.gelfand_pde_bound := by
  refine ⟨fun rr lam u hu hc hb hpde => ?_, fun _ => trivial⟩
  rcases le_or_gt lam 0 with hl | hlam
  · linarith
  have hΔu : ∀ x ∈ ball (0:EuclideanSpace ℝ (Fin 3)) 1, Δ u x ≤ 0 := fun x hx => by
    have := hpde x hx
    have := mul_pos hlam (Real.exp_pos (u x))
    linarith
  have hu0 := Checked.Math.GMaxPrinciple.superharmonic_nonneg u hu hc (fun x hx => (hb x hx).ge) hΔu
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0:EuclideanSpace ℝ (Fin 3)) 1).exists_isMaxOn
    ⟨0, mem_closedBall_self zero_le_one⟩ hc
  have huM : ∀ x ∈ closedBall (0:EuclideanSpace ℝ (Fin 3)) 1, u x ≤ u x₀ := fun x hx => hmax hx
  set M := u x₀ with hMdef
  set B := lam * Real.exp M with hBdef
  have hB : 0 < B := mul_pos hlam (Real.exp_pos M)
  have hit := gsf_iter hlam hu hc hb hpde hu0 huM
  have hMn : ∀ n, ∀ t ∈ Icc (0:ℝ) 1, gsf_w lam n t ≤ M := fun n => gsf_le_of_ball (hit n).2.2 huM
  have hsrc := fun n => gsf_src hlam hB.le (hMn n) (hit n).1 (hit n).2.1
  have hmono := gsf_mono hlam (fun n => (hsrc n).1)
  set W : ℝ → ℝ := fun r => ⨆ n, gsf_w lam n r with hWdef
  have hlim : ∀ r ∈ Icc (0:ℝ) 1, Tendsto (fun n => gsf_w lam n r) atTop (𝓝 (W r)) :=
    fun r hr => tendsto_atTop_ciSup (monotone_nat_of_le_succ fun n => hmono n r hr)
      ⟨M, by rintro _ ⟨n, rfl⟩; exact hMn n r hr⟩
  have h01 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hWM : ∀ r ∈ Icc (0:ℝ) 1, W r ≤ M := fun r hr =>
    le_of_tendsto' (hlim r hr) fun n => hMn n r hr
  have hWlip : ∀ r ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, |W r - W s| ≤ B * |r - s| :=
    fun r hr s hs => le_of_tendsto' (((hlim r hr).sub (hlim s hs)).abs) fun n => (hit n).1 r hr s hs
  have hWq : ∀ r ∈ Icc (0:ℝ) 1, |W r - W 0| ≤ B * r ^ 2 :=
    fun r hr => le_of_tendsto' (((hlim r hr).sub (hlim 0 h01)).abs) fun n => (hit n).2.1 r hr
  obtain ⟨hHc, hHl, -⟩ := gsf_src hlam hB.le hWM hWlip hWq
  set H : ℝ → ℝ := fun t => lam * Real.exp (W (gsf_c t)) with hHdef
  have hFlim : ∀ t, Tendsto (fun n => lam * Real.exp (gsf_w lam n (gsf_c t))) atTop (𝓝 (H t)) :=
    fun t => ((Real.continuous_exp.tendsto _).comp (hlim _ (gsf_c_mem t))).const_mul lam
  have heq : ∀ r ∈ Icc (0:ℝ) 1, W r = P H r := fun r hr => by
    have h1 : Tendsto (fun n => gsf_w lam (n + 1) r) atTop (𝓝 (W r)) :=
      (hlim r hr).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => gsf_w lam (n + 1) r) atTop (𝓝 (P H r)) := by
      simp only [gsf_w_succ]
      exact gsf_P_tendsto (F := fun n t => lam * Real.exp (gsf_w lam n (gsf_c t)))
        (fun n => (hsrc n).1) (fun n => (hsrc n).2.2) hFlim r
    exact tendsto_nhds_unique h1 h2
  obtain ⟨l1, l2, l3, l4⟩ := lift H _ hHc hHl
  have hth : lam = True.rec (motive := fun _ => ℝ) lam rr :=
    True.rec (motive := fun x => lam = True.rec (motive := fun _ => ℝ) lam x) rfl rr
  refine hth.le.trans ?_
  apply Checked.Math.GelfandPDE.gelfand_pde_radial_bound lam (fun x => P H ‖x‖) l1 l2 l3
    ⟨P H, fun x _ => rfl⟩
  intro x hx
  have hn : ‖x‖ ∈ Icc (0:ℝ) 1 := ⟨norm_nonneg _, (mem_ball_zero_iff.1 hx).le⟩
  rw [l4 x hx]
  show -H ‖x‖ + lam * Real.exp (P H ‖x‖) = 0
  rw [← heq _ hn, hHdef]
  simp only [gsf_c_eq hn]
  ring

end Bench

open Claims in
run_cmd do
  let env ← getEnv
  let isProg := fun (c : Name) => isCheckedConst env c || (`Bench).isPrefixOf c
  let isRd := fun (c : Name) => (`Bench.SecondReading).isPrefixOf c
  for (head, t) in [(`Checked.Math.GelfandPDEBound.gelfand_pde_bound, `Checked)] do
    let faults ← liftTermElabM <| closureFaults env isProg isRd head t
    if faults.isEmpty then logInfo m!"BENCH {t}: ACCEPTED"
    else logInfo m!"BENCH {t}: REJECTED ({faults.size}): {faults.toList}"

#print axioms Checked
