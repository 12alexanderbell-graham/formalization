/-! BA diagnostics for attempt 5: which part of closureFaults each ingredient defeats. -/
open Set Filter Topology Metric InnerProductSpace Laplacian

namespace Bench
namespace SecondReading
def Rtrue : Prop := True
end SecondReading

-- D1: prefix name `Checked`, stronger lemma, NOT threaded
theorem _root_.Checked : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists := by
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, -, hlo, hhi⟩ := Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩

-- D2: ordinary name, stronger lemma, threaded
theorem d2 : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists := by
  refine ⟨fun r => ?_, fun _ => trivial⟩
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, -, hlo, hhi⟩ := Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  exact ⟨True.rec (motive := fun _ => ℝ → ℝ) f r, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩

-- D3: prefix name, threaded, but through the headline itself (H-typed constant reached)
theorem _root_.Checked.Hiemenz : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists := by
  refine ⟨fun r => ?_, fun _ => trivial⟩
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩ := Checked.Hiemenz.hiemenz_exists
  exact ⟨True.rec (motive := fun _ => ℝ → ℝ) f r, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
end Bench

open Claims in
run_cmd do
  let env ← getEnv
  let isProg := fun (c : Name) => isCheckedConst env c || (`Bench).isPrefixOf c
  let isRd := fun (c : Name) => (`Bench.SecondReading).isPrefixOf c
  for (head, t) in [(`Checked.Hiemenz.hiemenz_exists, `Checked), (`Checked.Hiemenz.hiemenz_exists, `Bench.d2)] do
    let faults ← liftTermElabM <| closureFaults env isProg isRd head t
    if faults.isEmpty then logInfo m!"BENCH {t}: ACCEPTED"
    else logInfo m!"BENCH {t}: REJECTED ({faults.size}): {faults.toList}"
