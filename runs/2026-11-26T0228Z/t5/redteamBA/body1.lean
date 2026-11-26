/-! BA attempts 1-3: baseline, prefix-named closure, prefix + non-Prop wrapper. -/
open Set Filter Topology Metric InnerProductSpace Laplacian

namespace Bench
namespace SecondReading
def Rtrue : Prop := True
end SecondReading

-- A1: baseline, direct use of the headline, ordinary name
theorem a1 : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists :=
  ⟨fun _ => Checked.Hiemenz.hiemenz_exists, fun _ => trivial⟩

-- A2: closure theorem named `Checked` (prefix of every program name), direct use
theorem _root_.Checked : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists :=
  ⟨fun _ => Checked.Hiemenz.hiemenz_exists, fun _ => trivial⟩

-- A3: prefix name + non-Prop wrapper holding the proof, unwrapped under the binder r
def D3 (_ : True) : PLift (type_of% Checked.Hiemenz.hiemenz_exists) := ⟨Checked.Hiemenz.hiemenz_exists⟩
theorem _root_.Checked.Hiemenz : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists :=
  ⟨fun r => (D3 r).down, fun _ => trivial⟩
end Bench

open Claims in
run_cmd do
  let env ← getEnv
  let isProg := fun (c : Name) => isCheckedConst env c || (`Bench).isPrefixOf c
  let isRd := fun (c : Name) => (`Bench.SecondReading).isPrefixOf c
  for (head, t) in [(`Checked.Hiemenz.hiemenz_exists, `Bench.a1), (`Checked.Hiemenz.hiemenz_exists, `Checked), (`Checked.Hiemenz.hiemenz_exists, `Checked.Hiemenz)] do
    let faults ← liftTermElabM <| closureFaults env isProg isRd head t
    if faults.isEmpty then logInfo m!"BENCH {t}: ACCEPTED"
    else logInfo m!"BENCH {t}: REJECTED ({faults.size}): {faults.toList}"
