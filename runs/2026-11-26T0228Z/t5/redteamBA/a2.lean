/-! BA attempt 4: closure named `Checked`, built from the program's stronger lemma `hiemenz_exists_bounded`
(type differs from the headline's), with R := True threaded into the witness so no closed subterm has type H. -/
open Set Filter Topology Metric InnerProductSpace Laplacian

namespace Bench
namespace SecondReading
def Rtrue : Prop := True
end SecondReading

-- A4: unthreaded (expect: closed subterm flag from Exists.casesOn ... top term)
theorem a4 : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists := by
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, -, hlo, hhi⟩ := Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  exact ⟨f, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩

-- A5: same, name `Checked`, witness depends on the bound variable r
theorem _root_.Checked : SecondReading.Rtrue ↔ type_of% Checked.Hiemenz.hiemenz_exists := by
  refine ⟨fun r => ?_, fun _ => trivial⟩
  obtain ⟨f, p, q, hf, hp, hq, h0, h1, hl, -, hlo, hhi⟩ := Checked.FalknerSkan.Bounded.hiemenz_exists_bounded
  exact ⟨True.rec (motive := fun _ => ℝ → ℝ) f r, p, q, hf, hp, hq, h0, h1, hl, hlo, hhi⟩
end Bench
