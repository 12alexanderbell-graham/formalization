import Checked.Sim.Duffing
import Checked.Fidelity.DuffingSpec

/-!
# Pin of `IsDuffingSolution` by the blind spec `DuffingSpec`

The spec (`Checked/Fidelity/DuffingSpec.lean`, copied verbatim from the blind
`Work/Fidelity/DuffingSpec.lean`, run 2026-11-04T0628Z) was written from the interface alone; its
determining law is the textbook initial value problem with derivatives within [0, T], and its
anchors (energy conservation, the linear cos/cosh solutions, equilibria, near misses) are proved
from that law. The pin: a function meets the spec exactly when it is an `IsDuffingSolution`.
-/

namespace Checked.Sim.DuffingPin
open Set

/-- A function meets the blind Duffing spec exactly when it solves the Duffing initial value
problem in the program's sense (`IsDuffingSolution`). -/
theorem duffingSpec_pins (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) :
    Checked.Fidelity.DuffingSpec.DuffingSpec k β x₀ v₀ T x ↔
      Checked.Sim.Duffing.IsDuffingSolution k β x₀ v₀ T x := by
  rw [← Checked.Fidelity.DuffingSpec.refIVP_iff_spec]
  constructor
  · rintro ⟨h0, v, hv0, hd⟩
    exact ⟨h0, v, hv0, fun t ht => ⟨(hd t ht).1, by convert (hd t ht).2 using 1; ring⟩⟩
  · rintro ⟨h0, v, hv0, hd⟩
    exact ⟨h0, v, hv0, fun t ht => ⟨(hd t ht).1, by convert (hd t ht).2 using 1; ring⟩⟩

end Checked.Sim.DuffingPin
