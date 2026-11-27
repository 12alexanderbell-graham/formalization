import Closure.TargetRFrozen
import Statements

/-! In the replay project: the program's copy `Frozen.*` is the edition's own `Statements` module,
definitionally (so every closure theorem about `Frozen.*` is about the edition's headlines). -/

theorem TargetR.frozen_is_statements_1 : Frozen.RiemannZetaZerosOnLine = RiemannZetaZerosOnLine := rfl
theorem TargetR.frozen_is_statements_2 : Frozen.DirichletLNonvanishingRightOfHalf = DirichletLNonvanishingRightOfHalf := rfl
theorem TargetR.frozen_is_statements_3 : Frozen.DirichletLZerosOnLine = DirichletLZerosOnLine := rfl
theorem TargetR.frozen_is_statements_4 : Frozen.PrimitiveDirichletLZerosOnLine = PrimitiveDirichletLZerosOnLine := rfl
#print axioms TargetR.frozen_is_statements_1
#print axioms TargetR.frozen_is_statements_2
#print axioms TargetR.frozen_is_statements_3
#print axioms TargetR.frozen_is_statements_4
