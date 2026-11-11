import Checked.Trust.NonVacuity
namespace Checked.ToyPart
def Bund (x : Nat) : Prop := x = 1 ∧ (0 < x ∧ x < 5)
theorem toy (x : Nat) (h : Bund x) (h2 : x ≠ 7) : x = 1 := h.1
end Checked.ToyPart
#check (necessity% Checked.ToyPart.toy 1 1)
#check (necessity% Checked.ToyPart.toy 1 3)
#check (dropped% Checked.ToyPart.toy 1 2)
#check (necessity% Checked.ToyPart.toy 1)
example : necessity% Checked.ToyPart.toy 1 1 := ⟨2, by decide, by decide, by decide, by decide⟩
example : dropped% Checked.ToyPart.toy 1 2 := fun x a _ _ => a
