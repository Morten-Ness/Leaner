import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    FreeMonoid.count x l = Multiplicative.ofAdd (l.toList.count x) := rfl

