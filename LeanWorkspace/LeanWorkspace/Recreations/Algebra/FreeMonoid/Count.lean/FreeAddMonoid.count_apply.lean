import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : l.count x = l.toList.count x := rfl

