import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem countP_apply (l : FreeAddMonoid α) : l.countP p = l.toList.countP p := rfl

