import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem countP_apply (l : FreeMonoid α) : l.countP p = .ofAdd (l.toList.countP p) := rfl

