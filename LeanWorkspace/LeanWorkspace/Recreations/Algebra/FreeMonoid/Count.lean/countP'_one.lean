import Mathlib

variable {α : Type*} (p : α → Prop) [DecidablePred p]

theorem countP'_one : (1 : FreeMonoid α).countP' p = 0 := rfl

