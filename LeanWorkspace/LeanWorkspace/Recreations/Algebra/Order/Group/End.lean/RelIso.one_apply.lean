import Mathlib

variable {α : Type*} {r : α → α → Prop}

theorem one_apply (x : α) : (1 : r ≃r r) x = x := rfl

