import Mathlib

variable {α : Type*} {r : α → α → Prop}

theorem one_apply (a : α) : (1 : r →r r) a = a := rfl

