import Mathlib

variable {α : Type*} {r : α → α → Prop}

theorem one_def : (1 : r →r r) = .id r := rfl

