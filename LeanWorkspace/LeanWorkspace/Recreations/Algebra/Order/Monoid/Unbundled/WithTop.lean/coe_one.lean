import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem coe_one : ((1 : α) : WithTop α) = 1 := rfl

