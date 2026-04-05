import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem unbotD_one (d : α) : (1 : WithBot α).unbotD d = 1 := rfl

