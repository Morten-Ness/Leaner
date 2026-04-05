import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem untop_one : (1 : WithTop α).untop coe_ne_top = 1 := rfl

