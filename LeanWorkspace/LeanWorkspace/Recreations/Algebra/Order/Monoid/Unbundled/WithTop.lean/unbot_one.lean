import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem unbot_one : (1 : WithBot α).unbot coe_ne_bot = 1 := rfl

