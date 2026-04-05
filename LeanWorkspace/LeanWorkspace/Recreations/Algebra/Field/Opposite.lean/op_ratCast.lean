import Mathlib

variable {α : Type*}

theorem op_ratCast [RatCast α] (q : ℚ) : op (q : α) = q := rfl

