import Mathlib

variable {α : Type*}

theorem op_nnratCast [NNRatCast α] (q : ℚ≥0) : op (q : α) = q := rfl

