import Mathlib

variable {α : Type*}

theorem op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b := rfl

