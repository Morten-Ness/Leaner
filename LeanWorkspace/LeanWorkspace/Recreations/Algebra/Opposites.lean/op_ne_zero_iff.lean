import Mathlib

variable {α β : Type*}

theorem op_ne_zero_iff [Zero α] (a : α) : MulOpposite.op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) := not_congr <| MulOpposite.op_eq_zero_iff a

