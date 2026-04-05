import Mathlib

variable {α β : Type*}

theorem op_eq_zero_iff [Zero α] (a : α) : MulOpposite.op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) := MulOpposite.op_injective.eq_iff' rfl

