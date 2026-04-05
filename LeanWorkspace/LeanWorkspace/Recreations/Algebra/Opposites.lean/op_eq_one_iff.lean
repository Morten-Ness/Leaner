import Mathlib

variable {α β : Type*}

theorem op_eq_one_iff [One α] (a : α) : MulOpposite.op a = 1 ↔ a = 1 := MulOpposite.op_injective.eq_iff

