import Mathlib

variable {α β : Type*}

theorem unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 := MulOpposite.unop_injective.eq_iff' rfl

attribute [nolint simpComm] AddOpposite.unop_eq_zero_iff

