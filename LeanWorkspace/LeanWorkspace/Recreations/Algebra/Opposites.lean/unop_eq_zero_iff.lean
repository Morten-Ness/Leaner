import Mathlib

variable {α β : Type*}

theorem unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) := MulOpposite.unop_injective.eq_iff' rfl

