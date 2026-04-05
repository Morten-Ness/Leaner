import Mathlib

variable {α β : Type*}

theorem unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) := not_congr <| MulOpposite.unop_eq_zero_iff a

