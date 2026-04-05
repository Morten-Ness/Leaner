import Mathlib

variable {α β : Type*}

theorem op_comp_unop : (MulOpposite.op : α → αᵐᵒᵖ) ∘ MulOpposite.unop = id := rfl

