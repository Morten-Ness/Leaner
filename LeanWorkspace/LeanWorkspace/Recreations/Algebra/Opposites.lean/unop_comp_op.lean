import Mathlib

variable {α β : Type*}

theorem unop_comp_op : (MulOpposite.unop : αᵐᵒᵖ → α) ∘ MulOpposite.op = id := rfl

