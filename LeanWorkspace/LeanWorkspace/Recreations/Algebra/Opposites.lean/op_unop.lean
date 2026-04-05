import Mathlib

variable {α β : Type*}

theorem op_unop (x : αᵐᵒᵖ) : MulOpposite.op (MulOpposite.unop x) = x := rfl

