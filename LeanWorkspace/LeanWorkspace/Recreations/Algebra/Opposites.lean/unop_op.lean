import Mathlib

variable {α β : Type*}

theorem unop_op (x : α) : MulOpposite.unop (MulOpposite.op x) = x := rfl

