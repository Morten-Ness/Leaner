import Mathlib

variable {α β : Type*}

theorem unop_mul [Mul α] (x y : αᵐᵒᵖ) : MulOpposite.unop (x * y) = MulOpposite.unop y * MulOpposite.unop x := rfl

