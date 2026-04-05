import Mathlib

variable {M N G H α β γ δ : Type*}

theorem MulOpposite.smul_eq_mul_unop [Mul α] (a : αᵐᵒᵖ) (b : α) : a • b = b * a.unop := rfl

