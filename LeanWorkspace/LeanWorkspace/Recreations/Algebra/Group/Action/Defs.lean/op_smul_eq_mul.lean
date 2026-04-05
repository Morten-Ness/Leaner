import Mathlib

variable {M N G H α β γ δ : Type*}

theorem op_smul_eq_mul {α : Type*} [Mul α] (a b : α) : MulOpposite.op a • b = b * a := rfl

