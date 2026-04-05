import Mathlib

open scoped RightActions

variable {M N α β : Type*}

variable [Monoid α] [MulAction αᵐᵒᵖ β]

theorem op_smul_mul (b : β) (a₁ a₂ : α) : b <• (a₁ * a₂) = b <• a₁ <• a₂ := mul_smul _ _ _

