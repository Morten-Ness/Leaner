import Mathlib

open scoped RightActions

variable {M N α β : Type*}

variable [Monoid α] [MulAction αᵐᵒᵖ β]

theorem op_smul_op_smul (b : β) (a₁ a₂ : α) : b <• a₁ <• a₂ = b <• (a₁ * a₂) := smul_smul _ _ _

