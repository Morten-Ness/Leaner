import Mathlib

variable (α : Type*) [Mul α]

theorem toEquiv_toLexMulEquiv : (toLexMulEquiv α : α ≃ Lex α) = toLex := rfl

