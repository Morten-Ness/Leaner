import Mathlib

variable {α : Type u} {R : Type v}

variable [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α)

theorem ite_zero_mul : ite P a 0 * b = ite P (a * b) 0 := by simp

