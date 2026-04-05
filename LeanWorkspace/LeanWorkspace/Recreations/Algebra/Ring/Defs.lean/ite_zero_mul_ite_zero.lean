import Mathlib

variable {α : Type u} {R : Type v}

variable [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α)

theorem ite_zero_mul_ite_zero : ite P a 0 * ite Q b 0 = ite (P ∧ Q) (a * b) 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]

