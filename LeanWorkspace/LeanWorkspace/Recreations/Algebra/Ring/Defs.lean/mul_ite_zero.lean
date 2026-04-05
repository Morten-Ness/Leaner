import Mathlib

variable {α : Type u} {R : Type v}

variable [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α)

theorem mul_ite_zero : a * ite P b 0 = ite P (a * b) 0 := by simp

