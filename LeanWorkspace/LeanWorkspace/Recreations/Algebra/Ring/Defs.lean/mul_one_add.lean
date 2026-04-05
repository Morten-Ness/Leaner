import Mathlib

variable {α : Type u} {R : Type v}

variable [Add α] [MulOneClass α]

theorem mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b := by
  rw [mul_add, mul_one]

