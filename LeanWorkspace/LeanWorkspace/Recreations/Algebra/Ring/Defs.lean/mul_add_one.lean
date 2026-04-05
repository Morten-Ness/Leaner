import Mathlib

variable {α : Type u} {R : Type v}

variable [Add α] [MulOneClass α]

theorem mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a := by
  rw [mul_add, mul_one]

