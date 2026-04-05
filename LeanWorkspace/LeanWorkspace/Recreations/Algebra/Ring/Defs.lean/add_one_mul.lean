import Mathlib

variable {α : Type u} {R : Type v}

variable [Add α] [MulOneClass α]

theorem add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b := by
  rw [add_mul, one_mul]

