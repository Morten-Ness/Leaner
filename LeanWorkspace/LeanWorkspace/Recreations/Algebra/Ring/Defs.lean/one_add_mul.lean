import Mathlib

variable {α : Type u} {R : Type v}

variable [Add α] [MulOneClass α]

theorem one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b := by
  rw [add_mul, one_mul]

