import Mathlib

variable {α : Type u} {R : Type v}

variable [NonAssocRing α]

theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [sub_mul, one_mul]

