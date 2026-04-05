import Mathlib

variable {α : Type u} {R : Type v}

variable [NonAssocRing α]

theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by rw [sub_mul, one_mul]

