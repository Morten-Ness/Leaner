import Mathlib

variable {α : Type u} {R : Type v}

variable [NonAssocRing α]

theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by rw [mul_sub, mul_one]

