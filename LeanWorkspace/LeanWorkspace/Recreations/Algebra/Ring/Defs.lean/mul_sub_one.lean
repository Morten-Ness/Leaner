import Mathlib

variable {α : Type u} {R : Type v}

variable [NonAssocRing α]

theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_sub, mul_one]

