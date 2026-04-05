import Mathlib

variable {α β G M : Type*}

variable [Monoid M] [IsLeftCancelMul M] {a b : M}

theorem mul_eq_left : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

