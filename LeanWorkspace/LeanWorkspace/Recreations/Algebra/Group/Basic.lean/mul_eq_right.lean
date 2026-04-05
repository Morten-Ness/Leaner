import Mathlib

variable {α β G M : Type*}

variable [Monoid M] [IsRightCancelMul M] {a b : M}

theorem mul_eq_right : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff

