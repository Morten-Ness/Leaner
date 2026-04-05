import Mathlib

variable {R : Type*}

variable [Semiring R] {a b : R}

theorem of_mul_add (mul : a * b = 0) (add : a + b = 1) : IsIdempotentElem a ∧ IsIdempotentElem b := by
  simp_rw [IsIdempotentElem]; constructor
  · conv_rhs => rw [← mul_one a, ← add, mul_add, mul, add_zero]
  · conv_rhs => rw [← one_mul b, ← add, add_mul, mul, zero_add]

