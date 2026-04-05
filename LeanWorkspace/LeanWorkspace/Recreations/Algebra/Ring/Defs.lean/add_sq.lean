import Mathlib

variable {α : Type u} {R : Type v}

variable [CommSemiring α]

theorem add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [sq, add_mul_self_eq]

