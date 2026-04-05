import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem le_mul_left {a b : Associates M} : a ≤ b * a := by rw [mul_comm]; exact Associates.le_mul_right

