import Mathlib

open scoped Ring

variable {R : Type u}

variable [Mul R] [StarMul R]

theorem star_mul_star (x y : R) : star (x * star y) = y * star x := by rw [star_mul, star_star]

