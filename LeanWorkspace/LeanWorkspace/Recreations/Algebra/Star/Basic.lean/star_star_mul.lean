import Mathlib

open scoped Ring

variable {R : Type u}

variable [Mul R] [StarMul R]

theorem star_star_mul (x y : R) : star (star x * y) = star y * x := by rw [star_mul, star_star]

