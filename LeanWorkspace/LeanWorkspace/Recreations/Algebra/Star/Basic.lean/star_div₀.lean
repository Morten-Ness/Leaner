import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_div₀ [CommGroupWithZero R] [StarMul R] (x y : R) : star (x / y) = star x / star y := by
  apply op_injective
  rw [division_def, op_div, mul_comm, star_mul, star_inv₀, op_mul, op_inv]

