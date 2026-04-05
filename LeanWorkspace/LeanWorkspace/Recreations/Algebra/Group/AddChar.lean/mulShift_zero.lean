import Mathlib

variable {R M : Type*} [Ring R] [CommMonoid M]

theorem mulShift_zero (ψ : AddChar R M) : AddChar.mulShift ψ 0 = 1 := by
  ext; rw [mulShift_apply, zero_mul, map_zero_eq_one, one_apply]

