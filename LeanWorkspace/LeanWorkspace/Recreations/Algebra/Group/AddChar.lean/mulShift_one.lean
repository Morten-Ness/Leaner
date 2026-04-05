import Mathlib

variable {R M : Type*} [Ring R] [CommMonoid M]

theorem mulShift_one (ψ : AddChar R M) : AddChar.mulShift ψ 1 = ψ := by
  ext; rw [mulShift_apply, one_mul]

