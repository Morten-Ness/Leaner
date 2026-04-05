import Mathlib

variable {R M : Type*} [Ring R] [CommMonoid M]

theorem inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = AddChar.mulShift ψ (-1) := by
  ext
  rw [inv_apply, mulShift_apply, neg_mul, one_mul]

