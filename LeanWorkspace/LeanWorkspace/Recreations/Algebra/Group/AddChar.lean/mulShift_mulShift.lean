import Mathlib

variable {R M : Type*} [Ring R] [CommMonoid M]

theorem mulShift_mulShift (ψ : AddChar R M) (r s : R) :
    AddChar.mulShift (AddChar.mulShift ψ r) s = AddChar.mulShift ψ (r * s) := by
  ext
  simp only [mulShift_apply, mul_assoc]

