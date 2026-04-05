import Mathlib

variable {R M : Type*} [Ring R] [CommMonoid M]

theorem mulShift_mul (ψ : AddChar R M) (r s : R) :
    AddChar.mulShift ψ r * AddChar.mulShift ψ s = AddChar.mulShift ψ (r + s) := by
  ext
  rw [mulShift_apply, right_distrib, AddChar.map_add_eq_mul]; norm_cast

