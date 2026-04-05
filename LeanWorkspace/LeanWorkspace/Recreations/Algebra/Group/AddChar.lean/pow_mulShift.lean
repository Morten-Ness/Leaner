import Mathlib

variable {R M : Type*} [Ring R] [CommMonoid M]

theorem pow_mulShift (ψ : AddChar R M) (n : ℕ) : ψ ^ n = AddChar.mulShift ψ n := by
  ext x
  rw [pow_apply, ← AddChar.mulShift_spec']

